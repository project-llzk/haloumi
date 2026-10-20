//! e2e testing framework for creating tests of the main CLI.

use std::{
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    process::Command,
};
use tempfile::TempDir;

use crate::{llzk::LlzkArtifact, pcl::PclArtifact};

pub mod llzk;
pub mod pcl;

/// Marks a function as an end-to-end CLI test.
///
/// The function accepts either a result parameter or a [`Test`] followed by a result parameter.
/// The result parameter can be [`ToolResult`], [`ToolOutput`], or [`ToolError`].
/// Supplying `before = hook` runs `hook(&mut Test)` before the CLI; parameters after the result
/// receive the hook return value, or the elements of its returned tuple.
pub use e2e_testing_macros::test;

#[macro_export]
#[doc(hidden)]
macro_rules! __test_impl {
    ($target:expr, $args:expr, $copy:expr, |$result:ident: $result_ty:ty| $check:block) => {
        $crate::__test_impl!(
            $target,
            $args,
            $copy,
            |__test: $crate::Test, $result: $result_ty| $check
        );
    };
    ($target:expr, $args:expr, $copy:expr, |$test:ident : $test_ty:ty, $result:ident: $result_ty:ty| $check:block) => {{
        $crate::setup();
        let mut $test: $test_ty = $crate::Test::new(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join($target),
            env!("CARGO_BIN_EXE_cargo-haloumi"),
            $args,
            $copy,
        );
        let mut $result: $result_ty = $test.run().into();
        $check
    }};
    ($target:expr, $args:expr, $copy:expr, $before:ident, |$test:ident : $test_ty:ty, $result:ident: $result_ty:ty| $check:block) => {{
        $crate::setup();
        let mut $test: $test_ty = $crate::Test::new(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join($target),
            env!("CARGO_BIN_EXE_cargo-haloumi"),
            $args,
            $copy,
        );
        let _ = $before(&mut $test);
        let mut $result: $result_ty = $test.run().into();
        $check
    }};
    ($target:expr, $args:expr, $copy:expr, $before:ident, |$test:ident : $test_ty:ty, $result:ident: $result_ty:ty, $value:ident: $value_ty:ty| $check:block) => {{
        $crate::setup();
        let mut $test: $test_ty = $crate::Test::new(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join($target),
            env!("CARGO_BIN_EXE_cargo-haloumi"),
            $args,
            $copy,
        );
        let $value: $value_ty = $before(&mut $test);
        let mut $result: $result_ty = $test.run().into();
        $check
    }};
    ($target:expr, $args:expr, $copy:expr, $before:ident, |$test:ident : $test_ty:ty, $result:ident: $result_ty:ty, $first:ident: $first_ty:ty, $($value:ident: $value_ty:ty),+| $check:block) => {{
        $crate::setup();
        let mut $test: $test_ty = $crate::Test::new(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join($target),
            env!("CARGO_BIN_EXE_cargo-haloumi"),
            $args,
            $copy,
        );
        let ($first, $($value),+): ($first_ty, $($value_ty),+) = $before(&mut $test);
        let mut $result: $result_ty = $test.run().into();
        $check
    }};
}

/// Performs the initial setup of the test.
pub fn setup() {
    let _ = simplelog::TestLogger::init(log::LevelFilter::Debug, simplelog::Config::default());
}

/// Runs Git in `directory`, panicking if it fails.
pub fn git<'a>(directory: impl AsRef<Path>, args: impl IntoIterator<Item = &'a str>) {
    let output = Command::new("git")
        .current_dir(directory)
        .args(args)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
}

/// Defines a test.
pub struct Test {
    /// Directory of the extracted crate.
    target: Target,
    command: Command,
}

enum Target {
    Path(PathBuf),
    Temp(TempDir),
}

impl Target {
    fn path(&self) -> &Path {
        match self {
            Self::Path(path) => path,
            Self::Temp(temp) => temp.path(),
        }
    }
}

impl Test {
    /// Creates a new test.
    pub fn new<'s>(
        target: impl AsRef<Path>,
        program: &str,
        args: impl IntoIterator<Item = &'s str>,
        copy: bool,
    ) -> Self {
        let target = target.as_ref().to_path_buf();
        let target = if copy {
            let temp = tempfile::tempdir().unwrap();
            copy_directory(&target, temp.path());
            Target::Temp(temp)
        } else {
            Target::Path(target)
        };
        let mut command = Command::new(program);
        command.args(args).current_dir(target.path());
        Self { target, command }
    }

    /// Returns a reference to the target's path.
    pub fn target(&self) -> &Path {
        self.target.path()
    }

    /// Reads a UTF-8 file relative to the target crate directory.
    pub fn read_to_string(&self, path: impl AsRef<Path>) -> std::io::Result<String> {
        fs::read_to_string(self.target.path().join(path))
    }

    /// Asserts that a UTF-8 file relative to the target crate directory equals `expected`.
    pub fn file_eq(&self, path: impl AsRef<Path>, expected: &str) {
        let path = path.as_ref();
        let actual = self
            .read_to_string(path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
        assert_eq!(actual, expected, "contents of {}", path.display());
    }

    /// Asserts that a UTF-8 file relative to the target crate directory contains `expected`.
    pub fn file_contains(&self, path: impl AsRef<Path>, expected: &str) {
        let path = path.as_ref();
        let actual = self
            .read_to_string(path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
        assert!(
            actual.contains(expected),
            "contents of {} do not contain {expected:?}:\n{actual}",
            path.display()
        );
    }

    /// Asserts that a path relative to the target crate directory does not exist.
    pub fn path_not_exists(&self, path: impl AsRef<Path>) {
        let path = self.target.path().join(path);
        assert!(!path.exists(), "{} unexpectedly exists", path.display());
    }

    /// Asserts that a regular file relative to the target crate directory exists.
    pub fn file_exists(&self, path: impl AsRef<Path>) {
        let path = self.target.path().join(path);
        assert!(path.is_file(), "{} is not a file", path.display());
    }

    /// Parses a Cargo manifest relative to the target crate directory.
    pub fn manifest(&self, path: impl AsRef<Path>) -> cargo_toml::Manifest {
        let path = self.target.path().join(path);
        cargo_toml::Manifest::from_path(&path)
            .unwrap_or_else(|error| panic!("failed to parse {}: {error}", path.display()))
    }

    /// Writes a Cargo manifest relative to the target crate directory.
    pub fn write_manifest(&self, path: impl AsRef<Path>, manifest: &cargo_toml::Manifest) {
        let path = self.target.path().join(path);
        let contents = toml::to_string(manifest)
            .unwrap_or_else(|error| panic!("failed to serialize {}: {error}", path.display()));
        fs::write(&path, contents)
            .unwrap_or_else(|error| panic!("failed to write {}: {error}", path.display()));
    }

    /// Sets an environment variable for the tool invocation.
    pub fn env(&mut self, key: impl AsRef<OsStr>, value: impl AsRef<OsStr>) -> &mut Self {
        self.command.env(key, value);
        self
    }

    /// Executes the tool.
    pub fn run(&mut self) -> ToolResult {
        let output = self.command.output().unwrap();
        let common = ToolCommon {
            stdout: String::from_utf8_lossy(&output.stdout).as_ref().to_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).as_ref().to_owned(),
        };
        if output.status.success() {
            Ok(ToolOutput {
                common,
                pcl_artifacts: vec![],
                llzk_artifacts: vec![],
            })
        } else {
            Err(ToolError { common })
        }
    }
}

fn copy_directory(source: &Path, destination: &Path) {
    for entry in fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        let target = destination.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            fs::create_dir(&target).unwrap();
            copy_directory(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), target).unwrap();
        }
    }
}

/// Common results produced by the CLI invocation.
#[derive(Debug)]
struct ToolCommon {
    stdout: String,
    stderr: String,
}

impl ToolCommon {
    fn stdout_contains(&self, expected: &str) {
        assert!(
            self.stdout.contains(expected),
            "stdout does not contain {expected:?}:\n{}",
            self.stdout
        );
    }

    fn stderr_contains(&self, expected: &str) {
        assert!(
            self.stderr.contains(expected),
            "stderr does not contain {expected:?}:\n{}",
            self.stderr
        );
    }
}

/// Output produced by the tool on a succesful run.
#[derive(Debug)]
pub struct ToolOutput {
    common: ToolCommon,
    pcl_artifacts: Vec<PathBuf>,
    llzk_artifacts: Vec<PathBuf>,
}

impl ToolOutput {
    /// Asserts that stdout contains `expected`.
    pub fn stdout_contains(&self, expected: &str) {
        self.common.stdout_contains(expected);
    }

    /// Asserts that stderr contains `expected`.
    pub fn stderr_contains(&self, expected: &str) {
        self.common.stderr_contains(expected);
    }

    pub fn stdout(&self) -> &str {
        &self.common.stdout
    }

    pub fn stderr(&self) -> &str {
        &self.common.stderr
    }

    pub fn pcl_artifact(&self, name: impl AsRef<Path>) -> PclArtifact<'_> {
        let path = self
            .pcl_artifacts
            .iter()
            .find(|path| *path == name.as_ref());
        PclArtifact {
            requested: name.as_ref().to_path_buf(),
            path: path.map(|p| &**p),
        }
    }

    pub fn llzk_artifact(&self, name: impl AsRef<Path>) -> LlzkArtifact<'_> {
        let path = self
            .llzk_artifacts
            .iter()
            .find(|path| *path == name.as_ref());
        LlzkArtifact {
            requested: name.as_ref().to_path_buf(),
            path: path.map(|p| &**p),
        }
    }
}

/// Output produced by the tool in case of error.
#[derive(Debug)]
pub struct ToolError {
    common: ToolCommon,
}

impl ToolError {
    /// Asserts that stdout contains `expected`.
    pub fn stdout_contains(&self, expected: &str) {
        self.common.stdout_contains(expected);
    }

    /// Asserts that stderr contains `expected`.
    pub fn stderr_contains(&self, expected: &str) {
        self.common.stderr_contains(expected);
    }

    pub fn stdout(&self) -> &str {
        &self.common.stdout
    }

    pub fn stderr(&self) -> &str {
        &self.common.stderr
    }
}

/// A result produced by the tool.
pub type ToolResult = Result<ToolOutput, ToolError>;

/// Convenience conversion from a result to an output.
///
/// Panics if the result is an error.
impl From<ToolResult> for ToolOutput {
    fn from(result: ToolResult) -> Self {
        match result {
            Ok(output) => output,
            Err(err) => panic!("Expected tool output. Got error: {err:?}"),
        }
    }
}

/// Convenience conversion from a result to an error.
///
/// Panics if the result is a succesful output.
impl From<ToolResult> for ToolError {
    fn from(result: ToolResult) -> Self {
        match result {
            Ok(output) => panic!("Expected tool error. Got output: {output:?}"),
            Err(err) => err,
        }
    }
}
