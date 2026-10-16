//! e2e testing framework for creating tests of the main CLI.

use std::{
    path::{Path, PathBuf},
    process::Command,
};

use crate::{llzk::LlzkArtifact, pcl::PclArtifact};

pub mod llzk;
pub mod pcl;

/// Marks a function as an end-to-end CLI test.
///
/// The function accepts either a result parameter or a [`Test`] followed by a result parameter.
/// The result parameter can be [`ToolResult`], [`ToolOutput`], or [`ToolError`].
pub use e2e_testing_macros::test;

#[macro_export]
#[doc(hidden)]
macro_rules! __test_impl {
    ($target:expr, $args:expr, |$result:ident: $result_ty:ty| $check:block) => {
        $crate::__test_impl!(
            $target,
            $args,
            |__test: $crate::Test, $result: $result_ty| $check
        );
    };
    ($target:expr, $args:expr, |$test:ident : $test_ty:ty, $result:ident: $result_ty:ty| $check:block) => {{
        $crate::setup();
        let mut $test: $test_ty = $crate::Test::new(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join($target),
            env!("CARGO_BIN_EXE_cargo-haloumi"),
            $args,
        );
        let mut $result: $result_ty = $test.run().into();
        $check
    }};
}

/// Performs the initial setup of the test.
pub fn setup() {
    let _ = simplelog::TestLogger::init(log::LevelFilter::Debug, simplelog::Config::default());
}

/// Defines a test.
pub struct Test {
    /// Directory of the extracted crate.
    target: PathBuf,
    command: Command,
}

impl Test {
    /// Creates a new test.
    pub fn new<'s>(
        target: impl AsRef<Path>,
        program: &str,
        args: impl IntoIterator<Item = &'s str>,
    ) -> Self {
        let mut command = Command::new(program);
        command.args(args).current_dir(target.as_ref());
        Self {
            target: target.as_ref().to_path_buf(),
            command,
        }
    }

    /// Returns a reference to the target's path.
    pub fn target(&self) -> &Path {
        &self.target
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

/// Common results produced by the CLI invocation.
#[derive(Debug)]
struct ToolCommon {
    stdout: String,
    stderr: String,
}

/// Output produced by the tool on a succesful run.
#[derive(Debug)]
pub struct ToolOutput {
    common: ToolCommon,
    pcl_artifacts: Vec<PathBuf>,
    llzk_artifacts: Vec<PathBuf>,
}

impl ToolOutput {
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
