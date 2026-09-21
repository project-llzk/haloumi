use std::path::{Path, PathBuf};

use haloumi_inject::{
    Injector,
    crate_info::Crate,
    error::Error,
    spec::{SpecMatch, SpecRegistry},
};
use rstest::{fixture, rstest};
use tempfile::TempDir;

struct DestFixture {
    _temp: TempDir,
    path: PathBuf,
}

impl DestFixture {
    fn new() -> Self {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("dest");
        Self { _temp: temp, path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn cargo_toml_contents_eq(&self, expected: &str) {
        let contents =
            toml::from_str::<cargo_toml::Manifest>(&self.read_file("Cargo.toml")).unwrap();
        let expected = toml::from_str::<cargo_toml::Manifest>(expected).unwrap();
        similar_asserts::assert_eq!(contents, expected);
    }

    fn rust_file_contents_eq(&self, path: impl AsRef<Path>, expected: &str) {
        let contents = syn::parse_file(&self.read_file(path)).unwrap();
        let expected = syn::parse_file(expected).unwrap();
        similar_asserts::assert_eq!(contents, expected);
    }

    fn read_file(&self, path: impl AsRef<Path>) -> String {
        std::fs::read_to_string(self.path().join(path)).unwrap()
    }
}

#[fixture]
fn dest() -> DestFixture {
    DestFixture::new()
}

#[fixture]
fn specs() -> SpecRegistry {
    SpecRegistry::load(Path::new("tests/specs/")).unwrap()
}

#[fixture]
fn setup() {
    let _ = simplelog::TestLogger::init(log::LevelFilter::Debug, simplelog::Config::default());
}

fn do_inject(dest: &DestFixture, specs: SpecRegistry, src_path: impl AsRef<Path>) {
    let crt = Crate::open(&src_path)
        .map_err(|err| panic!("{err}"))
        .unwrap();
    let injector = Injector::new(&crt, &specs)
        .map_err(|err| panic!("{err}"))
        .unwrap();
    injector
        .apply(dest.path())
        .map_err(|err| panic!("{err}"))
        .unwrap();
}

#[rstest]
fn test_inject1(_setup: (), dest: DestFixture, specs: SpecRegistry) {
    do_inject(&dest, specs, "tests/crates/test1");

    dest.cargo_toml_contents_eq(
        r#"
            [package]
            name = "test1"
            version = "0.5.0"

            # This is usually implicit but since we are handling 
            # manifests at a low level we need to include it.
            [lib]
            path = "src/lib.rs"
            name = "test1"
            edition = "2015"
            crate-type = ["lib"]

            [dependencies.haloumi]
            version = "*"
            package = "haloumi-integration"
        "#,
    );
    dest.rust_file_contents_eq(
        "src/lib.rs",
        r#"
            pub mod bar;
            pub mod foo;

            haloumi::__mock_impl!();
        "#,
    );
    dest.rust_file_contents_eq(
        "src/foo.rs",
        r#"
            #[derive(Debug)]
            pub struct Foo {
                a: usize,
            }

            pub struct Bar;
        "#,
    );
    dest.rust_file_contents_eq(
        "src/bar.rs",
        r#"
            #[derive(haloumi::MockTrait)]
            #[foo(123)]
            #[bar = "baz"]
            pub enum Bar {
                X,
                Y,
            }
        "#,
    );
}

#[rstest]
#[should_panic = "Dependency 'foo' is already in the manifest"]
fn test_inject2(_setup: (), dest: DestFixture, specs: SpecRegistry) {
    do_inject(&dest, specs, "tests/crates/test2");
}

fn fixture(path: impl AsRef<Path>) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join(path)
}

#[test]
fn registry_ignores_non_toml_files_and_reports_match_cardinality() {
    let version = "1.2.3".parse().unwrap();
    let registry = SpecRegistry::load(fixture("specs/registry/valid")).unwrap();
    assert!(matches!(registry.find_matching("missing", &version), SpecMatch::None));
    assert!(matches!(registry.find_matching("foo", &version), SpecMatch::One(_)));

    let registry = SpecRegistry::load(fixture("specs/registry/ambiguous")).unwrap();
    assert!(matches!(
        registry.find_matching("foo", &version),
        SpecMatch::Ambiguous(specs) if specs.len() == 2
    ));

    let registry = SpecRegistry::load(fixture("specs/registry/valid/one.toml")).unwrap();
    assert!(matches!(registry.find_matching("foo", &version), SpecMatch::One(_)));
}

#[test]
fn registry_rejects_malformed_toml_specs() {
    assert!(SpecRegistry::load(fixture("specs/registry/malformed")).is_err());
}

#[cfg(unix)]
#[test]
fn clone_skips_root_target_preserves_symlinks_and_rebases_paths() {
    let temp = tempfile::tempdir().unwrap();
    let source = fixture("crates/copy-source");
    let copy = temp.path().join("copy");
    Crate::open(&source).unwrap().clone_in_path(&copy).unwrap();

    assert!(!copy.join("target").exists());
    assert!(copy.join("src/target/kept.rs").is_file());
    assert_eq!(std::fs::read_link(copy.join("linked.rs")).unwrap(), PathBuf::from("src/lib.rs"));
    let manifest = cargo_toml::Manifest::from_path(copy.join("Cargo.toml")).unwrap();
    let expected_path = fixture("crates/copy-sibling").to_string_lossy().into_owned();
    let copied_path = manifest.dependencies["copy-sibling"].detail().unwrap().path.as_deref().unwrap();
    assert!(Path::new(copied_path).is_absolute());
    assert_eq!(Path::new(copied_path).canonicalize().unwrap(), Path::new(&expected_path).canonicalize().unwrap());
}

#[test]
fn copied_workspace_member_has_a_standalone_readable_manifest() {
    let temp = tempfile::tempdir().unwrap();
    let copy = temp.path().join("copy");
    Crate::open(fixture("crates/workspace/member"))
        .unwrap()
        .clone_in_path(&copy)
        .unwrap();

    let raw_manifest: toml::Value = toml::from_str(&std::fs::read_to_string(copy.join("Cargo.toml")).unwrap()).unwrap();
    assert!(raw_manifest.get("workspace").is_none());
    assert!(Crate::open(&copy).is_ok());
    let cargo_metadata = std::process::Command::new("cargo")
        .args(["metadata", "--no-deps", "--format-version", "1", "--manifest-path"])
        .arg(copy.join("Cargo.toml"))
        .output()
        .unwrap();
    assert!(cargo_metadata.status.success());
    let manifest = cargo_toml::Manifest::from_path(copy.join("Cargo.toml")).unwrap();
    let expected_path = fixture("crates/workspace/shared").to_string_lossy().into_owned();
    assert_eq!(manifest.dependencies["shared"].detail().unwrap().path.as_deref(), Some(expected_path.as_str()));
}

#[test]
fn dependency_replacement_preserves_detailed_options() {
    let temp = tempfile::tempdir().unwrap();
    let copy = temp.path().join("copy");
    let local = temp.path().join("patched-upstream");
    let mut copied = Crate::open(fixture("crates/detailed-dependency"))
        .unwrap()
        .clone_in_path(&copy)
        .unwrap();
    copied.replace_dependency_with_path("alias", &local).unwrap();
    copied.commit().unwrap();

    let manifest = cargo_toml::Manifest::from_path(copy.join("Cargo.toml")).unwrap();
    let dependency = manifest.dependencies["alias"].detail().unwrap();
    assert_eq!(dependency.package.as_deref(), Some("upstream"));
    assert_eq!(dependency.features, ["feature-a"]);
    assert!(dependency.optional);
    assert!(!dependency.default_features);
    assert_eq!(dependency.path.as_deref(), Some(local.to_string_lossy().as_ref()));
    assert!(dependency.git.is_none());
}

#[test]
fn generated_file_commits_once_and_rejects_collisions() {
    let temp = tempfile::tempdir().unwrap();
    let copy = temp.path().join("copy");
    let mut copied = Crate::open(fixture("crates/test1"))
        .unwrap()
        .clone_in_path(&copy)
        .unwrap();

    copied.create_rust_file("src/bin/generated.rs", "fn main() {}\n").unwrap();
    assert!(matches!(
        copied.create_rust_file("src/bin/generated.rs", "fn main() {}\n"),
        Err(Error::GeneratedFileExists(_))
    ));
    assert!(matches!(
        copied.create_rust_file("src/lib.rs", "fn replacement() {}\n"),
        Err(Error::GeneratedFileExists(_))
    ));
    copied.commit().unwrap();
    assert!(copy.join("src/bin/generated.rs").is_file());
}
