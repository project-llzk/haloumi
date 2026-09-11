use std::path::{Path, PathBuf};

use haloumi_inject::{Injector, crate_info::Crate, spec::SpecRegistry};
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
