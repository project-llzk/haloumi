use std::path::{Path, PathBuf};

use haloumi_inject::spec::{SpecMatch, SpecRegistry};

fn fixture(path: impl AsRef<Path>) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join(path)
}

#[test]
fn ignores_non_toml_files_in_directories() {
    let registry = SpecRegistry::load(fixture("specs/registry/valid")).unwrap();
    assert_eq!(registry.specs().len(), 1);
}

#[test]
fn loads_a_single_spec_file() {
    let version = "1.2.3".parse().unwrap();
    let registry = SpecRegistry::load(fixture("specs/registry/valid/one.toml")).unwrap();
    assert!(matches!(registry.find_matching("foo", &version), SpecMatch::One(_)));
}

#[test]
fn reports_no_matching_spec() {
    let version = "1.2.3".parse().unwrap();
    let registry = SpecRegistry::load(fixture("specs/registry/valid")).unwrap();
    assert!(matches!(registry.find_matching("missing", &version), SpecMatch::None));
}

#[test]
fn reports_one_matching_spec() {
    let version = "1.2.3".parse().unwrap();
    let registry = SpecRegistry::load(fixture("specs/registry/valid")).unwrap();
    assert!(matches!(registry.find_matching("foo", &version), SpecMatch::One(_)));
}

#[test]
fn reports_ambiguous_matching_specs() {
    let version = "1.2.3".parse().unwrap();
    let registry = SpecRegistry::load(fixture("specs/registry/ambiguous")).unwrap();
    assert!(matches!(
        registry.find_matching("foo", &version),
        SpecMatch::Ambiguous(specs) if specs.len() == 2
    ));
}

#[test]
fn rejects_malformed_toml_specs() {
    assert!(SpecRegistry::load(fixture("specs/registry/malformed")).is_err());
}
