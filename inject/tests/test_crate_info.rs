use std::path::{Path, PathBuf};

use haloumi_inject::{
    crate_info::{Crate, RustFile},
    error::Error,
};

fn fixture(path: impl AsRef<Path>) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join(path)
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

    copied
        .create_rust_file("src/bin/generated.rs", RustFile::parse_str("fn main() {}\n").unwrap())
        .unwrap();
    assert!(matches!(
        copied.create_rust_file("src/bin/generated.rs", RustFile::new()),
        Err(Error::GeneratedFileExists(_))
    ));
    assert!(matches!(
        copied.create_rust_file("src/lib.rs", RustFile::default()),
        Err(Error::GeneratedFileExists(_))
    ));
    copied.commit().unwrap();
    assert!(copy.join("src/bin/generated.rs").is_file());
}
