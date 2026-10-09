use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

fn fixture(path: impl AsRef<Path>) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(path)
}

fn copy_directory(source: &Path, destination: &Path) {
    fs::create_dir_all(destination).unwrap();
    for entry in fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        let destination = destination.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_directory(&entry.path(), &destination);
        } else {
            fs::copy(entry.path(), destination).unwrap();
        }
    }
}

fn setup() -> (tempfile::TempDir, PathBuf, PathBuf, PathBuf) {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("source");
    let cargo = temp.path().join("cargo");
    let log = temp.path().join("cargo.log");
    copy_directory(&fixture("source"), &source);
    fs::copy(fixture("fake-cargo"), &cargo).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&cargo, fs::Permissions::from_mode(0o755)).unwrap();
    }
    (temp, source, cargo, log)
}

fn cli() -> Command {
    Command::new(env!("CARGO_BIN_EXE_inject-tester"))
}

#[test]
fn checks_source_and_patched_default_destination() {
    let (_temp, source, cargo, log) = setup();
    let original = fs::read_to_string(source.join("src/lib.rs")).unwrap();
    let output = cli()
        .env("CARGO", cargo)
        .env("INJECT_TESTER_LOG", &log)
        .args(["--spec", fixture("specs/valid.toml").to_str().unwrap()])
        .arg(&source)
        .args(["--", "--all-targets"])
        .output()
        .unwrap();

    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        fs::read_to_string(source.join("src/lib.rs")).unwrap(),
        original
    );
    let destination = source.join("target/haloumi/.inject-test");
    assert!(
        fs::read_to_string(destination.join("src/lib.rs"))
            .unwrap()
            .contains("INJECTED")
    );
    let log = fs::read_to_string(log).unwrap();
    assert!(
        log.contains(&format!("{} check --all-targets", source.display())),
        "{log}"
    );
    assert!(
        log.contains(&format!("{} check --all-targets", destination.display())),
        "{log}"
    );
}

#[test]
fn build_uses_explicit_destination() {
    let (_temp, source, cargo, log) = setup();
    let destination = source.parent().unwrap().join("patched");
    let output = cli()
        .env("CARGO", cargo)
        .env("INJECT_TESTER_LOG", &log)
        .args([
            "--spec",
            fixture("specs/valid.toml").to_str().unwrap(),
            "--build",
        ])
        .arg(&source)
        .arg(&destination)
        .output()
        .unwrap();

    assert!(output.status.success(), "{output:?}");
    let log = fs::read_to_string(log).unwrap();
    assert!(
        log.contains(&format!("{} build", source.display())),
        "{log}"
    );
    assert!(
        log.contains(&format!("{} build", destination.display())),
        "{log}"
    );
}

#[test]
fn malformed_specs_fail_before_default_destination_creation() {
    let (_temp, source, _cargo, _log) = setup();
    let output = cli()
        .args(["--spec", fixture("specs/malformed.toml").to_str().unwrap()])
        .arg(&source)
        .output()
        .unwrap();

    assert!(!output.status.success());
    assert!(!source.join("target/haloumi/.inject-test").exists());
}

#[test]
fn failed_source_validation_does_not_create_default_destination() {
    let (_temp, source, cargo, log) = setup();
    let output = cli()
        .env("CARGO", cargo)
        .env("INJECT_TESTER_LOG", log)
        .env("INJECT_TESTER_STATUS", "1")
        .args(["--spec", fixture("specs/valid.toml").to_str().unwrap()])
        .arg(&source)
        .output()
        .unwrap();

    assert!(!output.status.success());
    assert!(!source.join("target/haloumi/.inject-test").exists());
}
