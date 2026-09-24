use std::{
    env,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use tempfile::TempDir;

fn fixture(path: impl AsRef<Path>) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/crates")
        .join(path)
}

fn copy_fixture(name: &str) -> TempDir {
    let temp = tempfile::tempdir().unwrap();
    copy_directory(&fixture(name), temp.path());
    temp
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

fn cli() -> Command {
    Command::new(env!("CARGO_BIN_EXE_cargo-haloumi"))
}

#[test]
fn direct_help_succeeds() {
    let output = cli().arg("--help").output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("Workspace package to extract"));
    assert!(stdout.contains("Root directory of the Cargo project to extract"));
    assert!(stdout.contains("Build the generated extractor without running it"));
}

#[test]
fn cargo_external_subcommand_help_succeeds() {
    let temp = tempfile::tempdir().unwrap();
    let cargo_home = temp.path().join("cargo-home");
    let bin = cargo_home.join("bin");
    fs::create_dir_all(&bin).unwrap();
    fs::copy(
        env!("CARGO_BIN_EXE_cargo-haloumi"),
        bin.join("cargo-haloumi"),
    )
    .unwrap();

    let cargo = env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo"));
    let output = Command::new(cargo)
        .current_dir(temp.path())
        .env("CARGO_HOME", cargo_home)
        .arg("haloumi")
        .arg("--help")
        .output()
        .unwrap();

    assert!(output.status.success(), "{output:?}");
    assert!(String::from_utf8_lossy(&output.stdout).contains("Workspace package to extract"));
}

#[test]
fn workspace_without_package_lists_members() {
    let temp = copy_fixture("workspace-selection");
    let output = cli().current_dir(temp.path()).output().unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("-p"), "{stderr}");
    assert!(stderr.contains("one") && stderr.contains("two"), "{stderr}");
}

#[test]
fn workspace_rejects_package_that_is_not_a_member() {
    let temp = copy_fixture("workspace-selection");
    let output = cli()
        .current_dir(temp.path())
        .args(["-p", "missing"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("not a workspace member"));
}

#[test]
fn malformed_configuration_fails_before_mutating_the_project() {
    let temp = copy_fixture("malformed-config");
    let manifest = temp.path().join("Cargo.toml");
    let original_manifest = fs::read_to_string(&manifest).unwrap();

    let output = cli().current_dir(temp.path()).output().unwrap();
    assert!(!output.status.success());
    assert_eq!(fs::read_to_string(manifest).unwrap(), original_manifest);
}

#[test]
fn no_configuration_creates_an_isolated_extraction_copy_without_backend_outputs() {
    let temp = copy_fixture("extraction-root");
    let manifest = temp.path().join("Cargo.toml");
    let source = temp.path().join("src/lib.rs");
    let original_manifest = fs::read_to_string(&manifest).unwrap();
    let original_source = fs::read_to_string(&source).unwrap();

    let output = cli().current_dir(temp.path()).output().unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(fs::read_to_string(manifest).unwrap(), original_manifest);
    assert_eq!(fs::read_to_string(source).unwrap(), original_source);

    let extracted_root = temp
        .path()
        .join("target/haloumi/.crates/extraction-root-0.1.0");
    let generated = extracted_root.join("src/bin/haloumi-extractor.rs");
    assert!(generated.is_file());
    assert!(
        fs::read_to_string(generated)
            .unwrap()
            .contains("extraction_root::harnesses()")
    );
    assert!(!temp.path().join("target/haloumi/ir").exists());
    assert!(!temp.path().join("target/haloumi/picus").exists());
    assert!(!temp.path().join("target/haloumi/llzk").exists());
}

#[test]
fn root_runs_extraction_from_a_separate_directory() {
    let caller = tempfile::tempdir().unwrap();
    let root = caller.path().join("project");
    fs::create_dir(&root).unwrap();
    copy_directory(&fixture("extraction-root"), &root);

    let output = cli()
        .current_dir(caller.path())
        .args(["--root", "project"])
        .output()
        .unwrap();

    assert!(output.status.success(), "{output:?}");
    assert!(
        root.join("target/haloumi/.crates/extraction-root-0.1.0/src/bin/haloumi-extractor.rs")
            .is_file()
    );
    assert!(!caller.path().join("target/haloumi").exists());
}

#[test]
fn matching_spec_patches_an_aliased_direct_dependency_copy() {
    let temp = copy_fixture("aliased-patch-root");
    let original_dependency = temp.path().join("dependency/src/lib.rs");
    let original_manifest = temp.path().join("Cargo.toml");
    let original_dependency_contents = fs::read_to_string(&original_dependency).unwrap();
    let original_manifest_contents = fs::read_to_string(&original_manifest).unwrap();

    let output = cli().current_dir(temp.path()).output().unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        fs::read_to_string(original_dependency).unwrap(),
        original_dependency_contents
    );
    assert_eq!(
        fs::read_to_string(original_manifest).unwrap(),
        original_manifest_contents
    );

    let copied_root = temp
        .path()
        .join("target/haloumi/.crates/aliased-patch-root-0.1.0");
    let copied_dependency = temp
        .path()
        .join("target/haloumi/.crates/target-dependency-0.1.0");
    assert!(
        fs::read_to_string(copied_dependency.join("src/lib.rs"))
            .unwrap()
            .contains("pub const PATCHED: bool = true;")
    );

    let copied_manifest = fs::read_to_string(copied_root.join("Cargo.toml")).unwrap();
    assert!(copied_manifest.contains("patched"));
    assert!(copied_manifest.contains("package = \"target-dependency\""));
    assert!(copied_manifest.contains(&copied_dependency.display().to_string()));

    let copied_dependency_manifest =
        fs::read_to_string(copied_dependency.join("Cargo.toml")).unwrap();
    let manifest: toml::Value = toml::from_str(&copied_dependency_manifest).unwrap();
    let helper_path = manifest["dependencies"]["helper"]["path"].as_str().unwrap();
    assert!(Path::new(helper_path).is_absolute());
    assert_eq!(
        Path::new(helper_path).canonicalize().unwrap(),
        temp.path().join("helper").canonicalize().unwrap(),
    );
}

#[test]
fn matching_spec_patches_a_hyphenated_direct_dependency_copy() {
    let temp = copy_fixture("hyphenated-patch-root");

    let output = cli().current_dir(temp.path()).output().unwrap();
    assert!(output.status.success(), "{output:?}");

    let copied_root = temp
        .path()
        .join("target/haloumi/.crates/hyphenated-patch-root-0.1.0");
    let copied_dependency = temp
        .path()
        .join("target/haloumi/.crates/target-dependency-0.1.0");
    assert!(
        fs::read_to_string(copied_dependency.join("src/lib.rs"))
            .unwrap()
            .contains("pub const PATCHED: bool = true;")
    );

    let copied_manifest = fs::read_to_string(copied_root.join("Cargo.toml")).unwrap();
    let manifest: toml::Value = toml::from_str(&copied_manifest).unwrap();
    let dependency = &manifest["dependencies"]["target-dependency"];
    assert_eq!(
        Path::new(dependency["path"].as_str().unwrap())
            .canonicalize()
            .unwrap(),
        copied_dependency.canonicalize().unwrap()
    );
}

#[test]
fn ambiguous_specs_fail_before_cargo_execution() {
    let temp = copy_fixture("ambiguous-specs-root");
    let output = cli().current_dir(temp.path()).output().unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("2 specs match target-dependency 0.1.0")
    );
}

#[test]
fn generated_extractor_binary_collision_is_reported() {
    let temp = copy_fixture("generated-binary-collision");
    let original = fs::read_to_string(temp.path().join("src/bin/haloumi-extractor.rs")).unwrap();
    let output = cli().current_dir(temp.path()).output().unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("Refusing to overwrite existing generated file")
    );
    assert_eq!(
        fs::read_to_string(temp.path().join("src/bin/haloumi-extractor.rs")).unwrap(),
        original
    );
}

#[test]
fn higher_priority_backend_table_blocks_lower_priority_backend_parameters() {
    let temp = copy_fixture("config-chain-root");
    let args_output = temp.path().join("extractor-args");

    let output = cli()
        .current_dir(temp.path())
        .env("HALOUMI_TEST_ARGS_OUTPUT", &args_output)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");

    let args = fs::read_to_string(args_output).unwrap();
    assert!(args.contains("--format\nir"), "{args}");
    assert!(!args.contains("--llzk-field-name"), "{args}");
    assert!(args.contains("--output"), "{args}");

    let copied_root = temp
        .path()
        .join("target/haloumi/.crates/config-chain-root-0.1.0");
    let manifest = fs::read_to_string(copied_root.join("Cargo.toml")).unwrap();
    assert!(manifest.contains("custom-extractor"));
    assert!(manifest.contains("support"));
    assert!(
        fs::read_to_string(copied_root.join("src/bin/haloumi-extractor.rs"))
            .unwrap()
            .contains("custom_extractor::ExtractorMain::run")
    );
}

#[test]
fn dry_run_builds_the_generated_extractor_without_running_it() {
    let temp = copy_fixture("config-chain-root");
    let args_output = temp.path().join("extractor-args");

    let output = cli()
        .current_dir(temp.path())
        .arg("--dry-run")
        .env("HALOUMI_TEST_ARGS_OUTPUT", &args_output)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(
        temp.path()
            .join("target/haloumi/.cargo/debug/haloumi-extractor")
            .is_file()
    );
    assert!(!args_output.exists());
}

#[test]
fn target_config_forwards_all_features_with_explicit_features() {
    let temp = copy_fixture("config-chain-root");
    let config = temp.path().join(".haloumi.toml");
    let args_output = temp.path().join("extractor-args");
    let contents = fs::read_to_string(&config).unwrap();
    fs::write(
        &config,
        contents.replace(
            "features = [\"configured-feature\"]\nno-default-features = true",
            "features = [\"configured-feature\"]\nall-features = true",
        ),
    )
    .unwrap();

    let output = cli()
        .current_dir(temp.path())
        .env("HALOUMI_TEST_ARGS_OUTPUT", &args_output)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(args_output.is_file());
}
