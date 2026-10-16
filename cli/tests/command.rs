use std::{
    env,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

fn fixture(path: impl AsRef<Path>) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/crates")
        .join(path)
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

#[e2e::test(target = ".", args = ["--help"])]
fn direct_help_succeeds(output: e2e::ToolOutput) {
    assert!(output.stdout().contains("Workspace package to extract"));
    assert!(
        output
            .stdout()
            .contains("Root directory of the Cargo project to extract")
    );
    assert!(
        output
            .stdout()
            .contains("Build the generated extractor without running it")
    );
}

// Cannot use `#[e2e::test]`: this test installs the binary into a temporary `CARGO_HOME`.
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

#[e2e::test(target = "tests/crates/workspace-selection")]
fn workspace_without_package_lists_members(output: e2e::ToolError) {
    let stderr = output.stderr();
    assert!(stderr.contains("-p"), "{stderr}");
    assert!(stderr.contains("one") && stderr.contains("two"), "{stderr}");
}

#[e2e::test(
    target = "tests/crates/workspace-selection",
    args = ["-p", "missing"]
)]
fn workspace_rejects_package_that_is_not_a_member(output: e2e::ToolError) {
    assert!(output.stderr().contains("not a workspace member"));
}

#[e2e::test(
    target = "tests/crates/workspace-member-extraction",
    args = ["-p", "workspace-member", "--dry-run"]
)]
fn workspace_member_extraction_builds_the_isolated_copy(test: e2e::Test, _: e2e::ToolOutput) {
    let manifest = test
        .read_to_string("target/haloumi/.crates/workspace-member-0.1.0/Cargo.toml")
        .unwrap();
    let manifest: toml::Value = toml::from_str(&manifest).unwrap();
    assert!(manifest.get("workspace").is_some());
}

fn malformed_configuration_before(test: &mut e2e::Test) -> String {
    test.read_to_string("Cargo.toml").unwrap()
}

#[e2e::test(
    target = "tests/crates/malformed-config",
    before = malformed_configuration_before
)]
fn malformed_configuration_fails_before_mutating_the_project(
    test: e2e::Test,
    _: e2e::ToolError,
    original_manifest: String,
) {
    assert_eq!(
        test.read_to_string("Cargo.toml").unwrap(),
        original_manifest
    );
}

fn no_configuration_before(test: &mut e2e::Test) -> (String, String) {
    (
        test.read_to_string("Cargo.toml").unwrap(),
        test.read_to_string("src/lib.rs").unwrap(),
    )
}

#[e2e::test(
    target = "tests/crates/extraction-root",
    before = no_configuration_before
)]
fn no_configuration_creates_an_isolated_extraction_copy_without_backend_outputs(
    test: e2e::Test,
    _: e2e::ToolOutput,
    original_manifest: String,
    original_source: String,
) {
    assert_eq!(
        test.read_to_string("Cargo.toml").unwrap(),
        original_manifest
    );
    assert_eq!(test.read_to_string("src/lib.rs").unwrap(), original_source);

    let extracted_root = test
        .target()
        .join("target/haloumi/.crates/extraction-root-0.1.0");
    let generated = extracted_root.join("src/bin/haloumi-extractor.rs");
    assert!(generated.is_file());
    assert!(
        fs::read_to_string(generated)
            .unwrap()
            .contains("extraction_root::harnesses()")
    );
    assert!(!test.target().join("target/haloumi/ir").exists());
    assert!(!test.target().join("target/haloumi/picus").exists());
    assert!(!test.target().join("target/haloumi/llzk").exists());
}

#[e2e::test(target = "tests/crates/missing-configured-specs-path")]
fn missing_configured_specs_path_fails_before_creating_workspace(
    test: e2e::Test,
    output: e2e::ToolError,
) {
    let stderr = output.stderr();
    assert!(
        stderr.contains("Unsupported filesystem object at"),
        "{stderr}"
    );
    assert!(stderr.contains("missing-specs"), "{stderr}");
    assert!(!test.target().join("target/haloumi").exists());
}

#[e2e::test(
    target = "tests/crates/autobins-disabled-root",
    args = ["--dry-run"]
)]
fn disabled_autobins_still_builds_the_generated_extractor(test: e2e::Test, _: e2e::ToolOutput) {
    let manifest = test
        .read_to_string("target/haloumi/.crates/autobins-disabled-root-0.1.0/Cargo.toml")
        .unwrap();
    let manifest: toml::Value = toml::from_str(&manifest).unwrap();
    let bins = manifest["bin"].as_array().unwrap();
    assert_eq!(bins.len(), 1);
    assert_eq!(bins[0]["name"].as_str(), Some("haloumi-extractor"));
    assert_eq!(
        bins[0]["path"].as_str(),
        Some("src/bin/haloumi-extractor.rs")
    );
}

#[e2e::test(target = "tests/crates/stale-artifacts-root", args = ["--output", "outputs"])]
fn execution_removes_all_stale_haloumi_artifacts(test: e2e::Test, _: e2e::ToolOutput) {
    let artifacts = test.target().join("outputs");
    assert!(!artifacts.join(".crates/stale-crate/marker").exists());
    assert!(!artifacts.join(".cargo/stale-build").exists());
    assert!(!artifacts.join("ir/stale-result").exists());
    assert!(
        artifacts
            .join(".crates/stale-artifacts-root-0.1.0/src/bin/haloumi-extractor.rs")
            .is_file()
    );
}

#[e2e::test(target = "tests/crates/explicit-lib-name-root")]
fn explicit_library_target_name_is_used_by_the_generated_extractor(
    test: e2e::Test,
    _: e2e::ToolOutput,
) {
    let generated = test
        .read_to_string(
            "target/haloumi/.crates/explicit-lib-name-root-0.1.0/src/bin/haloumi-extractor.rs",
        )
        .unwrap();
    assert!(generated.contains("extraction_api::harnesses()"));
}

// Cannot use `#[e2e::test]`: this test needs a caller directory distinct from the target root.
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

#[e2e::test(target = "tests/crates/aliased-patch-root")]
fn matching_spec_patches_an_aliased_direct_dependency_copy(test: e2e::Test, _: e2e::ToolOutput) {
    assert_eq!(
        test.read_to_string("dependency/src/lib.rs").unwrap(),
        include_str!("crates/aliased-patch-root/dependency/src/lib.rs")
    );
    assert_eq!(
        test.read_to_string("Cargo.toml").unwrap(),
        include_str!("crates/aliased-patch-root/Cargo.toml")
    );

    let copied_root = "target/haloumi/.crates/aliased-patch-root-0.1.0";
    let copied_dependency = "target/haloumi/.crates/target-dependency-0.1.0";
    assert!(
        test.read_to_string(format!("{copied_dependency}/src/lib.rs"))
            .unwrap()
            .contains("pub const PATCHED: bool = true;")
    );

    let copied_manifest = test
        .read_to_string(format!("{copied_root}/Cargo.toml"))
        .unwrap();
    assert!(copied_manifest.contains("patched"));
    assert!(copied_manifest.contains("package = \"target-dependency\""));
    assert!(copied_manifest.contains(&test.target().join(copied_dependency).display().to_string()));

    let copied_dependency_manifest = test
        .read_to_string(format!("{copied_dependency}/Cargo.toml"))
        .unwrap();
    let manifest: toml::Value = toml::from_str(&copied_dependency_manifest).unwrap();
    let helper_path = manifest["dependencies"]["helper"]["path"].as_str().unwrap();
    assert!(Path::new(helper_path).is_absolute());
    assert_eq!(
        Path::new(helper_path).canonicalize().unwrap(),
        test.target().join("helper").canonicalize().unwrap(),
    );
}

#[e2e::test(target = "tests/crates/configured-file-patch-root")]
fn matching_spec_from_a_configured_file_patches_a_direct_dependency_copy(
    test: e2e::Test,
    _: e2e::ToolOutput,
) {
    assert!(
        test.read_to_string("target/haloumi/.crates/target-dependency-0.1.0/src/lib.rs")
            .unwrap()
            .contains("pub const PATCHED: bool = true;")
    );
}

#[e2e::test(
    target = "tests/crates/multi-version-aliased-patch-root",
    args = ["--dry-run"]
)]
fn matching_spec_patches_all_matching_aliased_direct_dependency_versions(
    test: e2e::Test,
    _: e2e::ToolOutput,
) {
    let copied_root = "target/haloumi/.crates/multi-version-aliased-patch-root-0.1.0";
    let copied_foo_10 = "target/haloumi/.crates/foo-1.0.0";
    let copied_foo_11 = "target/haloumi/.crates/foo-1.1.0";
    assert!(
        test.read_to_string(format!("{copied_foo_10}/src/lib.rs"))
            .unwrap()
            .contains("pub const PATCHED: bool = true;")
    );
    assert!(
        test.read_to_string(format!("{copied_foo_11}/src/lib.rs"))
            .unwrap()
            .contains("pub const PATCHED: bool = true;")
    );
    assert!(
        !test
            .target()
            .join("target/haloumi/.crates/foo-2.0.0")
            .exists()
    );

    let copied_manifest = test
        .read_to_string(format!("{copied_root}/Cargo.toml"))
        .unwrap();
    let manifest: toml::Value = toml::from_str(&copied_manifest).unwrap();
    for (alias, copied_dependency) in [("foo_10", copied_foo_10), ("foo_11", copied_foo_11)] {
        let dependency = &manifest["dependencies"][alias];
        assert_eq!(
            Path::new(dependency["path"].as_str().unwrap())
                .canonicalize()
                .unwrap(),
            test.target()
                .join(copied_dependency)
                .canonicalize()
                .unwrap()
        );
    }
    assert_eq!(
        Path::new(manifest["dependencies"]["foo_20"]["path"].as_str().unwrap())
            .canonicalize()
            .unwrap(),
        test.target().join("foo_20").canonicalize().unwrap()
    );
}

fn distinct_package_id_aliases_before(test: &mut e2e::Test) {
    let git_source = test.target().join("source-two");
    e2e::git(&git_source, ["init", "--quiet"]);
    e2e::git(&git_source, ["add", "."]);
    e2e::git(
        &git_source,
        [
            "-c",
            "user.name=Haloumi Tests",
            "-c",
            "user.email=tests@haloumi.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "--quiet",
            "-m",
            "initial",
        ],
    );

    let manifest_path = test.target().join("Cargo.toml");
    let manifest = fs::read_to_string(&manifest_path).unwrap();
    let git_dependency = format!(
        "source_two = {{ package = \"same-dependency\", git = \"file://{}\" }}",
        git_source.display()
    );
    fs::write(
        &manifest_path,
        manifest.replace(
            "source_two = { package = \"same-dependency\", path = \"source-two\" }",
            &git_dependency,
        ),
    )
    .unwrap();

    test.env("CARGO_HOME", test.target().join("cargo-home"));
}

#[e2e::test(
    target = "tests/crates/distinct-package-id-aliases",
    args = ["--dry-run"],
    before = distinct_package_id_aliases_before
)]
fn matching_spec_rejects_same_name_and_version_dependencies_from_distinct_sources(
    output: e2e::ToolError,
) {
    assert!(
        output.stderr().contains(
            "multiple direct dependencies named same-dependency 0.1.0 resolve to different package IDs; patching them is unsupported"
        ),
        "{output:?}"
    );
}

#[e2e::test(target = "tests/crates/hyphenated-patch-root")]
fn matching_spec_patches_a_hyphenated_direct_dependency_copy(test: e2e::Test, _: e2e::ToolOutput) {
    let copied_root = "target/haloumi/.crates/hyphenated-patch-root-0.1.0";
    let copied_dependency = "target/haloumi/.crates/target-dependency-0.1.0";
    assert!(
        test.read_to_string(format!("{copied_dependency}/src/lib.rs"))
            .unwrap()
            .contains("pub const PATCHED: bool = true;")
    );

    let copied_manifest = test
        .read_to_string(format!("{copied_root}/Cargo.toml"))
        .unwrap();
    let manifest: toml::Value = toml::from_str(&copied_manifest).unwrap();
    let dependency = &manifest["dependencies"]["target-dependency"];
    assert_eq!(
        Path::new(dependency["path"].as_str().unwrap())
            .canonicalize()
            .unwrap(),
        test.target()
            .join(copied_dependency)
            .canonicalize()
            .unwrap()
    );
}

#[e2e::test(target = "tests/crates/ambiguous-specs-root")]
fn ambiguous_specs_fail_before_cargo_execution(output: e2e::ToolError) {
    assert!(
        output
            .stderr()
            .contains("2 specs match target-dependency 0.1.0")
    );
}

#[e2e::test(target = "tests/crates/generated-binary-collision")]
fn generated_extractor_binary_collision_is_reported(test: e2e::Test, output: e2e::ToolError) {
    assert!(
        output
            .stderr()
            .contains("Binary 'haloumi-extractor' is already in the manifest")
    );
    assert_eq!(
        test.read_to_string("src/bin/haloumi-extractor.rs").unwrap(),
        include_str!("crates/generated-binary-collision/src/bin/haloumi-extractor.rs")
    );
}

#[e2e::test(target = "tests/crates/declared-binary-collision")]
fn declared_extractor_binary_target_collision_is_reported(test: e2e::Test, output: e2e::ToolError) {
    assert!(
        output
            .stderr()
            .contains("Binary 'haloumi-extractor' is already in the manifest")
    );
    assert_eq!(
        test.read_to_string("Cargo.toml").unwrap(),
        include_str!("crates/declared-binary-collision/Cargo.toml")
    );
}

#[e2e::test(
    target = "tests/crates/merged-runner-dependency",
    args = ["--dry-run"]
)]
fn compatible_existing_runner_dependency_is_merged(test: e2e::Test, _: e2e::ToolOutput) {
    let copied = test
        .read_to_string("target/haloumi/.crates/merged-runner-dependency-0.1.0/Cargo.toml")
        .unwrap();
    assert!(copied.contains("version = \">=0.1.0\""), "{copied}");
    assert!(
        copied.contains("existing") && copied.contains("requested"),
        "{copied}"
    );
}

#[e2e::test(
    target = "tests/crates/incompatible-runner-version",
    args = ["--dry-run"]
)]
fn incompatible_existing_runner_version_is_reported_before_building(output: e2e::ToolError) {
    assert!(
        output
            .stderr()
            .contains("dependency 'custom-extractor' conflicts with extractor configuration"),
        "{}",
        output.stderr()
    );
}

#[e2e::test(
    target = "tests/crates/unrelated-runner-dependency",
    args = ["--dry-run"]
)]
fn unrelated_existing_runner_dependency_is_reported(output: e2e::ToolError) {
    assert!(
        output
            .stderr()
            .contains("dependency 'custom-extractor' conflicts with extractor configuration"),
        "{}",
        output.stderr()
    );
}

#[e2e::test(
    target = "tests/crates/incompatible-extractor-support",
    args = ["--dry-run"]
)]
fn incompatible_existing_extractor_support_dependency_is_reported(output: e2e::ToolError) {
    assert!(
        output
            .stderr()
            .contains("dependency 'support' conflicts with extractor configuration"),
        "{}",
        output.stderr()
    );
}

#[e2e::test(target = "tests/crates/enabled-llzk-without-field")]
fn enabled_llzk_requires_a_field(output: e2e::ToolError) {
    assert!(
        output
            .stderr()
            .contains("LLZK is enabled but backends.llzk.field is missing")
    );
}
