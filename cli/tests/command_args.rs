//! Tests for arguments forwarded to the generated extractor.

use std::{
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

fn run_with_args_output(temp: &TempDir) -> String {
    let args_output = temp.path().join("extractor-args");
    let output = cli()
        .current_dir(temp.path())
        .env("HALOUMI_TEST_ARGS_OUTPUT", &args_output)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    fs::read_to_string(args_output).unwrap()
}

#[test]
fn higher_priority_backend_table_blocks_lower_priority_backend_parameters() {
    let temp = copy_fixture("config-chain-root");
    let args = run_with_args_output(&temp);
    assert!(args.contains("--format\nir"), "{args}");
    assert!(!args.contains("--llzk-field-name"), "{args}");
    assert!(args.contains("--preludes\nalpha,beta"), "{args}");
    assert!(!args.contains("--no-opt"), "{args}");
    assert!(!args.contains("--picus-no-opt"), "{args}");
    assert!(!args.contains("--llzk-no-opt"), "{args}");
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
fn disabled_optimization_is_forwarded_independently() {
    let temp = copy_fixture("config-chain-root");
    let config = temp.path().join(".haloumi.toml");
    let contents = fs::read_to_string(&config).unwrap();
    fs::write(
        &config,
        contents.replace(
            "preludes = [\"alpha\", \"beta\"]",
            "preludes = [\"alpha\", \"beta\"]\noptimize = false",
        ) + "\n[backends.picus]\noptimize = false\n\n[backends.llzk]\noptimize = false\n",
    )
    .unwrap();
    let args = run_with_args_output(&temp);
    assert!(args.contains("--no-opt"), "{args}");
    assert!(args.contains("--picus-no-opt"), "{args}");
    assert!(args.contains("--llzk-no-opt"), "{args}");
}

#[test]
fn omitted_or_empty_preludes_are_not_forwarded() {
    for replacement in ["", "preludes = []\n"] {
        let temp = copy_fixture("config-chain-root");
        let config = temp.path().join(".haloumi.toml");
        let contents = fs::read_to_string(&config).unwrap();
        fs::write(
            &config,
            contents.replace("preludes = [\"alpha\", \"beta\"]\n", replacement),
        )
        .unwrap();
        let args = run_with_args_output(&temp);
        assert!(!args.contains("--preludes"), "{args}");
    }
}

#[test]
fn llzk_field_implicitly_enables_llzk() {
    let temp = copy_fixture("config-chain-root");
    let config = temp.path().join(".haloumi.toml");
    let contents = fs::read_to_string(&config).unwrap();
    fs::write(
        &config,
        contents.replace(
            "[backends.ir]\nenabled = true",
            "[backends.llzk]\nfield = \"bn256\"",
        ),
    )
    .unwrap();
    let args = run_with_args_output(&temp);
    assert!(args.contains("--format\nllzk"), "{args}");
    assert!(args.contains("--llzk-field-name\nbn256"), "{args}");
}

#[test]
fn llzk_assembly_format_is_forwarded() {
    let temp = copy_fixture("config-chain-root");
    let config = temp.path().join(".haloumi.toml");
    let contents = fs::read_to_string(&config).unwrap();
    fs::write(
        &config,
        contents.replace(
            "[backends.ir]\nenabled = true",
            "[backends.llzk]\nfield = \"bn256\"\nformat = \"assembly\"",
        ),
    )
    .unwrap();
    assert!(run_with_args_output(&temp).contains("--llzk-emit-assembly"));
}

#[test]
fn explicit_backend_enablement_overrides_defaulting() {
    let temp = copy_fixture("config-chain-root");
    let config = temp.path().join(".haloumi.toml");
    let contents = fs::read_to_string(&config).unwrap();
    fs::write(
        &config,
        contents.replace(
            "[backends.ir]\nenabled = true",
            "[backends.llzk]\nenabled = false\nfield = \"bn256\"",
        ),
    )
    .unwrap();
    let args = run_with_args_output(&temp);
    assert!(!args.contains("--format"), "{args}");
    assert!(!args.contains("--llzk-field-name"), "{args}");
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
            .join("target/haloumi/.cargo/release/haloumi-extractor")
            .is_file()
    );
    assert!(!args_output.exists());
}

#[test]
fn target_config_forwards_all_features_with_explicit_features() {
    let temp = copy_fixture("config-chain-root");
    let config = temp.path().join(".haloumi.toml");
    let contents = fs::read_to_string(&config).unwrap();
    fs::write(
        &config,
        contents.replace(
            "features = [\"configured-feature\"]\nno-default-features = true",
            "features = [\"configured-feature\"]\nall-features = true",
        ),
    )
    .unwrap();
    let args_output = temp.path().join("extractor-args");
    let output = cli()
        .current_dir(temp.path())
        .env("HALOUMI_TEST_ARGS_OUTPUT", &args_output)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(args_output.is_file());
}
