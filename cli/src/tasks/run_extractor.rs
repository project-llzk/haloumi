use std::process::Command;

use haloumi_inject::crate_info::{CrateLike, CrateMut};

use crate::{Error, app::AppState, config::TargetConfig};

pub(crate) fn run_extractor(state: &AppState, root: &CrateMut) -> Result<(), Error> {
    let mut command = Command::new("cargo");
    command
        .current_dir(root.base_path())
        .arg(if state.dry_run { "build" } else { "run" })
        .arg("--release")
        .arg("--bin")
        .arg("haloumi-extractor")
        .arg("--target-dir")
        .arg(&state.paths.cargo_target);
    add_target_feature_args(&mut command, &state.config.target());
    let extractor = state.config.extractor()?;
    if extractor.groups_enabled() {
        command.env("HALOUMI_ENABLE_GROUPS", "1");
    }
    if !state.dry_run {
        command.arg("--").arg("--output").arg(&state.paths.output);
        if !extractor.optimize() {
            command.arg("--no-opt");
        }
        if !state.config.picus_optimize() {
            command.arg("--picus-no-opt");
        }
        if !state.config.llzk_optimize() {
            command.arg("--llzk-no-opt");
        }
        let formats = state.config.formats();
        if !formats.is_empty() {
            command.arg("--format").arg(formats.join(","));
        }
        if let Some(field) = state.config.llzk_field() {
            command.arg("--llzk-field-name").arg(field);
        }
        if let Some(preludes) = extractor.preludes().filter(|preludes| !preludes.is_empty()) {
            command.arg("--preludes").arg(preludes.join(","));
        }
    }
    log::debug!("Running {:?}", command);
    if !command.status()?.success() {
        return Err(Error::Message("generated extractor command failed".into()));
    }
    Ok(())
}

fn add_target_feature_args(command: &mut Command, target: &TargetConfig) {
    if target.all_features() {
        command.arg("--all-features");
    }
    if target.no_default_features() {
        command.arg("--no-default-features");
    }
    if !target.features().is_empty() {
        command.arg("--features").arg(target.features().join(","));
    }
}
