use std::collections::BTreeMap;

use haloumi_inject::{
    Injector,
    crate_info::{Crate, CrateMut},
    spec::SpecMatch,
};

use crate::{Error, app::AppState};

pub(crate) fn patch_direct_dependencies(
    state: &AppState,
    root: &mut CrateMut,
) -> Result<(), Error> {
    let dependencies = state.project.normal_direct_dependencies(&state.target)?;
    let mut package_ids = BTreeMap::new();
    for dependency in &dependencies {
        match state
            .specs
            .find_matching(&dependency.package.name, &dependency.package.version)
        {
            SpecMatch::None => {}
            SpecMatch::Ambiguous(specs) => {
                return Err(Error::Message(format!(
                    "{} specs match {} {}",
                    specs.len(),
                    dependency.package.name,
                    dependency.package.version
                )));
            }
            SpecMatch::One(_) => {
                let key = (
                    dependency.package.name.clone(),
                    dependency.package.version.to_string(),
                );
                if let Some(existing_id) = package_ids.insert(key, dependency.package.id.clone())
                    && existing_id != dependency.package.id
                {
                    return Err(Error::Message(format!(
                        "multiple direct dependencies named {} {} resolve to different package IDs; patching them is unsupported",
                        dependency.package.name, dependency.package.version
                    )));
                }
            }
        }
    }
    for dependency in dependencies {
        match state
            .specs
            .find_matching(&dependency.package.name, &dependency.package.version)
        {
            SpecMatch::None => log::debug!(
                "No spec matches {} {}",
                dependency.package.name,
                dependency.package.version
            ),
            SpecMatch::Ambiguous(specs) => {
                return Err(Error::Message(format!(
                    "{} specs match {} {}",
                    specs.len(),
                    dependency.package.name,
                    dependency.package.version
                )));
            }
            SpecMatch::One(_) => {
                let destination = state.paths.dependency_copy(&dependency.package);
                let source =
                    Crate::open(dependency.package.manifest_path.parent().ok_or_else(|| {
                        Error::Message("dependency manifest has no parent".into())
                    })?)?;
                Injector::new(&source, &state.specs)?.apply(&destination)?;
                root.replace_dependency_with_path(&dependency.name, destination)?;
            }
        }
    }
    Ok(())
}
