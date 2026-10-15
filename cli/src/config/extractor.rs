use std::path::Path;

use cargo_toml::{Dependency, DepsSet};
use serde::Deserialize;

use crate::{Error, extractor::ExtractorConfig};

#[derive(Debug, Default, Deserialize)]
pub(super) struct Extractor {
    name: Option<String>,
    dependency: Option<Dependency>,
    #[serde(default)]
    dependencies: DepsSet,
    groups: Option<bool>,
    preludes: Option<Vec<String>>,
    optimize: Option<bool>,
}

impl Extractor {
    pub(super) fn make_config(&self, base: impl AsRef<Path>) -> Result<ExtractorConfig, Error> {
        let mut config = ExtractorConfig::new();
        if let Some(name) = &self.name {
            config.set_name(name);
        }
        if let Some(dep) = &self.dependency {
            config.set_dependency(dep, &base)?;
        }
        config.set_dependencies(&self.dependencies, &base)?;
        if let Some(groups) = self.groups {
            config.set_groups_enabled(groups);
        }
        if let Some(optimize) = self.optimize {
            config.set_optimize(optimize);
        }
        if let Some(preludes) = &self.preludes {
            config.set_preludes(preludes.clone());
        }

        Ok(config)
    }
}

//impl Config {
//    /// Returns the extractor crate and extra dependencies for the generated binary.
//    pub(crate) fn extractor(&self) -> Result<ExtractorConfig, Error> {
//        let source = self
//            .sources
//            .iter()
//            .find(|source| source.data.extractor.is_some());
//        let extractor = source.and_then(|source| source.data.extractor.as_ref());
//        let name = extractor
//            .and_then(|value| value.name.clone())
//            .unwrap_or_else(|| "".into());
//        let groups_enabled = extractor.and_then(|value| value.groups).unwrap_or(true);
//        let preludes = extractor.and_then(|value| value.preludes.clone());
//        let optimize = extractor.and_then(|value| value.optimize).unwrap_or(true);
//        let configured_dependency = extractor.and_then(|value| value.dependency.clone());
//        let mut dependency = configured_dependency.clone().unwrap_or_else(|| {
//            Dependency::Simple(
//                VersionReq::parse(&format!("<= {}", env!("CARGO_PKG_VERSION")))
//                    .expect("package version is valid"),
//            )
//        });
//        let base = source.map(|source| source.base.as_path());
//        rebase_dependency(&mut dependency, base)?;
//        let mut dependencies = extractor
//            .map(|value| value.dependencies.clone())
//            .unwrap_or_default();
//        for dependency in dependencies.values_mut() {
//            rebase_dependency(dependency, base)?;
//        }
//        Ok(ExtractorConfig {
//            name,
//            dependency,
//            dependency_explicit: configured_dependency.is_some(),
//            dependencies,
//            groups_enabled,
//            preludes,
//            optimize,
//        })
//    }
//}

//fn rebase_dependency(dependency: &mut Dependency, base: Option<&Path>) -> Result<(), Error> {
//    let Some(base) = base else { return Ok(()) };
//    if dependency.detail().is_none() {
//        return Ok(());
//    }
//    let detail = dependency.try_detail_mut()?;
//    if let Some(path) = detail.path.as_ref()
//        && Path::new(path).is_relative()
//    {
//        detail.path = Some(base.join(path).display().to_string());
//    }
//    Ok(())
//}
