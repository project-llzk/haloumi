use std::path::Path;

use cargo_toml::{Dependency, DepsSet, VersionReq};
use serde::Deserialize;

use crate::Error;

use super::Config;

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

/// The resolved dependencies required by the generated extractor binary.
#[derive(Debug)]
pub(crate) struct ExtractorConfig {
    name: String,
    dependency: Dependency,
    dependency_explicit: bool,
    dependencies: DepsSet,
    /// Configures whether groups are enabled or not during extraction.
    ///
    /// On by default.
    groups_enabled: bool,
    /// Named semantic preludes forwarded to the extractor runner.
    preludes: Option<Vec<String>>,
    /// Configures whether the runner optimizes resolved IR.
    optimize: bool,
}

impl ExtractorConfig {
    /// Returns the Cargo dependency key for the extractor API crate.
    pub(crate) fn name(&self) -> &str {
        &self.name
    }

    /// Returns the extractor API crate dependency definition.
    pub(crate) fn dependency(&self) -> &Dependency {
        &self.dependency
    }

    /// Returns whether the runner dependency was explicitly configured.
    pub(crate) fn dependency_explicit(&self) -> bool {
        self.dependency_explicit
    }

    /// Returns additional dependencies for the generated binary.
    pub(crate) fn dependencies(&self) -> &DepsSet {
        &self.dependencies
    }

    /// Returns whether groups are enabled or not.
    pub fn groups_enabled(&self) -> bool {
        self.groups_enabled
    }

    /// Returns configured semantic prelude names, if present.
    pub(crate) fn preludes(&self) -> Option<&[String]> {
        self.preludes.as_deref()
    }

    /// Returns whether resolved IR optimization is enabled.
    pub(crate) fn optimize(&self) -> bool {
        self.optimize
    }
}

impl Config {
    /// Returns the extractor crate and extra dependencies for the generated binary.
    pub(crate) fn extractor(&self) -> Result<ExtractorConfig, Error> {
        let source = self
            .sources
            .iter()
            .find(|source| source.data.extractor.is_some());
        let extractor = source.and_then(|source| source.data.extractor.as_ref());
        let name = extractor
            .and_then(|value| value.name.clone())
            .unwrap_or_else(|| "haloumi-extractor-runner".into());
        let groups_enabled = extractor.and_then(|value| value.groups).unwrap_or(true);
        let preludes = extractor.and_then(|value| value.preludes.clone());
        let optimize = extractor.and_then(|value| value.optimize).unwrap_or(true);
        let configured_dependency = extractor.and_then(|value| value.dependency.clone());
        let mut dependency = configured_dependency.clone().unwrap_or_else(|| {
            Dependency::Simple(
                VersionReq::parse(&format!("<= {}", env!("CARGO_PKG_VERSION")))
                    .expect("package version is valid"),
            )
        });
        let base = source.map(|source| source.base.as_path());
        rebase_dependency(&mut dependency, base)?;
        let mut dependencies = extractor
            .map(|value| value.dependencies.clone())
            .unwrap_or_default();
        for dependency in dependencies.values_mut() {
            rebase_dependency(dependency, base)?;
        }
        Ok(ExtractorConfig {
            name,
            dependency,
            dependency_explicit: configured_dependency.is_some(),
            dependencies,
            groups_enabled,
            preludes,
            optimize,
        })
    }
}

fn rebase_dependency(dependency: &mut Dependency, base: Option<&Path>) -> Result<(), Error> {
    let Some(base) = base else { return Ok(()) };
    if dependency.detail().is_none() {
        return Ok(());
    }
    let detail = dependency.try_detail_mut()?;
    if let Some(path) = detail.path.as_ref()
        && Path::new(path).is_relative()
    {
        detail.path = Some(base.join(path).display().to_string());
    }
    Ok(())
}
