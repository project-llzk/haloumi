//! Haloumi configuration discovery and lookup.

use std::{
    fs,
    path::{Path, PathBuf},
};

use cargo_toml::{Dependency, DepsSet, VersionReq};
use serde::Deserialize;

use crate::Error;

/// Configuration loaded from all discovered sources in priority order.
#[derive(Debug)]
pub(crate) struct Config {
    root: PathBuf,
    sources: Vec<ConfigSource>,
}

#[derive(Debug)]
struct ConfigSource {
    base: PathBuf,
    data: ConfigData,
}

#[derive(Debug, Default, Deserialize)]
struct ConfigData {
    specs: Option<Specs>,
    target: Option<Target>,
    backends: Option<Backends>,
    extractor: Option<Extractor>,
}

#[derive(Debug, Default, Deserialize)]
struct Specs {
    path: Option<PathBuf>,
}

#[derive(Debug, Default, Clone, Deserialize)]
struct Target {
    #[serde(default)]
    features: Vec<String>,
    #[serde(default, rename = "no-default-features")]
    no_default_features: bool,
    #[serde(default, rename = "all-features")]
    all_features: bool,
}

/// Cargo feature settings for the extraction target.
#[derive(Debug, Default, Clone)]
pub(crate) struct TargetConfig {
    features: Vec<String>,
    no_default_features: bool,
    all_features: bool,
}

impl TargetConfig {
    /// Returns the explicitly enabled feature names.
    pub(crate) fn features(&self) -> &[String] {
        &self.features
    }

    /// Returns whether default features are disabled.
    pub(crate) fn no_default_features(&self) -> bool {
        self.no_default_features
    }

    /// Returns whether all target features are enabled.
    pub(crate) fn all_features(&self) -> bool {
        self.all_features
    }
}

#[derive(Debug, Default, Deserialize)]
struct Backends {
    picus: Option<Empty>,
    llzk: Option<Llzk>,
    ir: Option<Empty>,
}

#[derive(Debug, Default, Deserialize)]
struct Empty {}

#[derive(Debug, Default, Deserialize)]
struct Llzk {
    field: Option<Field>,
}

#[derive(Debug, Default, Deserialize)]
struct Field {
    builtin: Option<String>,
}

#[derive(Debug, Default, Deserialize)]
struct Extractor {
    name: Option<String>,
    dependency: Option<Dependency>,
    #[serde(default)]
    dependencies: DepsSet,
    groups: Option<bool>,
}

/// The resolved dependencies required by the generated extractor binary.
#[derive(Debug)]
pub(crate) struct ExtractorConfig {
    name: String,
    dependency: Dependency,
    dependencies: DepsSet,
    /// Configures whether groups are enabled or not during extraction.
    ///
    /// On by default.
    groups_enabled: bool,
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

    /// Returns additional dependencies for the generated binary.
    pub(crate) fn dependencies(&self) -> &DepsSet {
        &self.dependencies
    }

    /// Returns whether groups are enabled or not.
    pub fn groups_enabled(&self) -> bool {
        self.groups_enabled
    }
}

impl Config {
    /// Loads every supported configuration file in descending priority order.
    pub(crate) fn load(root: &Path) -> Result<Self, Error> {
        let mut sources = Vec::new();
        for (path, base) in [
            (root.join(".haloumi.toml"), root.to_path_buf()),
            (root.join(".haloumi/cfg.toml"), root.join(".haloumi")),
        ] {
            if path.is_file() {
                log::debug!("Loading configuration from {}", path.display());
                sources.push(ConfigSource {
                    base,
                    data: toml::from_str(&fs::read_to_string(path)?)?,
                });
            }
        }
        Ok(Self {
            root: root.to_path_buf(),
            sources,
        })
    }

    /// Returns the resolved specification registry path.
    pub(crate) fn specs_path(&self) -> PathBuf {
        self.sources
            .iter()
            .find_map(|source| {
                source.data.specs.as_ref().map(|specs| {
                    specs
                        .path
                        .as_ref()
                        .map(|path| source.base.join(path))
                        .unwrap_or_else(|| self.root.join(".haloumi/specs"))
                })
            })
            .unwrap_or_else(|| self.root.join(".haloumi/specs"))
    }

    /// Returns the selected target's Cargo feature settings.
    pub(crate) fn target(&self) -> TargetConfig {
        let target = self
            .sources
            .iter()
            .find_map(|source| source.data.target.as_ref())
            .cloned()
            .unwrap_or_default();
        TargetConfig {
            features: target.features,
            no_default_features: target.no_default_features,
            all_features: target.all_features,
        }
    }

    /// Returns enabled extractor output formats.
    pub(crate) fn formats(&self) -> Vec<&'static str> {
        let Some(backends) = self.backends() else {
            return Vec::new();
        };
        let mut formats = Vec::new();
        if backends.ir.is_some() {
            formats.push("ir");
        }
        if backends.picus.is_some() {
            formats.push("picus");
        }
        if backends.llzk.is_some() {
            formats.push("llzk");
        }
        formats
    }

    /// Returns the built-in LLZK field name, when LLZK is configured completely.
    pub(crate) fn llzk_field(&self) -> Option<&str> {
        self.backends()?
            .llzk
            .as_ref()?
            .field
            .as_ref()?
            .builtin
            .as_deref()
    }

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
        let mut dependency = extractor
            .and_then(|value| value.dependency.clone())
            .unwrap_or_else(|| {
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
            dependencies,
            groups_enabled,
        })
    }

    /// Validates configuration values required by enabled backends.
    pub(crate) fn validate(&self) -> Result<(), Error> {
        if self
            .backends()
            .and_then(|backends| backends.llzk.as_ref())
            .is_some()
            && self.llzk_field().is_none()
        {
            return Err(Error::Message(
                "LLZK is enabled but backends.llzk.field.builtin is missing".into(),
            ));
        }
        Ok(())
    }

    fn backends(&self) -> Option<&Backends> {
        self.sources
            .iter()
            .find_map(|source| source.data.backends.as_ref())
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
