//! Haloumi configuration discovery and lookup.

use std::{
    fs,
    path::{Path, PathBuf},
};

use serde::Deserialize;

use crate::Error;

mod backends;
mod extractor;
mod specs;
mod target;

use backends::Backends;
use extractor::Extractor;
use specs::Specs;
use target::Target;

pub(crate) use target::TargetConfig;

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
}
