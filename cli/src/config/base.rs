use std::{
    fs,
    path::{Path, PathBuf},
};

use serde::Deserialize;

use crate::{
    Error,
    config::{Backends, Extractor, Specs, Target},
};

struct DefaultConfigSource(&'static str, &'static str);

impl DefaultConfigSource {
    fn load(&self, root: impl AsRef<Path>) -> Result<Option<ConfigSource>, Error> {
        let path = root.as_ref().join(self.0);
        let base = root.as_ref().join(self.1);
        if !path.is_file() {
            return Ok(None);
        }
        let path = path.canonicalize()?;
        let base = base.canonicalize()?;

        log::debug!("Loading configuration from {}", path.display());
        Ok(Some(ConfigSource {
            base,
            data: toml::from_str(&fs::read_to_string(path)?)?,
        }))
    }
}

const DEFAULT_CONFIG_SOURCES: &[DefaultConfigSource] = &[
    DefaultConfigSource(".haloumi.toml", "."),
    DefaultConfigSource(".haloumi/cfg.toml", ".haloumi"),
];

pub(super) struct ConfigSources(Vec<ConfigSource>);

impl ConfigSources {
    pub(super) fn default_sources(root: impl AsRef<Path>) -> Result<Self, Error> {
        let mut sources = Vec::with_capacity(DEFAULT_CONFIG_SOURCES.len());
        for source in DEFAULT_CONFIG_SOURCES {
            if let Some(source) = source.load(&root)? {
                sources.push(source);
            }
        }
        Ok(Self(sources))
    }

    pub(super) fn find<'a, T>(&'a self, f: impl FnMut(&'a ConfigSource) -> Option<T>) -> Option<T> {
        self.0.iter().find_map(f)
    }

    pub(crate) fn specs(&self) -> Option<(&Path, &Specs)> {
        self.find(|src| src.specs())
    }

    pub(crate) fn target(&self) -> Option<&Target> {
        self.find(ConfigSource::target)
    }

    pub(crate) fn backends(&self) -> Option<&Backends> {
        self.find(ConfigSource::backends)
    }

    pub(crate) fn extractor(&self) -> Option<(&Path, &Extractor)> {
        self.find(ConfigSource::extractor)
    }
}

#[derive(Debug)]
pub(super) struct ConfigSource {
    base: PathBuf,
    data: ConfigData,
}

impl ConfigSource {
    pub fn specs(&self) -> Option<(&Path, &Specs)> {
        self.data
            .specs
            .as_ref()
            .map(|specs| (self.base.as_path(), specs))
    }

    pub fn target(&self) -> Option<&Target> {
        self.data.target.as_ref()
    }

    pub fn backends(&self) -> Option<&Backends> {
        self.data.backends.as_ref()
    }

    pub fn extractor(&self) -> Option<(&Path, &Extractor)> {
        self.data
            .extractor
            .as_ref()
            .map(|extractor| (self.base.as_path(), extractor))
    }
}

#[derive(Debug, Default, Deserialize)]
struct ConfigData {
    specs: Option<Specs>,
    target: Option<Target>,
    backends: Option<Backends>,
    extractor: Option<Extractor>,
}
