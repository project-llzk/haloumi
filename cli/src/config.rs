//! Haloumi configuration discovery and lookup.

mod backends;
mod base;
mod extractor;
mod specs;
mod target;

use std::path::Path;

use backends::Backends;
use extractor::Extractor;
use haloumi_inject::spec::SpecRegistry;
use specs::Specs;

pub(crate) use target::Target;

use crate::{
    Error,
    backends::BackendConfig,
    config::{
        backends::{LlzkBackend, PicusBackend},
        base::ConfigSources,
    },
    extractor::ExtractorConfig,
    specs::SpecRegistrySource,
};

/// Configuration loaded from all discovered sources in priority order.
#[derive(Debug)]
pub(crate) struct Config {
    specs: SpecRegistry,
    target: Target,
    extractor: ExtractorConfig,
    backends: Backends,
}

impl Config {
    /// Loads every supported configuration file in descending priority order.
    pub(crate) fn load(root: impl AsRef<Path>) -> Result<Self, Error> {
        let sources = ConfigSources::default_sources(&root)?;

        let specs = sources
            .specs()
            .and_then(|(base, specs)| Some(SpecRegistrySource::explicit(base, specs.path()?)))
            .unwrap_or_else(|| SpecRegistrySource::default(&root))
            .load()?;
        let extractor = sources
            .extractor()
            .map(|(base, extractor)| extractor.make_config(base))
            .transpose()?
            .unwrap_or_default();
        let backends = sources.backends().cloned().unwrap_or_default();
        Ok(Self {
            target: sources.target().cloned().unwrap_or_default(),
            specs,
            extractor,
            backends,
        })
    }

    pub(crate) fn specs(&self) -> &SpecRegistry {
        &self.specs
    }

    pub(crate) fn target(&self) -> &Target {
        &self.target
    }

    pub(crate) fn extractor(&self) -> &ExtractorConfig {
        &self.extractor
    }

    /// Returns enabled extractor output formats.
    pub(crate) fn formats(&self) -> Vec<&'static str> {
        let mut formats = Vec::new();
        if self.backends.ir().is_some_and(BackendConfig::enabled) {
            formats.push("ir");
        }
        if self.backends.picus().is_some_and(BackendConfig::enabled) {
            formats.push("picus");
        }
        if self.backends.llzk().is_some_and(BackendConfig::enabled) {
            formats.push("llzk");
        }
        formats
    }

    /// Returns the built-in LLZK field name, when LLZK is configured completely.
    pub(crate) fn llzk_field(&self) -> Option<&str> {
        let llzk = self.backends.llzk()?;
        llzk.enabled().then_some(llzk)?.field()?.builtin()
    }

    /// Returns whether Picus optimization is enabled.
    pub(crate) fn picus_optimize(&self) -> bool {
        self.backends.picus().is_none_or(PicusBackend::optimize)
    }

    /// Returns whether LLZK optimization is enabled.
    pub(crate) fn llzk_optimize(&self) -> bool {
        self.backends.llzk().is_none_or(LlzkBackend::optimize)
    }

    /// Validates configuration values required by enabled backends.
    pub(crate) fn validate(&self) -> Result<(), Error> {
        if self.backends.llzk().is_some_and(BackendConfig::enabled) && self.llzk_field().is_none() {
            return Err(Error::Message(
                "LLZK is enabled but backends.llzk.field.builtin is missing".into(),
            ));
        }
        Ok(())
    }
}
