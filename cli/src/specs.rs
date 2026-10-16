use std::path::{Path, PathBuf};

use haloumi_inject::spec::SpecRegistry;

use crate::Error;

const DEFAULT_SPECS_DIR: &str = ".haloumi/specs";

#[derive(Debug)]
pub struct SpecRegistrySource {
    explicit: bool,
    path: PathBuf,
}

impl SpecRegistrySource {
    fn new(path: PathBuf, explicit: bool) -> Self {
        Self { explicit, path }
    }

    pub fn explicit(base: impl AsRef<Path>, path: impl AsRef<Path>) -> Self {
        Self::new(base.as_ref().join(path), true)
    }

    pub fn default(root: impl AsRef<Path>) -> Self {
        Self::new(root.as_ref().join(DEFAULT_SPECS_DIR), false)
    }

    pub fn load(&self) -> Result<SpecRegistry, Error> {
        // If not explicitly set, and the path is not a valid directory, then return an empty
        // registry.
        if !self.explicit && !self.path.is_dir() {
            return Ok(SpecRegistry::empty());
        }

        Ok(SpecRegistry::load(&self.path)?)
    }
}
