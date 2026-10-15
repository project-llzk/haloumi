use std::path::PathBuf;

use serde::Deserialize;

use super::Config;

#[derive(Debug, Default, Deserialize)]
pub(super) struct Specs {
    path: Option<PathBuf>,
}

impl Config {
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
}
