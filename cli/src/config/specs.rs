use std::path::{Path, PathBuf};

use serde::Deserialize;

#[derive(Debug, Default, Deserialize)]
pub(super) struct Specs {
    path: Option<PathBuf>,
}

impl Specs {
    pub(super) fn path(&self) -> Option<&Path> {
        self.path.as_deref()
    }
}
