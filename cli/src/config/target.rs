use serde::Deserialize;

use super::Config;

#[derive(Debug, Default, Clone, Deserialize)]
pub(crate) struct Target {
    #[serde(default)]
    features: Vec<String>,
    #[serde(default, rename = "no-default-features")]
    no_default_features: bool,
    #[serde(default, rename = "all-features")]
    all_features: bool,
}

impl Target {
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

impl Config {
    ///// Returns the selected target's Cargo feature settings.
    //pub(crate) fn target(&self) -> TargetConfig {
    //    let target = self
    //        .sources
    //        .iter()
    //        .find_map(|source| source.data.target.as_ref())
    //        .cloned()
    //        .unwrap_or_default();
    //    TargetConfig {
    //        features: target.features,
    //        no_default_features: target.no_default_features,
    //        all_features: target.all_features,
    //    }
    //}
}
