/// Common enablement rules for configured output backends.
pub trait BackendConfig {
    /// Returns the explicit backend enablement setting, if configured.
    fn enabled_override(&self) -> Option<bool>;

    /// Returns whether the backend's mandatory parameter blocks are configured.
    fn mandatory_parameters_configured(&self) -> bool {
        false
    }

    /// Returns whether this backend is enabled.
    fn enabled(&self) -> bool {
        self.enabled_override()
            .unwrap_or_else(|| self.mandatory_parameters_configured())
    }
}
