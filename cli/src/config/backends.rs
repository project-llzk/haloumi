use serde::Deserialize;

use crate::Error;

use super::Config;

#[derive(Debug, Default, Deserialize)]
pub(super) struct Backends {
    picus: Option<PicusBackend>,
    llzk: Option<LlzkBackend>,
    ir: Option<SimpleBackend>,
}

#[derive(Debug, Default, Deserialize)]
struct SimpleBackend {
    enabled: Option<bool>,
}

#[derive(Debug, Default, Deserialize)]
struct PicusBackend {
    enabled: Option<bool>,
    optimize: Option<bool>,
}

#[derive(Debug, Default, Deserialize)]
struct LlzkBackend {
    enabled: Option<bool>,
    optimize: Option<bool>,
    field: Option<Field>,
}

#[derive(Debug, Default, Deserialize)]
struct Field {
    builtin: Option<String>,
}

/// Common enablement rules for configured output backends.
trait BackendConfig {
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

impl BackendConfig for SimpleBackend {
    fn enabled_override(&self) -> Option<bool> {
        self.enabled
    }
}

impl BackendConfig for PicusBackend {
    fn enabled_override(&self) -> Option<bool> {
        self.enabled
    }
}

impl BackendConfig for LlzkBackend {
    fn enabled_override(&self) -> Option<bool> {
        self.enabled
    }

    fn mandatory_parameters_configured(&self) -> bool {
        self.field.is_some()
    }
}

impl PicusBackend {
    fn optimize(&self) -> bool {
        self.optimize.unwrap_or(true)
    }
}

impl LlzkBackend {
    fn optimize(&self) -> bool {
        self.optimize.unwrap_or(true)
    }
}

impl Config {
    /// Returns enabled extractor output formats.
    pub(crate) fn formats(&self) -> Vec<&'static str> {
        let Some(backends) = self.backends() else {
            return Vec::new();
        };
        let mut formats = Vec::new();
        if backends.ir.as_ref().is_some_and(BackendConfig::enabled) {
            formats.push("ir");
        }
        if backends.picus.as_ref().is_some_and(BackendConfig::enabled) {
            formats.push("picus");
        }
        if backends.llzk.as_ref().is_some_and(BackendConfig::enabled) {
            formats.push("llzk");
        }
        formats
    }

    /// Returns the built-in LLZK field name, when LLZK is configured completely.
    pub(crate) fn llzk_field(&self) -> Option<&str> {
        let llzk = self.backends()?.llzk.as_ref()?;
        llzk.enabled()
            .then_some(llzk)?
            .field
            .as_ref()?
            .builtin
            .as_deref()
    }

    /// Returns whether Picus optimization is enabled.
    pub(crate) fn picus_optimize(&self) -> bool {
        self.backends()
            .and_then(|backends| backends.picus.as_ref())
            .is_none_or(PicusBackend::optimize)
    }

    /// Returns whether LLZK optimization is enabled.
    pub(crate) fn llzk_optimize(&self) -> bool {
        self.backends()
            .and_then(|backends| backends.llzk.as_ref())
            .is_none_or(LlzkBackend::optimize)
    }

    /// Validates configuration values required by enabled backends.
    pub(crate) fn validate(&self) -> Result<(), Error> {
        if self
            .backends()
            .and_then(|backends| backends.llzk.as_ref())
            .is_some_and(BackendConfig::enabled)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_backends_require_explicit_enablement() {
        assert!(!SimpleBackend { enabled: None }.enabled());
        assert!(
            SimpleBackend {
                enabled: Some(true)
            }
            .enabled()
        );
        assert!(
            !SimpleBackend {
                enabled: Some(false)
            }
            .enabled()
        );
    }

    #[test]
    fn llzk_enablement_uses_field_presence_unless_overridden() {
        assert!(
            LlzkBackend {
                enabled: None,
                optimize: None,
                field: Some(Field { builtin: None }),
            }
            .enabled()
        );
        assert!(
            !LlzkBackend {
                enabled: Some(false),
                optimize: None,
                field: Some(Field { builtin: None }),
            }
            .enabled()
        );
        assert!(
            LlzkBackend {
                enabled: Some(true),
                optimize: None,
                field: None,
            }
            .enabled()
        );
    }
}
