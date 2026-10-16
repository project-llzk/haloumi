use haloumi_core::llzk::LlzkOutputFormat;
use serde::Deserialize;

use crate::backends::BackendConfig;

use super::Config;

#[derive(Debug, Default, Deserialize, Clone)]
pub(super) struct Backends {
    picus: Option<PicusBackend>,
    llzk: Option<LlzkBackend>,
    ir: Option<SimpleBackend>,
}

impl Backends {
    pub(super) fn picus(&self) -> Option<&PicusBackend> {
        self.picus.as_ref()
    }

    pub(super) fn llzk(&self) -> Option<&LlzkBackend> {
        self.llzk.as_ref()
    }

    pub(super) fn ir(&self) -> Option<&SimpleBackend> {
        self.ir.as_ref()
    }
}

#[derive(Debug, Default, Deserialize, Clone)]
pub(super) struct SimpleBackend {
    enabled: Option<bool>,
}

#[derive(Debug, Default, Deserialize, Clone)]
pub(super) struct PicusBackend {
    enabled: Option<bool>,
    optimize: Option<bool>,
}

#[derive(Debug, Default, Deserialize, Clone)]
pub(super) struct LlzkBackend {
    enabled: Option<bool>,
    optimize: Option<bool>,
    field: Option<String>,
    format: Option<LlzkOutputFormat>,
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
    pub fn optimize(&self) -> bool {
        self.optimize.unwrap_or(true)
    }
}

impl LlzkBackend {
    pub fn optimize(&self) -> bool {
        self.optimize.unwrap_or(true)
    }

    pub fn field(&self) -> Option<&str> {
        self.field.as_deref()
    }

    pub fn emit_assembly(&self) -> bool {
        matches!(self.format, Some(LlzkOutputFormat::Assembly))
    }
}

impl Config {}

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
                field: Some("bn254".into()),
                format: None,
            }
            .enabled()
        );
        assert!(
            !LlzkBackend {
                enabled: Some(false),
                optimize: None,
                field: Some("bn254".into()),
                format: None,
            }
            .enabled()
        );
        assert!(
            LlzkBackend {
                enabled: Some(true),
                optimize: None,
                field: None,
                format: None,
            }
            .enabled()
        );
    }
}
