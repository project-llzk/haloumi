use haloumi_backend::codegen::CodegenParams;
use llzk::prelude::{FeltType, FieldSpecAttribute};
use melior::Context;

use super::LlzkParams;

#[derive(Debug)]
pub struct LlzkCodegenState<'c> {
    context: &'c Context,
    params: LlzkParams<'c>,
}

impl<'c> LlzkCodegenState<'c> {
    pub fn context(&self) -> &'c Context {
        self.context
    }

    pub fn params(&self) -> &LlzkParams<'c> {
        &self.params
    }

    /// Returns true if optimization is enabled.
    pub fn optimize(&self) -> bool {
        self.params.optimize()
    }

    /// Returns true if struct members need to be marked as signals.
    pub fn members_are_signals(&self) -> bool {
        self.params.members_are_signals()
    }

    /// Returns true if struct members need to be marked as columns.
    pub fn members_are_columns(&self) -> bool {
        self.params.members_are_columns()
    }

    /// Returns the prime field spec if available.
    ///
    /// Only returns a value if the spec was configured with a custom field. If the user configured
    /// the field with a builtin then this method returns `None` since there's no need for setting
    /// the `llzk.fields` attribute in the resulting module.
    pub fn spec(&self) -> Option<FieldSpecAttribute<'c>> {
        let spec = self.params.spec()?;
        let prime = spec.prime()?;
        Some(FieldSpecAttribute::from_biguint(
            self.context,
            spec.name(),
            prime.value(),
        ))
    }

    /// Returns the field spec name, if available.
    pub fn field_name(&self) -> Option<&str> {
        self.params.spec().map(|spec| spec.name())
    }

    /// Returns the correct felt type based on the spec parameter.
    ///
    /// If the spec is available returns `!felt.type<"spec">` otherwise
    /// returns an unspecified `!felt.type`.
    pub fn felt_type(&self) -> FeltType<'c> {
        match self.params.spec() {
            Some(spec) => FeltType::with_field(self.context, spec.name()),
            None => FeltType::new(self.context),
        }
    }
}

impl<'c> From<LlzkParams<'c>> for LlzkCodegenState<'c> {
    fn from(params: LlzkParams<'c>) -> Self {
        Self {
            context: params.context(),
            params,
        }
    }
}

impl CodegenParams for LlzkCodegenState<'_> {
    fn inlining_enabled(&self) -> bool {
        self.params().inline()
    }
}
