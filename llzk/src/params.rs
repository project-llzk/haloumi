use haloumi_ir::Prime;
use llzk::prelude::*;
use melior::Context;

/// Stores the parameters for configuring the field
/// used for the Felt types.
///
/// Stores the name of the spec, and, if its not a
/// builtin, the prime value for defining the spec.
#[derive(Debug, Clone)]
pub struct FieldSpecParam {
    name: String,
    prime: Option<Prime>,
}

impl FieldSpecParam {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn prime(&self) -> Option<Prime> {
        self.prime
    }
}

/// Configuration for the LLZK backend.
#[derive(Clone, Debug)]
pub struct LlzkParams<'c> {
    context: &'c LlzkContext,
    top_level: Option<String>,
    inline: bool,
    optimize: bool,
    spec: Option<FieldSpecParam>,
}

impl<'c> LlzkParams<'c> {
    /// Creates new parameters with the default configuration.
    pub fn new(context: &'c LlzkContext) -> Self {
        Self {
            context,
            top_level: Default::default(),
            optimize: true,
            inline: false,
            spec: None,
        }
    }

    /// Returns a reference to the [`melior::Context`].
    pub fn context(&self) -> &'c Context {
        self.context
    }

    /// Returns the name of the top-level structure if it was configured.
    pub fn top_level(&self) -> Option<&str> {
        self.top_level.as_deref()
    }

    /// Returns wether inlining is enabled or not.
    pub fn inline(&self) -> bool {
        self.inline
    }

    /// Returns true if optimization is enabled.
    pub fn optimize(&self) -> bool {
        self.optimize
    }

    /// Returns the prime field spec, if available.
    pub fn spec(&self) -> Option<&FieldSpecParam> {
        self.spec.as_ref()
    }

    // Builder methods

    /// Sets the name of the top-level struct.
    pub fn with_top_level<S: ToString>(mut self, s: S) -> Self {
        self.top_level = Some(s.to_string());
        self
    }

    /// Removes the name of the top-level struct.
    pub fn no_top_level(mut self) -> Self {
        self.top_level = None;
        self
    }

    /// Sets lowering to inlining everything into one module.
    pub fn with_inline(mut self) -> Self {
        self.inline = true;
        self
    }

    /// Sets lowering to creating separate modules for each group.
    pub fn no_inline(mut self) -> Self {
        self.inline = false;
        self
    }

    /// Enables optimizations.
    pub fn with_optimization(mut self) -> Self {
        self.optimize = true;
        self
    }

    /// Disables optimizations.
    pub fn no_optimize(mut self) -> Self {
        self.optimize = false;
        self
    }

    /// Sets the prime field spec.
    pub fn with_prime_field(mut self, name: &str, prime: Prime) -> Self {
        self.spec = Some(FieldSpecParam {
            name: name.to_owned(),
            prime: Some(prime),
        });
        self
    }

    /// Sets the prime field from a builtin spec.
    pub fn with_builtin_field(mut self, name: &str) -> Self {
        self.spec = Some(FieldSpecParam {
            name: name.to_owned(),
            prime: None,
        });
        self
    }

    /// Removes the prime field spec.
    pub fn no_prime_field(mut self) -> Self {
        self.spec = None;
        self
    }
}
