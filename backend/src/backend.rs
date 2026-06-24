use std::marker::PhantomData;

use haloumi_ir_gen::{circuit::resolved::ResolvedIRCircuit, ctx::IRCtx};

use crate::codegen::{
    Codegen, CodegenParams, CodegenStrategy,
    strats::{groups::GroupConstraintsStrat, inline::InlineConstraintsStrat},
};

/// Entrypoint for the backend.
pub struct Backend<C, S> {
    state: S,
    _codegen: PhantomData<C>,
}

impl<C, S: std::fmt::Debug> std::fmt::Debug for Backend<C, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Backend")
            .field("state", &self.state)
            .finish()
    }
}

impl<C, S> Backend<C, S> {
    /// Initializes the backend.
    pub fn initialize<P: Clone + Into<S>>(params: P) -> Self {
        Self {
            state: params.into(),
            _codegen: PhantomData,
        }
    }
}

impl<'b, 's: 'b, C> Backend<C, C::State>
where
    C: Codegen<'s, 'b>,
    C::State: 's,
    C::Output: 's,
    C::State: CodegenParams,
{
    fn create_codegen(&'b self) -> C {
        C::initialize(&self.state)
    }

    /// Generate code using the default strategy.
    pub fn codegen(&'b self, ir: &ResolvedIRCircuit, ctx: &IRCtx) -> Result<C::Output, C::Error> {
        if self.state.inlining_enabled() {
            self.codegen_with_strat(ir, ctx, InlineConstraintsStrat::default())
        } else {
            self.codegen_with_strat(ir, ctx, GroupConstraintsStrat::default())
        }
    }

    /// Generate code using the given strategy.
    fn codegen_with_strat(
        &'b self,
        ir: &ResolvedIRCircuit,
        ctx: &IRCtx,
        strat: impl CodegenStrategy,
    ) -> Result<C::Output, C::Error> {
        log::debug!("Initializing code generator");
        let codegen = self.create_codegen();
        codegen.set_prime_field(ir.prime())?;
        log::debug!(
            "Starting code generation with {} strategy...",
            std::any::type_name_of_val(&strat)
        );

        strat.codegen(&codegen, ctx, ir)?;

        log::debug!("Code generation completed");
        codegen.generate_output()
    }
}
