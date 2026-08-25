//! Traits for defining code generators.

use std::cell::RefCell;
use std::rc::Rc;

use haloumi_ir::Prime;
use haloumi_ir::Slot;
use haloumi_ir_gen::{circuit::resolved::ResolvedIRCircuit, ctx::IRCtx};
use haloumi_lowering::{
    ExprLowering as _, Lowering, error::Error as LoweringError, lowerable::LowerableStmt,
};
use haloumi_synthesis::io::{AdviceIO, InstanceIO};

pub(crate) mod strats;

/// Implemented by code generators that emit some code representation of the circuit.
pub trait Codegen<'c: 's, 's>: Sized + 's {
    /// Implementation of the lowering behavior.
    type FuncOutput: Lowering;
    /// Final output of the code generator.
    type Output;
    /// Internal state of the code generator.
    type State: 'c;
    /// Error type of the code generator.
    type Error: From<LoweringError> + From<haloumi_ir_gen::error::Error>;

    /// Initializes the code generator.
    fn initialize(state: &'s Self::State) -> Self;

    /// Sets the prime field used by the circuit.
    ///
    /// By default does nothing.
    #[allow(unused_variables)]
    fn set_prime_field(&self, prime: Prime) -> Result<(), Self::Error> {
        Ok(())
    }

    /// Defines an empty function.
    fn define_function(
        &self,
        name: &str,
        inputs: usize,
        outputs: usize,
        callees: impl IntoIterator<Item = String>,
    ) -> Result<Self::FuncOutput, Self::Error>;

    /// Defines a function filled with the given body.
    fn define_function_with_body<FN, L, I>(
        &self,
        name: &str,
        inputs: usize,
        outputs: usize,
        callees: impl IntoIterator<Item = String>,
        f: FN,
    ) -> Result<(), Self::Error>
    where
        FN: FnOnce(&Self::FuncOutput, &[Slot], &[Slot]) -> Result<I, Self::Error>,
        I: IntoIterator<Item = L>,
        L: LowerableStmt,
    {
        let func = self.define_function(name, inputs, outputs, callees)?;
        let inputs = func.lower_function_inputs(0..inputs);
        let outputs = func.lower_function_outputs(0..outputs);
        let stmts = f(&func, &inputs, &outputs)?;
        for stmt in stmts {
            stmt.lower(&func)?;
        }
        self.on_scope_end(func)
    }

    /// Defines the entrypoint function of the circuit.
    fn define_main_function(
        &self,
        advice_io: &AdviceIO,
        instance_io: &InstanceIO,
        callees: impl IntoIterator<Item = String>,
    ) -> Result<Self::FuncOutput, Self::Error>;

    /// Defines the entrypoint function of the circuit and fills it with the given body.
    fn define_main_function_with_body<L>(
        &self,
        advice_io: &AdviceIO,
        instance_io: &InstanceIO,
        callees: impl IntoIterator<Item = String>,
        stmts: impl IntoIterator<Item = L>,
    ) -> Result<(), Self::Error>
    where
        L: LowerableStmt + std::fmt::Debug,
    {
        let main = self.define_main_function(advice_io, instance_io, callees)?;
        log::debug!("Defined main function");
        for stmt in stmts {
            log::debug!("Lowering statement {stmt:?}");
            stmt.lower(&main)?;
        }
        log::debug!("Lowered function body");
        self.on_scope_end(main)
    }

    /// Callback called when a scope ends.
    fn on_scope_end(&self, _: Self::FuncOutput) -> Result<(), Self::Error> {
        Ok(())
    }

    /// Consumes the code generator and returns the final output.
    fn generate_output(self) -> Result<Self::Output, Self::Error>
    where
        Self::Output: 'c;
}

pub(crate) trait CodegenStrategy {
    fn codegen<'c: 'st, 's, 'st, C>(
        &self,
        codegen: &C,
        ctx: &IRCtx,
        ir: &ResolvedIRCircuit,
    ) -> Result<(), C::Error>
    where
        C: Codegen<'c, 'st>;
}

/// Trait defining generic code generation configuration parameters.
pub trait CodegenParams {
    /// Returns true if inlining is enabled.
    fn inlining_enabled(&self) -> bool;
}

impl<T: CodegenParams> CodegenParams for Rc<RefCell<T>> {
    fn inlining_enabled(&self) -> bool {
        self.borrow().inlining_enabled()
    }
}
