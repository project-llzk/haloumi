//! Types for working with the circuit extractor.

use ff::PrimeField;
use haloumi_core::{
    circuit::{AbstractCircuitIO, ChipArgs},
    expressions::{EvaluableExpr, ExprBuilder, ExpressionInfo},
    info_traits::ConstraintSystemInfo,
    types::Types,
};
use haloumi_driver::driver::Driver;

use haloumi_ir_gen::{
    IRGenParams, circuit::resolved::ResolvedIRCircuit, gates::callbacks::SimpleGateCallbacks,
    lookups::callbacks::LookupCallbacks,
};
use haloumi_synthesis::CircuitSynthesis;

use crate::{circuit::CircuitImpl, error::Error};

/// Possible values for the `debug_comments` configuration.
#[derive(PartialEq, Eq, Default, Copy, Clone, Debug)]
pub enum Comments {
    /// Generate debug comments.
    Debug,
    /// Generate no comments.
    #[default]
    None,
}

/// IR injection policy.
#[derive(PartialEq, Eq, Default, Copy, Clone, Debug)]
pub enum InjectedIRPolicy {
    /// Emits injected IR for all parts of the final circuit.
    AllowAll,
    /// Forbids emitting injected IR on the circuit outputs.
    #[default]
    DisallowForOutputs,
}

/// Configuration for an extractor.
#[derive(Debug)]
pub struct ExtractorCfg {
    constants: Vec<String>,
    debug_comments: Comments,
    injected_ir: InjectedIRPolicy,
    //gate_callbacks: SimpleGateCallbacks<F, E>,
}

impl ExtractorCfg {
    /// Creates a new default Configuration
    pub fn new() -> Self {
        Self {
            constants: Default::default(),
            debug_comments: Default::default(),
            injected_ir: Default::default(),
            //gate_callbacks: Default::default(),
        }
    }

    /// Returns the list of constants.
    pub fn constants(&self) -> &[String] {
        &self.constants
    }

    /// Sets the list of constants.
    pub fn set_constants(&mut self, constants: Vec<String>) {
        self.constants = constants;
    }

    /// Returns a mutable reference to the list of constants.
    pub fn constants_mut(&mut self) -> &mut Vec<String> {
        &mut self.constants
    }

    /// Returns the configuration regarding debug comments.
    pub fn debug_comments(&self) -> &Comments {
        &self.debug_comments
    }

    /// Sets the configuration regarding debug comments.
    pub fn set_debug_comments(&mut self, debug_comments: Comments) {
        self.debug_comments = debug_comments;
    }

    /// Returns the configuration regarding IR injection.
    pub fn injected_ir(&self) -> &InjectedIRPolicy {
        &self.injected_ir
    }

    /// Sets the configuration regarding IR injection.
    pub fn set_injected_ir(&mut self, injected_ir: InjectedIRPolicy) {
        self.injected_ir = injected_ir;
    }

    ///// Returns the gate callbacks list.
    //pub fn gate_callbacks(&self) -> &SimpleGateCallbacks<F, E> {
    //    &self.gate_callbacks
    //}
    //
    ///// Returns a mutable reference to the callbacks list.
    //pub fn gate_callbacks_mut(&mut self) -> &mut SimpleGateCallbacks<F, E> {
    //    &mut self.gate_callbacks
    //}
}

impl Default for ExtractorCfg {
    fn default() -> Self {
        Self::new()
    }
}

/// Extractor of circuits into resolved IR.
#[derive(Debug)]
pub struct Extractor<'cfg> {
    cfg: &'cfg ExtractorCfg,
    /// Used for generating the output of tests.
    sort_injected_ir: bool,
}

impl<'cfg> Extractor<'cfg> {
    /// Creates a new extractor.
    pub fn new(cfg: &'cfg ExtractorCfg) -> Self {
        Self {
            cfg,
            sort_injected_ir: false,
        }
    }

    /// Makes the extractor sort the injected IR.
    pub fn with_sort_injected_ir(mut self) -> Self {
        self.sort_injected_ir = true;
        self
    }

    /// Creates a new concrete circuit based on the given abstract circuit.
    pub fn make_circuit<F, C, M, T, CS>(
        &self,
        abstract_circuit: C,
    ) -> CircuitImpl<'_, F, C, CS, T, M>
    where
        F: PrimeField,
        CS: ConstraintSystemInfo<F, Polynomial = T::Expression> + Default + 'static,
        T: std::fmt::Debug + Types<F>,
        <CS as ConstraintSystemInfo<F>>::Polynomial:
            std::fmt::Debug + EvaluableExpr<F> + Clone + ExpressionInfo + ExprBuilder<F>,
    {
        CircuitImpl::new(abstract_circuit, self.cfg.constants(), self.cfg.injected_ir)
    }

    /// Extracts the circuit to IR using the driver.
    pub fn extract_circuit<'c, F, C, M, T, CS>(
        &self,
        circuit: CircuitImpl<'c, F, C, CS, T, M>,
        lookups: Option<&dyn LookupCallbacks<F, CS::Polynomial>>,
    ) -> Result<ResolvedIRCircuit, Error>
    where
        F: PrimeField + Ord,
        C: AbstractCircuitIO + ChipArgs,
        T: Types<F> + std::fmt::Debug,
        CircuitImpl<'c, F, C, CS, T, M>: for<'a> CircuitSynthesis<'a, F, CS = CS>,
        CS: ConstraintSystemInfo<F, Polynomial = T::Expression> + Default + 'static,
        <CS as ConstraintSystemInfo<F>>::Polynomial:
            std::fmt::Debug + EvaluableExpr<F> + Clone + ExpressionInfo + ExprBuilder<F>,
    {
        let mut driver = Driver::default();
        let syn = driver.synthesize(&circuit)?;
        log::info!("Synthesis completed");
        let ir_params = self.prepare_ir_gen_params(lookups);
        let mut unresolved = driver.generate_ir(&syn, ir_params)?;
        unresolved.validate()?;

        log::info!("Generated unresolved IR");
        let injected = circuit.take_injected_ir(self.sort_injected_ir);
        unresolved.inject_ir(injected, &syn)?;
        log::info!("Injected additional IR");
        let resolved = unresolved.resolve()?;

        resolved.validate()?;
        Ok(resolved)
    }

    fn prepare_ir_gen_params<'lc, F, E>(
        &self,
        lookups: Option<&'lc dyn LookupCallbacks<F, E>>,
    ) -> IRGenParams<'lc, '_, F, E>
    where
        F: ff::Field,
    {
        let mut ir_params = IRGenParams::new();
        //ir_params.gate_callbacks(self.cfg.gate_callbacks());
        if matches!(self.cfg.debug_comments, Comments::Debug) {
            ir_params.with_debug_comments();
        }
        if let Some(lookups) = lookups {
            ir_params.lookup_callbacks(lookups);
        }
        ir_params
    }
}
