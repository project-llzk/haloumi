#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use ff::PrimeField;
use haloumi_core::{
    expressions::{EvaluableExpr, ExprBuilder, ExpressionInfo},
    info_traits::ConstraintSystemInfo,
};
use haloumi_driver::driver::Driver;
use haloumi_integration::{
    Types,
    circuit::{AbstractCircuitIO, ChipArgs},
};
use haloumi_ir_gen::{
    IRGenParams, circuit::resolved::ResolvedIRCircuit, lookups::callbacks::LookupCallbacks,
};
use haloumi_synthesis::CircuitSynthesis;

use crate::{circuit::CircuitImpl, error::Error};

pub mod circuit;
pub mod error;

/// Re-export of the inventory crate.
pub mod inventory {
    pub use ::inventory::*;
}
/// Re-export of the anyhow crate.
pub mod anyhow {
    pub use ::anyhow::*;
}

/// Output produced by a harness function.
pub type Output = ResolvedIRCircuit;

/// Type representing the harness logic.
pub type HarnessFn = fn(&Extractor) -> anyhow::Result<Output>;

/// Entry in the harness table.
#[derive(Copy, Clone, Debug)]
pub struct Harness(&'static str, HarnessFn);

impl Harness {
    /// Creates a new entry
    pub const fn new(name: &'static str, harness: HarnessFn) -> Self {
        Self(name, harness)
    }

    /// Returns the name of the entry.
    pub fn name(&self) -> &'static str {
        self.0
    }

    /// Returns the harness function.
    pub fn harness(&self) -> HarnessFn {
        self.1
    }
}

::inventory::collect!(Harness);

/// Registers a harness in the registry.
#[macro_export]
macro_rules! register_harness {
    ($name:literal, $harness:path) => {
        $crate::inventory::submit!($crate::Harness::new($name, $harness));
    };
}

/// Information required for executing a harness.
#[derive(Debug)]
pub struct Extractor<'s> {
    constants: &'s [String],
    debug_comments: bool,
    disable_decomposition_pattern: bool,
    allow_injected_ir_for_outputs: bool,
    /// Used for generating the output of tests.
    sort_injected_ir: bool,
}

impl<'s> Extractor<'s> {
    /// Creates a new extractor.
    pub fn new(
        constants: &'s [String],
        debug_comments: bool,
        disable_decomposition_pattern: bool,
        allow_injected_ir_for_outputs: bool,
    ) -> Self {
        Self {
            constants,
            debug_comments,
            disable_decomposition_pattern,
            allow_injected_ir_for_outputs,
            sort_injected_ir: false,
        }
    }

    /// Makes the extractor sort the injected IR.
    pub fn with_sort_injected_ir(mut self) -> Self {
        self.sort_injected_ir = true;
        self
    }

    /// Extracts the circuit to IR using the driver.
    pub fn extract_circuit<'c, F, C, M, T, E, CS>(
        &self,
        circuit: CircuitImpl<'c, F, C, CS, T, M>,
        lookups: Option<&dyn LookupCallbacks<F, CS::Polynomial>>,
    ) -> Result<ResolvedIRCircuit, Error>
    where
        F: PrimeField + Ord,
        C: AbstractCircuitIO + ChipArgs,
        T: Types<F, Expression = E> + std::fmt::Debug,
        CircuitImpl<'c, F, C, CS, T, M>: for<'a> CircuitSynthesis<'a, F, CS = CS>,
        CS: ConstraintSystemInfo<F, Polynomial = T::Expression> + Default + 'static,
        <CS as ConstraintSystemInfo<F>>::Polynomial: std::fmt::Debug,
        E: EvaluableExpr<F> + Clone + ExpressionInfo + ExprBuilder<F>,
    {
        let mut driver = Driver::default();
        let syn = driver.synthesize(&circuit)?; //.context("Synthesis failed")?;
        log::info!("Synthesis completed");
        //std::fs::write("synthesized_circuit.txt", format!("{syn:#?}"))?;

        let mut ir_params = IRGenParams::new();

        //let patterns = Patterns {
        //    decompose_core: !self.disable_decomposition_pattern,
        //};
        //ir_params = ir_params.gate_callbacks(&patterns);
        if self.debug_comments {
            ir_params = ir_params.with_debug_comments();
        }
        if let Some(lookups) = lookups {
            ir_params = ir_params.lookup_callbacks(lookups);
        }

        let mut unresolved = driver.generate_ir(&syn, ir_params)?;
        //.context("IR generation failed")?;
        unresolved.validate()?;
        //if let Err(err) = status {
        //    log::error!("{err}");
        //
        //    anyhow::bail!("Failed due to validation errors on unresolved IR");
        //}

        log::info!("Generated unresolved IR");
        let injected = circuit.take_injected_ir(self.sort_injected_ir);
        unresolved.inject_ir(injected, &syn)?;
        //.context("IR injection failed")?;
        log::info!("Injected additional IR");
        let resolved = unresolved.resolve()?; //.context("IR resolution failed")?;

        //std::fs::write("driver_state.txt", format!("{driver:#?}"))?;
        resolved.validate()?;
        //if let Err(err) = status {
        //    log::error!("{err}");
        //    anyhow::bail!("Failed due to validation errors on resolved IR");
        //}
        Ok(resolved)
    }

    /// Returns the constants supplied to the extractor.
    pub fn constants(&self) -> &[String] {
        self.constants
    }

    /// Returns whether IR injection is enabled while loading outputs.
    pub fn allow_injected_ir_for_outputs(&self) -> bool {
        self.allow_injected_ir_for_outputs
    }
}

/// Entry-point for the extractor tool.
#[derive(Debug)]
pub struct ExtractorMain {}

impl ExtractorMain {
    /// Runs the extraction logic.
    pub fn run(harnesses: impl Iterator<Item = &'static Harness>) {
        let extractor = Extractor::new(&[], false, false, false);
        for harness in harnesses {
            println!("{}", harness.name());
            let _ = (harness.harness())(&extractor);
        }
    }
}
