//! Driver for handling synthesis and lowering.

use ff::PrimeField;
use haloumi_core::{
    expressions::{EvaluableExpr, ExprBuilder, ExpressionInfo},
    info_traits::ConstraintSystemInfo,
};
use haloumi_ir_gen::circuit::resolved::ResolvedIRCircuit;
use haloumi_ir_gen::{IRGenParams, IRGenerationUser, circuit::unresolved::UnresolvedIRCircuit};
#[cfg(feature = "llzk-backend")]
use haloumi_llzk::{LlzkBackend, LlzkOutput, LlzkParams};
#[cfg(feature = "picus-backend")]
use haloumi_picus::{PicusBackend, PicusOutput, PicusParams};
use haloumi_synthesis::{CircuitSynthesis, SynthesisUser, SynthesizedCircuit};

/// Result type of a [`Driver`] action.
pub type Result<O> = std::result::Result<O, crate::error::Error>;

/// Controls the different lowering stages of circuits.
#[derive(Default, Debug)]
pub struct Driver {
    ir_gen: IRGenerationUser,
    synthesis: SynthesisUser,
}

impl Driver {
    /// Creates a new driver.
    pub fn new() -> Self {
        Self {
            ir_gen: Default::default(),
            synthesis: Default::default(),
        }
    }

    /// Synthesizes a circuit .
    pub fn synthesize<F, C>(
        &mut self,
        circuit: &C,
    ) -> Result<SynthesizedCircuit<F, <C::CS as ConstraintSystemInfo<F>>::Polynomial>>
    where
        C: CircuitSynthesis<F>,
        F: PrimeField,
    {
        Ok(self.synthesis.synthesize(circuit)?)
    }

    /// Generates the IR of the synthesized circuit.
    pub fn generate_ir<'syn, 'drv, 'cb, 'sco, F, E>(
        &'drv mut self,
        syn: &'syn SynthesizedCircuit<F, E>,
        params: IRGenParams<'cb, '_, F, E>,
    ) -> Result<UnresolvedIRCircuit<'drv, 'syn, 'sco, F, E>>
    where
        F: PrimeField + Ord,
        E: Clone + ExprBuilder<F> + ExpressionInfo + EvaluableExpr<F> + std::fmt::Debug,
        'syn: 'sco,
        'drv: 'sco + 'syn,
        'cb: 'sco + 'syn,
    {
        Ok(self.ir_gen.generate_ir(syn, params)?)
    }

    /// Creates a picus program from the circuit synthesis.
    #[cfg(feature = "picus-backend")]
    pub fn picus(&self, ir: &ResolvedIRCircuit, params: PicusParams) -> Result<PicusOutput> {
        Ok(PicusBackend::initialize(params).codegen(ir, ir.ctx())?)
    }

    /// Creates a llzk module from the circuit synthesis.
    #[cfg(feature = "llzk-backend")]
    pub fn llzk<'c>(
        &self,
        ir: &ResolvedIRCircuit,
        params: LlzkParams<'c>,
    ) -> Result<LlzkOutput<'c>> {
        Ok(LlzkBackend::initialize(params).codegen(ir, ir.ctx())?)
    }
}
