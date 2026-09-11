//! Types and traits related to circuits.

use std::{cell::RefCell, marker::PhantomData};

use ff::{Field, PrimeField};
use haloumi_core::{info_traits::ConstraintSystemInfo, table::RegionIndex};
use haloumi_driver::ir::{inject::InjectedIR, stmt::IRStmt};
use haloumi_integration::circuit::{AbstractCircuit, ChipArgs};
use haloumi_ir_gen::expressions::ExpressionInRow;
use haloumi_synthesis::{
    CircuitSynthesis,
    error::Error as SynError,
    io::{AdviceIO, InstanceIO},
    synthesizer::Synthesizer,
};

use crate::error::Error;

mod configuration;

/// Marker for function harnesses.
#[derive(Debug)]
pub struct Function;
/// Marker for procedure harnesses.
#[derive(Debug)]
pub struct Procedure;
/// Marker for mut function harnesses.
#[derive(Debug)]
pub struct FunctionMut;

/// Scaffold for implementations of [`AbstractCircuit`].
///
/// The circuit has two modes; function or procedure. The mode is configured by passing either
/// [`Function`] or [`Procedure`] to the `M` type parameter. By default is set to [`Function`].
#[derive(Debug)]
pub struct CircuitImpl<'a, F, C, CS, M = Function>
where
    F: Field,
    CS: ConstraintSystemInfo<F>,
{
    abstract_circuit: C,
    constants: &'a [String],
    allow_injected_ir_for_outputs: bool,
    injected_ir: RefCell<InjectedIR<RegionIndex, CS::Polynomial>>,
    _marker: PhantomData<(M, CS)>,
}

impl<F, C, CS, M> CircuitImpl<'_, F, C, CS, M>
where
    F: Field,
    CS: ConstraintSystemInfo<F>,
{
    /// Consumes the circuit wrapper and returns the extra IR added during synthesis.
    pub fn take_injected_ir<'ir>(
        self,
    ) -> Vec<(RegionIndex, IRStmt<ExpressionInRow<'ir, CS::Polynomial, F>>)> {
        self.injected_ir
            .into_inner()
            .into_iter()
            .map(|(idx, ir)| {
                (
                    idx,
                    IRStmt::<ExpressionInRow<_, F>>::seq(
                        ir.into_iter()
                            .map(|s| s.map(&mut |(row, e)| ExpressionInRow::new(row, e))),
                    )
                    .into(),
                )
            })
            .collect()
    }
}

impl<F, C, CS> CircuitSynthesis<F> for CircuitImpl<'_, F, C, CS, Function>
where
    F: PrimeField,
    CS: ConstraintSystemInfo<F> + std::default::Default + 'static,
    C: AbstractCircuit<F> + ChipArgs,
    //C::Chip: for<'a, 'b> CircuitInitialization<
    //        ExtractionLayouter<'a, 'b, F>,
    //        Args = C::Args,
    //        Config = C::Config,
    //        ConfigCols = C::ConfigCols,
    //        CS = ConstraintSystem<F>,
    //        Error = Error,
    //    >,
    //C::ConfigCols: AutoConfigure<ConstraintSystem<F>>,
    //C::Input:
    //    for<'a, 'b> LoadFromCells<F, C::Chip, ExtractionSupport, ExtractionLayouter<'a, 'b, F>>,
    //C::Output:
    //    for<'a, 'b> StoreIntoCells<F, C::Chip, ExtractionSupport, ExtractionLayouter<'a, 'b, F>>,
{
    type Circuit = Self;
    type Config = Config<C>;
    type CS = CS;
    type Error = Error;

    fn circuit(&self) -> &Self::Circuit {
        self
    }

    fn configure(cs: &mut Self::CS) -> Self::Config {
        Self::Config::configure(cs)
    }

    fn advice_io(_: &Self::Config) -> Result<AdviceIO, SynError> {
        //Ok(CircuitIO::empty())
        todo!()
    }

    fn instance_io(config: &Self::Config) -> Result<InstanceIO, SynError> {
        todo!()
        //let inputs: Vec<_> = (0..C::Input::SIZE).collect();
        //let outputs: Vec<_> = (0..C::Output::SIZE).collect();
        //
        //CircuitIO::new(
        //    &[(config.input_instance(), &inputs)],
        //    &[(config.output_instance(), &outputs)],
        //)
    }

    fn synthesize(
        circuit: &Self::Circuit,
        config: Self::Config,
        synthesizer: &mut Synthesizer<F>,
        cs: &Self::CS,
    ) -> Result<(), Self::Error> {
        todo!()
        //let layouter = ExtractionLayouter::new(synthesizer, cs.constants());
        //circuit.synthesize_inner(config, layouter)
    }
}
