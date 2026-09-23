//! Types and traits related to circuits.

use std::{cell::RefCell, marker::PhantomData};

use configuration::Config;
use ff::{Field, PrimeField};
use haloumi_core::{
    circuit::{AbstractCircuitIO, ChipArgs, ExtraibleChip},
    expressions::{EvaluableExpr, ExpressionInfo},
    groups::RegionsGroupHooks,
    info_traits::ConstraintSystemInfo,
    io::table::InputDescr,
    layouter::{LayoutAdaptor, Layouter},
    query::Fixed,
    table::{CellReprSize, Column, RegionIndex},
    types::Types,
};

use haloumi_extractor_core::io::{
    ctx::{input::ICtx, output::OCtx},
    load::LoadFromCells,
    store::StoreIntoCells,
};
use haloumi_ir::{inject::InjectedIR, stmt::IRStmt};
use haloumi_ir_gen::expressions::ExpressionInRow;
use haloumi_synthesis::{
    CircuitSynthesis,
    error::Error as SynError,
    io::{AdviceIO, CircuitIO, InstanceIO},
    synthesizer::Synthesizer,
};

use crate::{circuit::layouter::ExtractionLayouter, extractor::InjectedIRPolicy};

mod configuration;
mod layouter;

/// Main trait for defining harness that return a value.
///
/// The actual logic of the circuit is defined in an implementation of this trait with the circuit
/// implementation struct acting as scaffolding and glue.
///
/// For harnesses that return `()` see [`AbstractUnitCircuit`].
pub trait AbstractCircuit<F: PrimeField>: AbstractCircuitIO {
    /// Error type.
    type Error;
    /// Expression type.
    type Expression;
    /// Cell type used by the circuit implementation.
    type Cell;
    /// Region index type.
    type RegionIndex;

    /// Runs the circuit's main logic.
    fn synthesize<L>(
        &self,
        chip: &Self::Chip,
        layouter: &mut LayoutAdaptor<L>,
        input: Self::Input,
        injected_ir: &mut InjectedIR<Self::RegionIndex, Self::Expression>,
    ) -> Result<Self::Output, Self::Error>
    where
        L: Layouter<F, Self::Error> + RegionsGroupHooks<F, Self::Cell, Error = Self::Error>;
}

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
pub struct CircuitImpl<'a, F, C, CS, T, M>
where
    F: Field,
    CS: ConstraintSystemInfo<F, Polynomial = T::Expression>,
    T: Types<F>,
{
    abstract_circuit: C,
    constants: &'a [String],
    injected_ir_policy: InjectedIRPolicy,
    injected_ir: RefCell<InjectedIR<T::RegionIndex, CS::Polynomial>>,
    _marker: PhantomData<(M, CS, T)>,
}

impl<'a, F, C, CS, M, T, E> CircuitImpl<'a, F, C, CS, T, M>
where
    F: PrimeField,
    CS: ConstraintSystemInfo<F, Polynomial = E>,
    T: Types<F, Expression = E> + std::fmt::Debug,
    E: Clone + ExpressionInfo + EvaluableExpr<F>,
{
    /// Creates a circuit scaffold with the extraction settings supplied by its harness.
    pub(crate) fn new(
        abstract_circuit: C,
        constants: &'a [String],
        injected_ir_policy: InjectedIRPolicy,
    ) -> Self {
        Self {
            abstract_circuit,
            constants,
            injected_ir_policy,
            injected_ir: Default::default(),
            _marker: PhantomData,
        }
    }

    /// Consumes the circuit wrapper and returns the extra IR added during synthesis.
    pub fn take_injected_ir<'ir>(
        self,
        sorted: bool,
    ) -> Vec<(RegionIndex, IRStmt<ExpressionInRow<'ir, CS::Polynomial, F>>)> {
        let mut ir = self
            .injected_ir
            .into_inner()
            .into_iter()
            .map(|(idx, ir)| {
                (
                    (*idx).into(),
                    IRStmt::<ExpressionInRow<_, F>>::seq(
                        ir.into_iter()
                            .map(|s| s.map(&mut |(row, e)| ExpressionInRow::new(row, e))),
                    )
                    .into(),
                )
            })
            .collect::<Vec<(RegionIndex, IRStmt<_>)>>();
        if sorted {
            ir.sort_by(|&(lhs, _), &(rhs, _)| (*lhs).cmp(&*rhs));
        }
        ir
    }

    fn create_chip<'l, L: 'l>(&self, config: &Config<C>) -> C::Chip
    where
        C: AbstractCircuitIO + ChipArgs,
        C::Chip: ExtraibleChip<
                LayoutAdaptor<'l, L>,
                Args = C::Args,
                Config = C::Config,
                ConfigCols = C::ConfigCols,
            >,
    {
        C::Chip::new_chip(&config.chip.inner, self.abstract_circuit.chip_args())
    }

    fn load_chip<'l, L: 'l>(
        &self,
        layouter: &mut LayoutAdaptor<'l, L>,
        chip: &C::Chip,
        config: &Config<C>,
    ) -> Result<(), T::Error>
    where
        C: AbstractCircuitIO + ChipArgs,
        C::Chip: ExtraibleChip<
                LayoutAdaptor<'l, L>,
                Args = C::Args,
                Config = C::Config,
                ConfigCols = C::ConfigCols,
                Error = T::Error,
            >,
    {
        chip.load_chip(layouter, &config.chip.inner)
    }

    fn load<'l, 's, Load, L>(
        &self,
        cells: impl IntoIterator<Item = InputDescr<F, T>>,
        n_cells: usize,
        cell_type: &'static str,
        chip: &C::Chip,
        layouter: &mut LayoutAdaptor<'l, L>,
        do_ir_injection: bool,
    ) -> Result<Load, T::Error>
    where
        Load: LoadFromCells<F, C::Chip, T>,
        C: AbstractCircuitIO + ChipArgs,
        //C::Chip: ExtraibleChip<LayoutAdaptor<'l, L>, Args = C::Args, Error = T::Error>,
        L: Layouter<F, T::Error> + 's,
        T: Types<F>,
    {
        let mut injected_ir = self.injected_ir.borrow_mut();
        let mut dummy_injected_ir = InjectedIR::default();
        Load::load(
            &mut ICtx::new(
                cells
                    .into_iter()
                    .enumerate()
                    .inspect(|(idx, i)| {
                        log::debug!("{cell_type} cell {}/{n_cells}: {i:?}", idx + 1)
                    })
                    .map(|(_, i)| i),
                self.constants,
            ),
            chip,
            layouter,
            if do_ir_injection {
                &mut injected_ir
            } else {
                &mut dummy_injected_ir
            },
        )
    }

    fn load_inputs<'l, 's, L>(
        &self,
        config: &Config<C>,
        chip: &C::Chip,
        layouter: &mut LayoutAdaptor<'l, L>,
    ) -> Result<C::Input, T::Error>
    where
        C::Input: LoadFromCells<F, C::Chip, T>,
        C: AbstractCircuitIO + ChipArgs,
        //C::Chip: ExtraibleChip<LayoutAdaptor<'l, L>, Args = C::Args, Error = T::Error>,
        L: Layouter<F, T::Error> + 's,
    {
        let inputs = config.inputs();
        let n_inputs = inputs.len();
        self.load(inputs, n_inputs, "Input", chip, layouter, true)
    }

    fn store_outputs<'l, 's, L>(
        &self,
        output: C::Output,
        config: &Config<C>,
        chip: &C::Chip,
        layouter: &mut LayoutAdaptor<L>,
    ) -> Result<(), T::Error>
    where
        C::Output: StoreIntoCells<F, C::Chip, T>,
        C: AbstractCircuitIO + ChipArgs,
        //C::Chip: ExtraibleChip<LayoutAdaptor<'l, L>, Args = C::Args, Error = T::Error>,
        L: Layouter<F, T::Error> + 's,
    {
        let outputs = config.outputs();
        // Store the results
        let n_outputs = outputs.len();
        let mut injected_ir = self.injected_ir.borrow_mut();
        let mut dummy_injected_ir = InjectedIR::default();
        output.store(
            &mut OCtx::new(
                outputs
                    .into_iter()
                    .enumerate()
                    .inspect(|(idx, o)| log::debug!("Output cell {}/{}: {o:?}", idx + 1, n_outputs))
                    .map(|(_, o)| o),
            ),
            chip,
            layouter,
            match self.injected_ir_policy {
                InjectedIRPolicy::AllowAll => &mut injected_ir,
                InjectedIRPolicy::DisallowForOutputs => &mut dummy_injected_ir,
            },
        )?;
        Ok(())
    }
}

impl<'s, F, C, CS, I, O, T, E> CircuitSynthesis<'s, F> for CircuitImpl<'_, F, C, CS, T, Function>
where
    T: Types<F, Expression = E> + std::fmt::Debug,
    F: PrimeField,
    CS: ConstraintSystemInfo<F, Polynomial = E> + std::default::Default + 'static,
    CS::InstanceCol: Into<Column<haloumi_core::query::Instance>>,
    CS::AdviceCol: Into<Column<haloumi_core::query::Advice>>,
    CS::FixedCol: Into<Column<Fixed>>,
    C: AbstractCircuit<
            F,
            Input = I,
            Output = O,
            Error = T::Error,
            Cell = T::Cell,
            Expression = E,
            RegionIndex = T::RegionIndex,
        > + ChipArgs,
    I: CellReprSize + LoadFromCells<F, C::Chip, T>,
    O: CellReprSize + StoreIntoCells<F, C::Chip, T>,
    C::Chip: for<'l> ExtraibleChip<
            LayoutAdaptor<'l, ExtractionLayouter<'s, F, T::Error>>,
            Args = C::Args,
            Config = C::Config,
            ConfigCols = C::ConfigCols,
            CS = CS,
            Error = T::Error,
        >,
    C::ConfigCols: haloumi_core::auto_conf::AutoConfigure<CS>,
    E: Clone + ExpressionInfo + EvaluableExpr<F>,
    ExtractionLayouter<'s, F, T::Error>: RegionsGroupHooks<F, C::Cell, Error = T::Error>,
{
    type Circuit = Self;
    type Config = Config<C>;
    type CS = CS;
    type Error = T::Error;

    fn circuit(&self) -> &Self::Circuit {
        self
    }

    fn configure(cs: &mut Self::CS) -> Self::Config {
        Self::Config::configure::<LayoutAdaptor<'_, ExtractionLayouter<'s, F, T::Error>>, F, CS>(cs)
    }

    fn advice_io(_: &Self::Config) -> Result<AdviceIO, SynError> {
        Ok(CircuitIO::empty())
    }

    fn instance_io(config: &Self::Config) -> Result<InstanceIO, SynError> {
        let inputs: Vec<_> = (0..I::SIZE).collect();
        let outputs: Vec<_> = (0..O::SIZE).collect();

        CircuitIO::new(
            &[(config.input_instance(), &inputs)],
            &[(config.output_instance(), &outputs)],
        )
    }

    fn synthesize(
        circuit: &Self::Circuit,
        config: Self::Config,
        synthesizer: &'s mut Synthesizer<F>,
        cs: &Self::CS,
    ) -> Result<(), Self::Error> {
        let mut layouter = ExtractionLayouter::new(synthesizer, cs.constants());
        let mut adaptor = LayoutAdaptor(&mut layouter);
        // Create and load chip.
        let chip = circuit.create_chip(&config);
        let input = circuit.load_inputs(&config, &chip, &mut adaptor)?;
        let output = {
            let mut injected_ir = circuit.injected_ir.borrow_mut();
            // Call the inner circuit

            circuit
                .abstract_circuit
                .synthesize(&chip, &mut adaptor, input, &mut injected_ir)
        }?;

        circuit.store_outputs(output, &config, &chip, &mut adaptor)?;

        circuit.load_chip(&mut adaptor, &chip, &config)?;

        Ok(())
    }
}
