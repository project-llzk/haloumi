//! Integration of circuits with Haloumi.

pub mod config;
pub mod io;

use ff::PrimeField;
use haloumi_core::{
    groups::RegionsGroupHooks,
    layouter::{LayoutAdaptor, Layouter},
    table::RegionIndex,
};
use haloumi_ir::inject::InjectedIR;

use crate::circuit::{
    config::AutoConfigure,
    io::{CellReprSize, ctx::InputDescr},
};

/// Trait for configuring the arguments of a chip.
///
/// If the chip has no arguments the type should be `()`. In that case the type
/// can implement [`NoChipArgs`] which will automatically implement this trait
/// with that type.
pub trait ChipArgs {
    /// Type of the arguments taken by the chip.
    type Args: Default;

    /// Returns an instance of the arguments.
    fn chip_args(&self) -> Self::Args {
        Default::default()
    }
}

/// Trait for configuring [`ChipArgs`] for types that don't have arguments.
///
/// Sets the type of the arguments to `()`.
pub trait NoChipArgs {}

impl<T> ChipArgs for T
where
    T: NoChipArgs,
{
    type Args = ();
}

/// Adaptor trait for integrating chips with the extractor.
pub trait ExtraibleChip<L> {
    /// Configuration of the circuit.
    type Config: Clone + std::fmt::Debug;
    /// Arguments required by the circuit.
    type Args: Default;
    /// Configuration columns of the circuit.
    type ConfigCols: Clone + std::fmt::Debug + AutoConfigure<Self::CS>;
    /// Constrait system.
    type CS;
    /// Error type.
    type Error;

    /// Creates a new instance of the chip.
    fn new_chip(config: &Self::Config, args: Self::Args) -> Self;

    /// Creates an instance of the chip's configuration.
    fn configure_circuit(meta: &mut Self::CS, columns: &Self::ConfigCols) -> Self::Config;

    /// Loads internal information of the chip.
    fn load_chip(&self, layouter: &mut L, config: &Self::Config) -> Result<(), Self::Error>;
}

/// Super trait for extracting IO from an abstract circuit.
pub trait AbstractCircuitIO {
    /// Type that implements the main logic.
    type Chip;
    /// Input type of the chip.
    type Input: CellReprSize;
    /// Output type of the chip.
    type Output: CellReprSize;
    /// Configuration of the circuit.
    type Config: Clone + std::fmt::Debug;
    /// Configuration columns of the circuit.
    type ConfigCols: Clone + std::fmt::Debug;
}

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

///// Main trait for defining harness that return a value.
/////
///// This trait is analogous to [`AbstractCircuit`] but accepts a mutable reference to the chip
///// instead.
/////
///// The actual logic of the circuit is defined in an implementation of this trait with the circuit
///// implementation struct acting as scaffolding and glue.
/////
///// For harnesses that return `()` see [`AbstractUnitCircuit`].
//pub trait AbstractCircuitMut<F: PrimeField>: AbstractCircuitIO {
//    fn synthesize_mut<L>(
//        &self,
//        chip: &mut Self::Chip,
//        layouter: &mut L,
//        input: Self::Input,
//        injected_ir: &mut InjectedIR<RegionIndex, Expression<F>>,
//    ) -> Result<Self::Output, Error>
//    where
//        L: Layouter<F>;
//}

///// Main trait for defining harness that do not return a value.
/////
///// When defining the harness both inputs and outputs are passed as arguments. The distinction
///// between inputs and outputs is meant for the lowering backend. When lowering to Picus the
///// outputs must be the arguments of the function under test that are, conceptually, a function of
///// the inputs.
/////
///// The actual logic of the circuit is defined in an implementation of this trait with the circuit
///// implementation struct acting as scaffolding and glue.
/////
///// For harnesses that return a value see [`AbstractCircuit`].
//pub trait AbstractUnitCircuit<F: PrimeField>: AbstractCircuitIO {
//    fn synthesize<L>(
//        &self,
//        chip: &Self::Chip,
//        layouter: &mut L,
//        input: Self::Input,
//        output: Self::Output,
//        injected_ir: &mut InjectedIR<RegionIndex, Expression<F>>,
//    ) -> Result<(), Error>
//    where
//        L: Layouter<F>;
//}

///// Trait for obtaining information about the configuration of a circuit.
//pub trait AbstractCircuitConfig {
//    /// Returns the list of [`InputDescr`] that make up the inputs.
//    fn inputs<F: PrimeField>(&self) -> Vec<InputDescr<F, ExtractionSupport>>;
//
//    /// Returns the column that represents the inputs.
//    fn input_instance(&self) -> Column<Instance>;
//
//    /// Returns the list of [`OutputDescr`] that make up the outputs.
//    fn outputs<F: PrimeField>(&self) -> Vec<OutputDescr<F, ExtractionSupport>>;
//
//    /// Returns the column that represents the outputs.
//    fn output_instance(&self) -> Column<Instance>;
//}
