//! Integration of circuits with Haloumi.

pub mod config;

/// Implements [`AdviceCopy`] for an assigned cell type.
#[macro_export]
macro_rules! __impl_advice_copy_for_assigned_cell {
    ($($assigned_cell:ident)::+, $field:path, $types:ty, $($region:ident)::+, $advice_col:ty, $error:ty, $($rational:ident)::+) => {
        impl<F: $field, V: Clone> $crate::core::query::AdviceCopy<V, F, $types> for $($assigned_cell)::+<V, F>
        where
            for<'v> $($rational)::+<F>: From<&'v V>,
        {
            fn copy_advice_helper(
                &self,
                region: &mut $($region)::+<'_, F>,
                advice_col: $advice_col,
                advice_row: usize,
            ) -> Result<Self, $error> {
                self.copy_advice(|| "", region, advice_col, advice_row)
            }
        }
    };
}

//pub mod io;

///// Main trait for defining harness that return a value.
/////
///// The actual logic of the circuit is defined in an implementation of this trait with the circuit
///// implementation struct acting as scaffolding and glue.
/////
///// For harnesses that return `()` see [`AbstractUnitCircuit`].
//pub trait AbstractCircuit<F: PrimeField>: AbstractCircuitIO {
//    /// Error type.
//    type Error;
//    /// Expression type.
//    type Expression;
//    /// Cell type used by the circuit implementation.
//    type Cell;
//    /// Region index type.
//    type RegionIndex;
//
//    /// Runs the circuit's main logic.
//    fn synthesize<L>(
//        &self,
//        chip: &Self::Chip,
//        layouter: &mut LayoutAdaptor<L>,
//        input: Self::Input,
//        injected_ir: &mut InjectedIR<Self::RegionIndex, Self::Expression>,
//    ) -> Result<Self::Output, Self::Error>
//    where
//        L: Layouter<F, Self::Error> + RegionsGroupHooks<F, Self::Cell, Error = Self::Error>;
//}

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
