//! Integration of circuits with Haloumi.

pub mod config;
pub mod io;

use crate::circuit::config::AutoConfigure;

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
pub trait CircuitInitialization<L> {
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
