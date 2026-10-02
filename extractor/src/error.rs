//! Error type.

/// Error type.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Forwarded integration error.
    #[error(transparent)]
    Integration(#[from] haloumi_core::error::Error),
    /// IR generation error.
    #[error(transparent)]
    IrGen(#[from] haloumi_ir_gen::error::Error),
    /// Driver error.
    #[error(transparent)]
    Driver(#[from] haloumi_driver::error::Error),
    /// IO error.
    #[error(transparent)]
    Io(#[from] std::io::Error),
}
