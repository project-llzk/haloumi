//! Error type.

use crate::main_impl::app_error::AppError;

/// Error type.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Forwarded integration error.
    #[error(transparent)]
    Integration(#[from] haloumi_integration::error::Error),
    /// IR generation error.
    #[error(transparent)]
    IrGen(#[from] haloumi_ir_gen::error::Error),
    /// Driver error.
    #[error(transparent)]
    Driver(#[from] haloumi_driver::error::Error),
    /// Logging configuration error.
    #[error(transparent)]
    Logging(#[from] log::SetLoggerError),
    /// IO error.
    #[error(transparent)]
    Io(#[from] std::io::Error),
    /// Raised when both parameters are passed at the same time.
    #[error("Cannot set --constants and --constants-file at the same time")]
    ConstantsConfigErr,
    /// Extraction failed with some errors.
    #[error("Extraction failed with {0} errors")]
    FailedExtraction(usize),
    /// Raised when the tool didn't extract any circuits.
    #[error("No circuits were generated!")]
    EmptyExtraction,
    /// Raised when the configured output path is not a directory.
    #[error("Output path {0} must be a directory")]
    OutputNotDir(String),
    /// Main entrypoint error.
    #[error(transparent)]
    App(#[from] AppError),
    /// Raised when an optimization pass fails.
    #[error("{0} pass failed")]
    Opt(&'static str),
    /// Raised when LLZK output is emitted but the field name was not passed.
    #[error("Pass the --llzk-field-name=<name> parameter when emitting LLZK IR")]
    RequiredLlzkFieldName,
}
