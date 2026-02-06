//! Error types.

use std::sync::Arc;

use haloumi_core::slot::output::OutputId as FieldId;
use llzk::prelude::Type;
use thiserror::Error;

/// General error type.
#[derive(Debug, Error)]
pub enum Error {
    /// Raised when an output is missing.
    #[error("Struct is missing output #{0}")]
    MissingOutput(FieldId),
    /// Raised if the constrain function is missing.
    #[error("Constrain function is missing!")]
    MissingConstrainFunc,
    /// Raised if the constrain function does not have blocks.
    #[error("Constrain function region is missing a block")]
    MissingBlock,
    /// Raised if the constain function does not have a terminator op.
    #[error("Constrain function is missing a terminator")]
    MissingTerminator,
    /// Raised if a LLZK error occurs.
    #[error("LLZK error: {0}")]
    Llzk(#[from] llzk::error::Error),
    /// Raised if a MLIR error occurs.
    #[error("MLIR error: {0}")]
    Mlir(#[from] melior::Error),
    /// Raised if a lowering error occurs.
    #[error("Lowering error: {0}")]
    Lowering(#[from] haloumi_lowering::error::Error),
    /// Raised if a IR generation error occurs.
    #[error("IR gen error: {0}")]
    IRGen(#[from] haloumi_ir_gen::error::Error),
    /// Raised if the output produced by the backend failed verification.
    #[error("Output module failed verification{note}: {err}")]
    VerificationFailed {
        /// LLZK error raised by the verification procedure.
        err: llzk::error::Error,
        /// Additional context notes.
        note: &'static str,
    },
}

impl From<Error> for haloumi_lowering::error::Error {
    fn from(value: Error) -> Self {
        Self::Backend(Arc::new(value))
    }
}

#[derive(Debug, Error)]
#[error("Was expecting type {expected} but got type {actual}")]
pub(crate) struct UnexpectedTypeError {
    expected: String,
    actual: String,
}

impl UnexpectedTypeError {
    pub fn new(expected: Type<'_>, actual: Type<'_>) -> Self {
        Self {
            expected: format!("{expected}"),
            actual: format!("{actual}"),
        }
    }
    pub fn with_context(self, msg: impl ToString) -> ContextualizedError<Self> {
        ContextualizedError {
            msg: msg.to_string(),
            error: self,
        }
    }
}

impl From<UnexpectedTypeError> for haloumi_lowering::error::Error {
    fn from(value: UnexpectedTypeError) -> Self {
        Self::Backend(Arc::new(value))
    }
}
#[derive(Debug, Error)]
#[error("{msg}: {error}")]
pub(crate) struct ContextualizedError<E: std::error::Error> {
    msg: String,
    #[source]
    error: E,
}

impl<E: std::error::Error + 'static> From<ContextualizedError<E>>
    for haloumi_lowering::error::Error
{
    fn from(value: ContextualizedError<E>) -> Self {
        Self::Backend(Arc::new(value))
    }
}
