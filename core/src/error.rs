//! Error type.

use crate::table::Any;
use thiserror::Error;

/// Core error type.
#[derive(Error, Copy, Clone, Debug)]
pub enum Error {
    /// Unexpected column type when Fixed was expected.
    #[error("Expected Any::Fixed. Got {0:?}")]
    ExpectedFixed(Any),
    /// Unexpected column type when Advice was expected.
    #[error("Expected Any::Advice. Got {0:?}")]
    ExpectedAdvice(Any),
    /// Unexpected column type when Instance was expected.
    #[error("Expected Any::Instance. Got {0:?}")]
    ExpectedInstance(Any),
}
