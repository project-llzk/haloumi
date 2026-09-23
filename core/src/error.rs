//! Error type.

use std::sync::Arc;

use crate::{io::error::IoError, slot::cell::CellError, table::TableError};
use thiserror::Error;

/// Core error type.
#[derive(Error, Clone, Debug)]
pub enum Error {
    /// Error related to the PLONK table.
    #[error(transparent)]
    TableError(#[from] TableError),
    /// Error related to cell references.
    #[error(transparent)]
    CellRefError(#[from] CellError),
    /// Error related to circuit IO.
    #[error(transparent)]
    Io(#[from] IoError),
    /// Circuit synthesis requires global constants, but circuit configuration
    /// did not call [`ConstraintSystem::enable_constant`] on fixed columns
    /// with sufficient space.
    ///
    /// [`ConstraintSystem::enable_constant`]: crate::plonk::ConstraintSystem::enable_constant
    #[error("Too few fixed columns are enabled for global constants usage")]
    NotEnoughColumnsForConstants,
    /// Raised when the default value is missing while synthesizing a table.
    #[error("Unknown default value")]
    MissingDefaultValue,
    /// Raised when a table value is missing while synthesizing a table.
    #[error("Unknown table value")]
    MissingTableValue,
    /// Raised when an unknown fixed value is assigned to a fixed cell.
    #[error("Unknown fixed value assigned to cell ({0}, {1})")]
    MissingFixedValue(usize, usize),
    /// Plonk synthesis error.
    #[error("Synthesis error")]
    Plonk(Arc<dyn std::error::Error>),
    /// An error represented with an static string.
    #[error("Error")]
    StrError(&'static str),
    /// Error when an encountered an unexpected number of elements.
    #[error("{header}Was expecting {expected} elements but got {actual}")]
    UnexpectedElements {
        /// Context header for the error
        header: String,
        /// The expected number of elements.
        expected: usize,
        /// The number of elements.
        actual: usize,
    },
}

impl From<&'static str> for Error {
    fn from(value: &'static str) -> Self {
        Self::StrError(value)
    }
}

unsafe impl Send for Error {}
unsafe impl Sync for Error {}
