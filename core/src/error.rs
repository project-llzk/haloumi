//! Error type.

use crate::{slot::cell::CellError, table::TableError};
use thiserror::Error;

/// Core error type.
#[derive(Error, Copy, Clone, Debug)]
pub enum Error {
    /// Error related to the PLONK table.
    #[error(transparent)]
    TableError(#[from] TableError),
    /// Error related to cell references.
    #[error(transparent)]
    CellRefError(#[from] CellError),
}
