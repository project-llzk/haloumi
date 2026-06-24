//! Error types related to synthesis.

use std::sync::Arc;

/// Errors that can raise while synthesizing a circuit.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Raised by [`CircuitIO`](crate::io::CircuitIO) if the specification is not valid.
    #[error("sets are not disjoint")]
    IOValidation,
    /// Raised by [`FixedData`](crate::regions::FixedData) if there are missing columns.
    #[error("fixed data does not have all the required columns")]
    InvalidTableColumns,
    /// Raised by [`TableData`](crate::regions::TableData) while obtaining of rows of a table.
    #[error("could not get the largest row fill of table")]
    NoTableUpperLimit,
    /// Raised by [`TableData`](crate::regions::TableData) while obtaining the rows of a table.
    #[error("detected gaps in table")]
    DetectedTableGaps,
    /// Raised by [`Lookup`](crate::lookups::Lookup) if the table queries contain queries to cells
    /// other than [`Fixed`](haloumi_core::query::Fixed).
    #[error("table row expressions can only be fixed cell queries")]
    DisallowedQueriesInLookup,
    /// Raised by [`Lookup`](crate::lookups::Lookup) if the expression's query do not contain the
    /// given column.
    #[error("column {0} not found")]
    ColumnNotFound(usize),
    /// Wraps an error raised by the call to
    /// [`CircuitSynthesis::synthesize`](crate::CircuitSynthesis::synthesize).
    #[error(transparent)]
    Synthesis(Arc<dyn std::error::Error + Sync + Send>),
}
