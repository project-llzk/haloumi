//! IO error type.

use std::{num::ParseIntError, str::ParseBoolError};

use num_bigint::ParseBigIntError;

/// Error type.
#[derive(thiserror::Error, Clone, Debug)]
pub enum IoError {
    /// Parsing error while loading a field element from a string.
    #[error("Failure while parsing field element")]
    FieldParsingError,
    /// The circuit requested more constants than provided.
    #[error("Not enough constants")]
    NotEnoughConstants,
    /// The circuit did not declare enough cells for input or output.
    #[error("IO cell iterator was exhausted")]
    NotEnoughIOCells,
    /// Integer parse error.
    #[error("Parse failure")]
    IntParse(#[from] ParseIntError),
    /// Boolean parse error.
    #[error("Parse failure")]
    BoolParse(#[from] ParseBoolError),
    /// BigUint parse error.
    #[error("Parse failure")]
    BigUintParse(#[from] ParseBigIntError),
}
