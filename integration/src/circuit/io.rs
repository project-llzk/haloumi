//! Integration support for IO related tasks in a circuit.

use num_bigint::BigUint;

pub mod ctx;
pub mod layouter;
pub mod load;
pub mod store;

pub use crate::core::table::CellReprSize;
