#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

mod canon;
mod circuit;
pub mod error;
pub mod expr;
pub mod groups;
pub mod printer;
mod slot;
pub mod stmt;
pub mod traits;
pub use circuit::IRCircuit;
pub use haloumi_core::{cmp::*, eqv::*, felt::*, slot::*};
