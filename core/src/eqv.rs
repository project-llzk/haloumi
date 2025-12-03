//! Types and traits related to equivalence relations.
//!
//! Re-exports the [`eqv`] crate for convenience.

pub use ::eqv::*;

/// Equivalence relation on symbolic equivalence.
///
/// Symbolic in this context means that when comparing
/// entities information that does not affect the semantics
/// of what the entities are expression is ignored.
#[derive(Debug)]
pub struct SymbolicEqv;
