//! Types related to constraints.

use crate::{
    felt::Felt,
    query::Fixed,
    table::{Any, Column},
};

/// Types of copy constraints.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum CopyConstraint {
    /// A copy constraint between two cells.
    Cells(Column<Any>, usize, Column<Any>, usize),
    /// Constraints a fixed cell to a constant value.
    Fixed(Column<Fixed>, usize, Felt),
}
