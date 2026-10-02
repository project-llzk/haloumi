//! Types related to constraints.

use crate::{
    felt::Felt,
    query::Fixed,
    table::{Any, Column},
};

#[cfg(any(test, feature = "arbitrary"))]
use quickcheck::Arbitrary;

/// Types of copy constraints.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CopyConstraint {
    /// A copy constraint between two cells.
    Cells(Column<Any>, usize, Column<Any>, usize),
    /// Constraints a fixed cell to a constant value.
    Fixed(Column<Fixed>, usize, Felt),
}

#[cfg(any(test, feature = "arbitrary"))]
impl Arbitrary for CopyConstraint {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        if bool::arbitrary(g) {
            Self::Cells(
                Column::arbitrary(g),
                usize::arbitrary(g),
                Column::arbitrary(g),
                usize::arbitrary(g),
            )
        } else {
            Self::Fixed(
                Column::arbitrary(g),
                usize::arbitrary(g),
                Felt::arbitrary(g),
            )
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "serde")]
    use quickcheck_macros::quickcheck;

    use super::*;

    #[cfg(feature = "serde")]
    #[quickcheck]
    fn copy_constraint_round_trip(value: CopyConstraint) {
        assert_eq!(value, crate::serde_tests_helpers::round_trip(value));
    }
}
