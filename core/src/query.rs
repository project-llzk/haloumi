//! Types and traits related to cell queries.

mod sealed {
    /// Sealed trait pattern to avoid clients implementing the trait [`super::QueryKind`] on
    /// external types.
    pub trait QK {}
}

/// Marker trait for defining the kind of a query.
pub trait QueryKind: sealed::QK {}

/// Marker for fixed cell queries.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Fixed;

#[cfg(any(test, feature = "arbitrary"))]
impl quickcheck::Arbitrary for Fixed {
    fn arbitrary(_: &mut quickcheck::Gen) -> Self {
        Self
    }
}

impl sealed::QK for Fixed {}
impl QueryKind for Fixed {}

impl std::fmt::Debug for Fixed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Fix")
    }
}

/// Marker for advice cell queries.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Advice;

#[cfg(any(test, feature = "arbitrary"))]
impl quickcheck::Arbitrary for Advice {
    fn arbitrary(_: &mut quickcheck::Gen) -> Self {
        Self
    }
}

impl sealed::QK for Advice {}
impl QueryKind for Advice {}

impl std::fmt::Debug for Advice {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Adv")
    }
}

/// Marker for instance cell queries.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Instance;

#[cfg(any(test, feature = "arbitrary"))]
impl quickcheck::Arbitrary for Instance {
    fn arbitrary(_: &mut quickcheck::Gen) -> Self {
        Self
    }
}

impl sealed::QK for Instance {}
impl QueryKind for Instance {}

impl std::fmt::Debug for Instance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Ins")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(feature = "serde")]
    use crate::serde_tests_helpers::round_trip;

    #[cfg(feature = "serde")]
    #[test]
    fn query_markers_round_trip() {
        assert_eq!(Fixed, round_trip(Fixed));
        assert_eq!(Advice, round_trip(Advice));
        assert_eq!(Instance, round_trip(Instance));
    }
}
