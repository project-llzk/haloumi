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
pub struct Fixed;

impl sealed::QK for Fixed {}
impl QueryKind for Fixed {}

impl std::fmt::Debug for Fixed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Fix")
    }
}

/// Marker for advice cell queries.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Advice;

impl sealed::QK for Advice {}
impl QueryKind for Advice {}

impl std::fmt::Debug for Advice {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Adv")
    }
}

/// Marker for instance cell queries.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Instance;

impl sealed::QK for Instance {}
impl QueryKind for Instance {}

impl std::fmt::Debug for Instance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Ins")
    }
}
