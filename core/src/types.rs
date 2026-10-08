//! Central integration point between Halo2 and Haloumi types.

use std::{error, fmt, hash, ops::Deref};

use ff::Field;

use crate::{
    error::Error,
    layouter::FromRegionAdaptor,
    query::{Advice, Instance},
    table::{Cell, Column, DecomposeIn, FromCell},
};

/// This trait defines the halo2 types required by this crate.
/// An implementation of halo2 compatible with this crate must have
/// some type that implements this trait s.t. it can be passed to traits
/// and types in this crate.
pub trait Types<F: Field>: Sized {
    /// Type for instance columns.
    type InstanceCol: fmt::Debug + Copy + Clone + Into<Column<Instance>> + From<Column<Instance>>;
    /// Type for advice columns.
    type AdviceCol: fmt::Debug + Copy + Clone + Into<Column<Advice>> + From<Column<Advice>>;
    /// Type for a cell.
    type Cell: fmt::Debug + Copy + Clone + DecomposeIn<Self::Cell> + Into<Cell> + From<Cell>;
    /// Type for an assigned cell.
    type AssignedCell<V>: FromCell;
    /// Region type.
    type Region<'a>: FromRegionAdaptor<'a, F, Self::Error>;
    /// Error type.
    type Error: Into<Error> + From<Error> + error::Error + Send + Sync + 'static;
    /// Region index type
    type RegionIndex: hash::Hash + Copy + Eq + Deref<Target = usize>;
    /// Expression type
    type Expression;
    /// Associated type for Rational.
    type Rational;
}
