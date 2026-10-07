//! Types and traits related to PLONK tables.
//!
//! Some types try to replicate the API of their namesakes in Halo2.

use std::{marker::PhantomData, ops::Deref};

use ff::Field;
use thiserror::Error;

use crate::{
    expressions::ExprBuilder,
    info_traits::CreateQuery,
    query::{Advice, Fixed, Instance},
};

/// Column type
pub trait ColumnType: std::fmt::Debug + Copy + Clone + PartialEq + Eq + std::hash::Hash {
    /// Constructs a polynomial representing a query to the cell.
    fn query_cell<F: Field, E: ExprBuilder<F>>(&self, index: usize, at: Rotation) -> E;
}

/// Erased column type.
#[derive(Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum Any {
    /// Fixed type.
    Fixed,
    /// Advice type.
    Advice,
    /// Instance type.
    Instance,
}

impl std::fmt::Debug for Any {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Fixed => write!(f, "Fix"),
            Self::Advice => write!(f, "Adv"),
            Self::Instance => write!(f, "Ins"),
        }
    }
}

impl ColumnType for Any {
    fn query_cell<F: Field, E: ExprBuilder<F>>(&self, index: usize, at: Rotation) -> E {
        match self {
            Any::Fixed => Fixed.query_cell(index, at),
            Any::Advice => Advice.query_cell(index, at),
            Any::Instance => Instance.query_cell(index, at),
        }
    }
}

impl ColumnType for Fixed {
    fn query_cell<F: Field, E: ExprBuilder<F>>(&self, index: usize, at: Rotation) -> E {
        E::FixedQuery::query_expr(index, at)
    }
}

impl ColumnType for Advice {
    fn query_cell<F: Field, E: ExprBuilder<F>>(&self, index: usize, at: Rotation) -> E {
        E::AdviceQuery::query_expr(index, at)
    }
}

impl ColumnType for Instance {
    fn query_cell<F: Field, E: ExprBuilder<F>>(&self, index: usize, at: Rotation) -> E {
        E::InstanceQuery::query_expr(index, at)
    }
}

/// A column with a type.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Column<C: ColumnType> {
    index: usize,
    column_type: C,
}

impl<C: ColumnType + std::fmt::Debug> std::fmt::Debug for Column<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}:{}", self.column_type, self.index)
    }
}

impl<C: ColumnType> Column<C> {
    /// Creates a new column.
    pub fn new(index: usize, column_type: C) -> Self {
        Self { index, column_type }
    }

    /// Returns the index of a column.
    pub fn index(&self) -> usize {
        self.index
    }

    /// Returns the column type.
    pub fn column_type(&self) -> &C {
        &self.column_type
    }

    /// Creates an expression representing a query to a cell in this column.
    pub fn query_cell<F: Field, E: ExprBuilder<F>>(&self, at: Rotation) -> E {
        self.column_type.query_cell(self.index, at)
    }
}

impl From<Column<Fixed>> for Column<Any> {
    fn from(value: Column<Fixed>) -> Self {
        Self {
            index: value.index,
            column_type: Any::Fixed,
        }
    }
}

impl TryFrom<Column<Any>> for Column<Fixed> {
    type Error = TableError;

    fn try_from(value: Column<Any>) -> Result<Self, Self::Error> {
        match value.column_type {
            Any::Fixed => Ok(Self {
                index: value.index,
                column_type: Fixed,
            }),
            c => Err(TableError::ExpectedFixed(c)),
        }
    }
}

impl From<Column<Advice>> for Column<Any> {
    fn from(value: Column<Advice>) -> Self {
        Self {
            index: value.index,
            column_type: Any::Advice,
        }
    }
}

impl TryFrom<Column<Any>> for Column<Advice> {
    type Error = TableError;

    fn try_from(value: Column<Any>) -> Result<Self, Self::Error> {
        match value.column_type {
            Any::Advice => Ok(Self {
                index: value.index,
                column_type: Advice,
            }),
            c => Err(TableError::ExpectedAdvice(c)),
        }
    }
}

impl From<Column<Instance>> for Column<Any> {
    fn from(value: Column<Instance>) -> Self {
        Self {
            index: value.index,
            column_type: Any::Instance,
        }
    }
}

impl TryFrom<Column<Any>> for Column<Instance> {
    type Error = TableError;

    fn try_from(value: Column<Any>) -> Result<Self, Self::Error> {
        match value.column_type {
            Any::Instance => Ok(Self {
                index: value.index,
                column_type: Instance,
            }),
            c => Err(TableError::ExpectedInstance(c)),
        }
    }
}

/// Represents a cell in the table.
#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub struct Cell {
    /// The index of the region this cell belongs to.
    pub region_index: RegionIndex,
    /// Offset relative to the region of the cell's row.
    pub row_offset: usize,
    /// The cell's column.
    pub column: Column<Any>,
}

/// Replacement type for Halo2's `Rotation` type.
pub type Rotation = i32;

/// Extension methods for [`Rotation`].
pub trait RotationExt {
    /// Returns the current row.
    fn cur() -> Self;

    /// Returns the next row.
    fn next() -> Self;

    /// Returns the previous row.
    fn prev() -> Self;
}

impl RotationExt for Rotation {
    fn cur() -> Self {
        0
    }

    fn next() -> Self {
        1
    }

    fn prev() -> Self {
        -1
    }
}

/// Replacement for Halo2's `RegionIndex` type.
#[derive(Eq, Hash, PartialEq, Debug, Copy, Clone)]
pub struct RegionIndex(usize);

impl Deref for RegionIndex {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<usize> for RegionIndex {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

/// Replacement for Halo2's `RegionStart` type.
#[derive(Eq, Hash, PartialEq, Debug, Copy, Clone)]
pub struct RegionStart(usize);

impl Deref for RegionStart {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<usize> for RegionStart {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

/// Errors related to the PLONK table.
#[derive(Error, Copy, Clone, Debug)]
pub enum TableError {
    /// Unexpected column type when Fixed was expected.
    #[error("Expected Any::Fixed. Got {0:?}")]
    ExpectedFixed(Any),
    /// Unexpected column type when Advice was expected.
    #[error("Expected Any::Advice. Got {0:?}")]
    ExpectedAdvice(Any),
    /// Unexpected column type when Instance was expected.
    #[error("Expected Any::Instance. Got {0:?}")]
    ExpectedInstance(Any),
}

/// Implementations of this trait represent complex types that aggregate a
/// collection of `Cell` values.
pub trait DecomposeIn<Cell> {
    /// Returns an iterator of `Cell` instances.
    fn cells(&self) -> impl IntoIterator<Item = Cell>;
}

impl<Cell> DecomposeIn<Cell> for u32 {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        std::iter::empty()
    }
}

impl<Cell, T> DecomposeIn<Cell> for PhantomData<T> {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        std::iter::empty()
    }
}

impl<Cell, T: DecomposeIn<Cell> + ?Sized> DecomposeIn<Cell> for &T {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        (*self).cells()
    }
}

impl<Cell, T: DecomposeIn<Cell> + ?Sized> DecomposeIn<Cell> for &mut T {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        (**self).cells()
    }
}

impl<Cell, T: DecomposeIn<Cell>, E> DecomposeIn<Cell> for Result<T, E> {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        self.iter().flat_map(|t| t.cells())
    }
}

impl<Cell, T: DecomposeIn<Cell>> DecomposeIn<Cell> for Option<T> {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        self.iter().flat_map(|t| t.cells())
    }
}

impl<Cell, T: DecomposeIn<Cell>> DecomposeIn<Cell> for [T] {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        self.iter().flat_map(|t| t.cells())
    }
}

impl<Cell, T: DecomposeIn<Cell>, const N: usize> DecomposeIn<Cell> for [T; N] {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        self.iter().flat_map(|t| t.cells())
    }
}

impl<Cell, T: DecomposeIn<Cell>> DecomposeIn<Cell> for Vec<T> {
    fn cells(&self) -> impl IntoIterator<Item = Cell> {
        self.iter().flat_map(|t| t.cells())
    }
}

macro_rules! chain {
    () => {
        std::iter::empty()
    };
    ($h:expr $(,$t:expr)* $(,)?) => {
        $h.into_iter().chain( chain!($( $t, )*))
    };
}

macro_rules! tuple_impl {
    () => {
        tuple_impl!(@impl [] [] [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12] [0 1 2 3 4 5 6 7 8 9 10 11]);
    };

    (@impl [$($done:ident)*] [$($idxs:tt)*] [$head:ident $($rest:ident)*] [$i:tt $($is:tt)*]) => {
        //// Implement for tuple ($head, $done...)
        impl<Cell, $head: DecomposeIn<Cell>, $( $done: DecomposeIn<Cell>, )*> DecomposeIn<Cell> for (
                $head, $( $done, )*
            )
        {
            fn cells(&self) -> impl IntoIterator<Item = Cell> {
                chain!($(
                    self.$idxs.cells(),
                )*
                self.$i.cells())
            }
        }

        // Recurse
        tuple_impl!(
            @impl [$head $($done)*] [$($idxs)* $i] [$($rest)*] [$($is)*]
        );
    };

    // Stop when no identifiers remain
    (@impl [$($done:ident)*] [$($idxs:tt)*] [] $rem:tt) => {
        // Also emit the 0-tuple base case
        impl<Cell> DecomposeIn<Cell> for () {
            fn cells(&self) -> impl IntoIterator<Item = Cell> {
                std::iter::empty()
            }
        }
    };

}

tuple_impl!();
