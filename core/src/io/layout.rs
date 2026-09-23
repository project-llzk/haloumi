//! Helper traits for working with layouters during IO.

use ff::Field;

use crate::{query::AdviceCopy, types::Types};

/// Adaptor trait that defines the required behavior from a Layouter.
pub trait LayoutHelper<F: Field, T: Types<F>> {
    /// Constraints two cells to be equal.
    ///
    /// The left hand side cell could be any cell and the right hand side is an instance cell.
    fn constrain_instance(
        &mut self,
        cell: T::Cell,
        instance_col: T::InstanceCol,
        instance_row: usize,
    ) -> Result<(), T::Error>;

    /// Constraints an advice cell to a constant value.
    fn constrain_advice_constant(
        &mut self,
        advice_col: T::AdviceCol,
        advice_row: usize,
        constant: F,
    ) -> Result<T::Cell, T::Error>;

    /// Assigns an advice cell from an instance cell.
    fn assign_advice_from_instance<V>(
        &mut self,
        advice_col: T::AdviceCol,
        advice_row: usize,
        instance_col: T::InstanceCol,
        instance_row: usize,
    ) -> Result<T::AssignedCell<V>, T::Error>
    where
        V: Clone,
        T::Rational: for<'v> From<&'v V>;

    /// Copies the cell's contents into the given advice cell.
    fn copy_advice<V>(
        &mut self,
        ac: &T::AssignedCell<V>,
        region: &mut T::Region<'_>,
        advice_col: T::AdviceCol,
        advice_row: usize,
    ) -> Result<T::AssignedCell<V>, T::Error>
    where
        V: Clone,
        T::AssignedCell<V>: AdviceCopy<V, F, T>,
        T::Rational: for<'v> From<&'v V>;

    /// Enters the scope of a region.
    fn region<A, AR, N, NR>(&mut self, name: N, assignment: A) -> Result<AR, T::Error>
    where
        A: FnMut(T::Region<'_>) -> Result<AR, T::Error>,
        N: Fn() -> NR,
        NR: Into<String>;
}
