//! Adaptor traits related to layouting.

use crate::{
    groups::RegionsGroupHooks,
    info_traits::{ChallengeInfo, SelectorInfo},
    query::{Advice, AdviceCopy, Fixed, Instance},
    table::{Any, Cell, Column, FromCell},
    types::Types,
};
use ff::Field;

/// Wrapper around a region layouter intended for conversion between halo2 and haloumi.
pub struct RegionAdaptor<'l, F: Field, E>(pub &'l mut dyn RegionLayouter<F, E>);

impl<F: Field, E> std::fmt::Debug for RegionAdaptor<'_, F, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("RegionAdaptor").finish()
    }
}

/// Bespoke conversion trait from a [`RegionAdaptor`].
pub trait FromRegionAdaptor<'a, F: Field, E> {
    /// Creates an instance of self from a region adaptor.
    fn from_region_adaptor(adaptor: &'a mut RegionAdaptor<'_, F, E>) -> Self;
}

/// Wrapper around a table layouter intended for conversion between halo2 and haloumi.
pub struct TableAdaptor<'l, F: Field, E>(pub &'l mut dyn TableLayouter<F, E>);

impl<F: Field, E> std::fmt::Debug for TableAdaptor<'_, F, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("TableAdaptor").finish()
    }
}

/// Adaptor wrapper around a Haloumi layouter.
#[derive(Debug)]
pub struct LayoutAdaptor<'l, L>(pub &'l mut L);

impl<L> LayoutAdaptor<'_, L> {
    /// Adds an equality constraint between the cell and the given instance cell.
    pub fn constrain_instance<F, T>(
        &mut self,
        cell: T::Cell,
        instance_col: T::InstanceCol,
        instance_row: usize,
    ) -> Result<(), T::Error>
    where
        F: Field,
        T: Types<F>,
        L: Layouter<F, T::Error>,
    {
        self.0
            .constrain_instance(cell.into(), instance_col, instance_row)
    }

    /// Adds an equality constraint between the advice cell and a constant value.
    pub fn constrain_advice_constant<F, T>(
        &mut self,
        advice_col: T::AdviceCol,
        advice_row: usize,
        constant: F,
    ) -> Result<T::Cell, T::Error>
    where
        F: Field,
        T: Types<F>,
        L: Layouter<F, T::Error>,
    {
        let advice_col = Column::<Advice>::from(advice_col.into());
        Ok(self
            .0
            .assign_region(
                || format!("Adv[{}, {advice_row}] == 0", advice_col.index()),
                |region| {
                    region.0.assign_advice_from_constant(
                        &|| format!("Adv[{}, {advice_row}]", advice_col.index()),
                        advice_col,
                        advice_row,
                        constant,
                    )
                },
            )?
            .into())
    }

    /// Adds an equality constraint between the given advice and instance cells.
    pub fn assign_advice_from_instance<F, T, V>(
        &mut self,
        advice_col: T::AdviceCol,
        advice_row: usize,
        instance_col: T::InstanceCol,
        instance_row: usize,
    ) -> Result<T::AssignedCell<V>, T::Error>
    where
        V: Clone,
        F: Field,
        T: Types<F>,
        L: Layouter<F, T::Error>,
    {
        let advice_col = Column::<Advice>::from(advice_col.into());
        let instance_col = Column::<Instance>::from(instance_col.into());
        let c = self.0.assign_region(
            || "ins",
            |region| {
                region.0.assign_advice(
                    &|| {
                        format!(
                            "Adv[{}, +{advice_row}] == Ins[{}, {instance_row}]",
                            advice_col.index(),
                            instance_col.index()
                        )
                    },
                    advice_col,
                    advice_row,
                    &mut || None,
                )
            },
        )?;

        self.0.constrain_instance(c, instance_col, instance_row)?;
        Ok(from_cell_helper(c))
    }

    /// Adds an equality constraint between the assigned cell and the advice cell.
    pub fn copy_advice<F, T, V>(
        &mut self,
        ac: &T::AssignedCell<V>,
        region: &mut T::Region<'_>,
        advice_col: T::AdviceCol,
        advice_row: usize,
    ) -> Result<T::AssignedCell<V>, T::Error>
    where
        V: Clone,
        T::AssignedCell<V>: AdviceCopy<V, F, T>,
        F: Field,
        T: Types<F>,
        L: Layouter<F, T::Error>,
    {
        ac.copy_advice_helper(region, advice_col, advice_row)
    }

    /// Creates a new region in the table.
    pub fn region<F, T, A, AR, N, NR>(&mut self, name: N, mut assignment: A) -> Result<AR, T::Error>
    where
        A: FnMut(T::Region<'_>) -> Result<AR, T::Error>,
        N: Fn() -> NR,
        NR: Into<String>,
        F: Field,
        T: Types<F>,
        L: Layouter<F, T::Error>,
    {
        self.0.assign_region(name, |mut adaptor| {
            assignment(from_region_adaptor(&mut adaptor))
        })
    }
}

impl<F, C, L> RegionsGroupHooks<F, C> for LayoutAdaptor<'_, L>
where
    L: RegionsGroupHooks<F, C>,
{
    type Error = L::Error;

    type RootHook = Self;

    fn get_root_hook(&mut self) -> &mut Self::RootHook {
        self
    }

    fn push_group<N, NR, K>(&mut self, name: N, key: K)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
        K: crate::groups::GroupKey,
    {
        self.0.push_group(name, key);
    }

    fn pop_group(&mut self, meta: crate::groups::RegionsGroup<C>) {
        self.0.pop_group(meta);
    }
}

/// Helper for keeping the syntax of its users a bit more terse.
fn from_cell_helper<T>(cell: Cell) -> T
where
    T: FromCell,
{
    T::from_cell(cell)
}

/// Helper for keeping the syntax of its users a bit more terse.
fn from_region_adaptor<'a, T, F, E>(adaptor: &'a mut RegionAdaptor<'_, F, E>) -> T
where
    T: FromRegionAdaptor<'a, F, E>,
    F: Field,
{
    T::from_region_adaptor(adaptor)
}

/// Replica trait of a halo2 layouter.
///
/// During integration there must be a blanket implementation that links the two traits.
pub trait Layouter<F: Field, E> {
    /// Represents the type of the "root" of this layouter, so that nested
    /// namespaces can minimize indirection.
    type Root;

    /// Assign a region of gates to an absolute row number.
    ///
    /// Inside the closure, the chip may freely use relative offsets; the
    /// `Layouter` will treat these assignments as a single "region" within
    /// the circuit. Outside this closure, the `Layouter` is allowed to
    /// optimise as it sees fit.
    ///
    /// ```text
    /// fn assign_region(&mut self, || "region name", |region| {
    ///     let config = chip.config();
    ///     region.assign_advice(config.a, offset, || { Some(value)});
    /// });
    /// ```
    fn assign_region<A, AR, N, NR>(&mut self, name: N, assignment: A) -> Result<AR, E>
    where
        A: FnMut(RegionAdaptor<'_, F, E>) -> Result<AR, E>,
        N: Fn() -> NR,
        NR: Into<String>;

    /// Assign a table region to an absolute row number.
    ///
    /// ```text
    /// fn assign_table(&mut self, || "table name", |table| {
    ///     let config = chip.config();
    ///     table.assign_fixed(config.a, offset, || { Some(value)});
    /// });
    /// ```
    fn assign_table<A, N, NR>(&mut self, name: N, assignment: A) -> Result<(), E>
    where
        A: FnMut(TableAdaptor<'_, F, E>) -> Result<(), E>,
        N: Fn() -> NR,
        NR: Into<String>;

    /// Constrains a [`Cell`] to equal an instance column's row value at an
    /// absolute position.
    fn constrain_instance(
        &mut self,
        cell: impl Into<Cell>,
        column: impl Into<Column<Instance>>,
        row: usize,
    ) -> Result<(), E>;

    /// Queries the value of the given challenge.
    ///
    /// Returns `Value::unknown()` if the current synthesis phase is before the
    /// challenge can be queried.
    fn get_challenge(&self, challenge: impl ChallengeInfo) -> Option<F>;

    /// Gets the "root" of this assignment, bypassing the namespacing.
    ///
    /// Not intended for downstream consumption; use [`Layouter::namespace`]
    /// instead.
    fn get_root(&mut self) -> &mut Self::Root;

    /// Creates a new (sub)namespace and enters into it.
    ///
    /// Not intended for downstream consumption; use [`Layouter::namespace`]
    /// instead.
    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR;

    /// Exits out of the existing namespace.
    ///
    /// Not intended for downstream consumption; use [`Layouter::namespace`]
    /// instead.
    fn pop_namespace(&mut self, gadget_name: Option<String>);
}

/// Replica trait of a halo2 region layouter.
///
/// During integration there must be a blanket implementation that links the two traits.
pub trait RegionLayouter<F: Field, E> {
    /// Enables a selector at the given offset.
    fn enable_selector<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        selector: &dyn SelectorInfo,
        offset: usize,
    ) -> Result<(), E>;

    /// Allows the circuit implementor to name/annotate a Column within a Region
    /// context.
    ///
    /// This is useful in order to improve the amount of information that
    /// `prover.verify()` and `prover.assert_satisfied()` can provide.
    fn name_column<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Any>,
    );

    /// Assign an advice column value (witness)
    fn assign_advice<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Advice>,
        offset: usize,
        to: &'v mut (dyn FnMut() -> Option<F> + 'v),
    ) -> Result<Cell, E>;

    /// Assigns a constant value to the column `advice` at `offset` within this
    /// region.
    ///
    /// The constant value will be assigned to a cell within one of the fixed
    /// columns configured via `ConstraintSystem::enable_constant`.
    ///
    /// Returns the advice cell that has been equality-constrained to the
    /// constant.
    fn assign_advice_from_constant<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Advice>,
        offset: usize,
        constant: F,
    ) -> Result<Cell, E>;

    /// Assign the value of the instance column's cell at absolute location
    /// `row` to the column `advice` at `offset` within this region.
    ///
    /// Returns the advice cell that has been equality-constrained to the
    /// instance cell, and its value if known.
    fn assign_advice_from_instance<'v>(
        &mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        instance: Column<Instance>,
        row: usize,
        advice: Column<Advice>,
        offset: usize,
    ) -> Result<(Cell, Option<F>), E>;

    /// Returns the value of the instance column's cell at absolute location
    /// `row`.
    fn instance_value(&mut self, instance: Column<Instance>, row: usize) -> Result<Option<F>, E>;

    /// Assigns a fixed value
    fn assign_fixed<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Fixed>,
        offset: usize,
        to: &'v mut (dyn FnMut() -> Option<F> + 'v),
    ) -> Result<Cell, E>;

    /// Constrains a cell to have a constant value.
    ///
    /// Returns an error if the cell is in a column where equality has not been
    /// enabled.
    fn constrain_constant(&mut self, cell: Cell, constant: F) -> Result<(), E>;

    /// Constraint two cells to have the same value.
    ///
    /// Returns an error if either of the cells is not within the given
    /// permutation.
    fn constrain_equal(&mut self, left: Cell, right: Cell) -> Result<(), E>;
}

/// Replica trait of a halo2 region layouter.
///
/// During integration there must be a blanket implementation that links the two traits.
pub trait TableLayouter<F: Field, E> {
    /// Assigns a fixed value to a table cell.
    ///
    /// Returns an error if the table cell has already been assigned to.
    fn assign_cell<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Fixed>,
        offset: usize,
        to: &'v mut (dyn FnMut() -> Option<F> + 'v),
    ) -> Result<(), E>;
}
