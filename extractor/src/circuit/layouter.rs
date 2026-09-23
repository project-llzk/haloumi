//! Layouter used while recording an extracted circuit.

use std::{
    cmp,
    collections::{HashMap, HashSet},
    hash::Hash,
    marker::PhantomData,
};

use ff::Field;
use haloumi_core::{error::Error, table::TableError};
use haloumi_core::{
    groups::{GroupKey, GroupKeyInstance, RegionsGroup, RegionsGroupHooks},
    info_traits::SelectorInfo,
    layouter::{Layouter, RegionAdaptor, RegionLayouter, TableAdaptor, TableLayouter},
    query::{Advice, Fixed, Instance},
    synthesis::SynthesizerLike,
    table::{Any, Cell, Column, RegionIndex, RegionStart},
};
use haloumi_synthesis::synthesizer::Synthesizer;

/// A Haloumi layouter that records assignments in a [`Synthesizer`].
#[derive(Debug)]
pub struct ExtractionLayouter<'s, F: Field, E> {
    synthesizer: &'s mut Synthesizer<F>,
    constants: Box<[Column<Fixed>]>,
    /// Stores the starting row for each region.
    regions: Vec<RegionStart>,

    /// Stores the first empty row for each column.
    columns: HashMap<RegionColumn, usize>,
    /// Stores the table fixed columns.
    table_columns: Vec<Column<Fixed>>,
    /// Group depth
    group_depth: usize,
    _error: PhantomData<E>,
}

impl<'s, F: Field, E> ExtractionLayouter<'s, F, E> {
    /// Creates a layouter that records into `synthesizer`.
    pub fn new<C: Into<Column<Fixed>> + Clone>(
        synthesizer: &'s mut Synthesizer<F>,
        constants: &[C],
    ) -> Self {
        Self {
            synthesizer,
            constants: Vec::from_iter(
                constants
                    .iter()
                    .map(|c| Column::<Fixed>::from(c.clone().into())),
            )
            .into(),
            regions: Default::default(),
            columns: Default::default(),
            table_columns: Default::default(),
            group_depth: Default::default(),
            _error: PhantomData,
        }
    }
}

impl<F: Field, E, C> RegionsGroupHooks<F, C> for ExtractionLayouter<'_, F, E>
where
    C: Copy + Eq + Hash + Into<Cell>,
{
    type Error = E;
    type RootHook = Self;

    fn get_root_hook(&mut self) -> &mut Self::RootHook {
        self
    }

    fn push_group<N, NR, K>(&mut self, name: N, key: K)
    where
        N: FnOnce() -> NR,
        NR: Into<String>,
        K: GroupKey,
    {
        self.group_depth += 1;
        let name: String = name().into();
        log::debug!("{}> Pushing group '{name}'", "-".repeat(self.group_depth));

        self.synthesizer
            .enter_group(name, *GroupKeyInstance::from(key));
    }

    fn pop_group(&mut self, meta: RegionsGroup<C>) {
        log::debug!("{}> Popping group", "-".repeat(self.group_depth));
        log::debug!(
            "{}>   Inputs:  {:?}",
            "-".repeat(self.group_depth),
            Vec::from_iter(meta.inputs().map(|cell| CellDbg(cell.into()))),
        );
        log::debug!(
            "{}>   Outputs: {:?}",
            "-".repeat(self.group_depth),
            Vec::from_iter(meta.outputs().map(|cell| CellDbg(cell.into()))),
        );
        self.group_depth -= 1;
        self.synthesizer.exit_group(meta)
    }
}

impl<F: Field, E: From<Error>> Layouter<F, E> for ExtractionLayouter<'_, F, E> {
    type Root = Self;

    fn assign_region<A, AR, N, NR>(&mut self, name: N, mut assignment: A) -> Result<AR, E>
    where
        A: FnMut(RegionAdaptor<'_, F, E>) -> Result<AR, E>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        let region_index = self.regions.len();

        let name: String = name().into();
        log::debug!(
            "{}> Entering region '{name}' ({region_index})",
            "-".repeat(self.group_depth)
        );

        // Get shape of the region.
        let mut shape = RegionShape::new(region_index.into());
        assignment(RegionAdaptor(&mut shape))?;

        // Lay out this region. We implement the simplest approach here: position the
        // region starting at the earliest row for which none of the columns are in use.
        let mut region_start = 0;
        for column in shape.columns() {
            region_start = cmp::max(region_start, self.columns.get(column).cloned().unwrap_or(0));
        }
        self.regions.push(region_start.into());

        // Update column usage information.
        for column in shape.columns() {
            self.columns
                .insert(*column, region_start + shape.row_count());
        }

        // Assign region cells.
        self.synthesizer
            //.enter_region(name, Some(region_index.into()), Some(region_start.into()));
            .enter_region(name, None, Some(region_start.into()));
        let mut region = ExtractionRegion::new(
            self.synthesizer,
            region_index.into(),
            &self.regions,
            self.group_depth,
        );
        let result = assignment(RegionAdaptor(&mut region))?;
        let constants_to_assign = region.constants;
        self.synthesizer.exit_region();

        // Assign constants. For the simple floor planner, we assign constants in order
        // in the first `constants` column.
        if self.constants.is_empty() {
            if !constants_to_assign.is_empty() {
                return Err(Error::NotEnoughColumnsForConstants.into());
            }
        } else {
            let constants_column = self.constants[0];
            let next_constant_row = self
                .columns
                .entry(Column::<Any>::from(constants_column).into())
                .or_default();
            for (constant, advice) in constants_to_assign {
                self.synthesizer
                    .on_fixed_assigned(constants_column, *next_constant_row, constant);
                self.synthesizer.copy(
                    constants_column,
                    *next_constant_row,
                    advice.column,
                    *self.regions[*advice.region_index] + advice.row_offset,
                );
                *next_constant_row += 1;
            }
        }

        Ok(result)
    }

    fn assign_table<A, N, NR>(&mut self, name: N, mut assignment: A) -> Result<(), E>
    where
        A: FnMut(TableAdaptor<'_, F, E>) -> Result<(), E>,
        N: Fn() -> NR,
        NR: Into<String>,
    {
        self.synthesizer.enter_region(name().into(), None, None);
        let mut table = ExtractionTable::new(self.synthesizer, &self.table_columns);
        assignment(TableAdaptor(&mut table))?;
        let default_and_assigned = table.default_and_assigned;
        self.synthesizer.exit_region();

        // Check that all table columns have the same length `first_unused`,
        // and all cells up to that length are assigned.
        let first_unused = compute_table_lengths(&default_and_assigned)?;

        // Record these columns so that we can prevent them from being used again.
        for column in default_and_assigned.keys() {
            self.table_columns.push(*column);
        }

        for (col, (default_val, _)) in default_and_assigned {
            // default_val must be Some because we must have assigned
            // at least one cell in each column, and in that case we checked
            // that all cells up to first_unused were assigned.
            self.synthesizer.fill_from_row(
                col,
                first_unused,
                default_val.flatten().ok_or(Error::MissingDefaultValue)?,
            );
        }

        self.synthesizer.mark_region_as_table();
        Ok(())
    }

    fn constrain_instance(
        &mut self,
        cell: impl Into<Cell>,
        instance: impl Into<Column<Instance>>,
        row: usize,
    ) -> Result<(), E> {
        let cell = cell.into();
        self.synthesizer.copy(
            cell.column,
            *self.regions[*cell.region_index] + cell.row_offset,
            instance.into(),
            row,
        );
        Ok(())
    }

    fn get_challenge(&self, _: impl haloumi_core::info_traits::ChallengeInfo) -> Option<F> {
        None
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }

    fn push_namespace<NR, N>(&mut self, name: N)
    where
        N: FnOnce() -> NR,
        NR: Into<String>,
    {
        self.synthesizer.push_namespace(name().into());
    }

    fn pop_namespace(&mut self, name: Option<String>) {
        self.synthesizer.pop_namespace(name);
    }
}

#[derive(Debug)]
struct ExtractionRegion<'s, 'r, F: Field, E> {
    synthesizer: &'s mut Synthesizer<F>,
    region_index: RegionIndex,
    regions: &'r [RegionStart],
    /// Stores the constants to be assigned, and the cells to which they are
    /// copied.
    constants: Vec<(F, Cell)>,
    group_depth: usize,
    _error: PhantomData<E>,
}

impl<'s, 'r, F: Field, E> ExtractionRegion<'s, 'r, F, E> {
    fn new(
        synthesizer: &'s mut Synthesizer<F>,
        region_index: RegionIndex,
        regions: &'r [RegionStart],
        group_depth: usize,
    ) -> Self {
        Self {
            synthesizer,
            region_index,
            regions,
            constants: vec![],
            group_depth,
            _error: PhantomData,
        }
    }

    fn row(&self, offset: usize) -> usize {
        self.row_at(self.region_index, offset)
    }

    fn row_at(&self, index: RegionIndex, offset: usize) -> usize {
        *self.regions[*index] + offset
    }
}

impl<F: Field, E: From<Error>> RegionLayouter<F, E> for ExtractionRegion<'_, '_, F, E> {
    fn enable_selector(
        &mut self,
        annotation: &(dyn Fn() -> String + '_),
        selector: &dyn SelectorInfo,
        offset: usize,
    ) -> Result<(), E> {
        log::debug!(
            "{}> Enabled selector {} @ R{}+{offset}(={}) (note: {:?})",
            "-".repeat(self.group_depth),
            selector.id(),
            *self.region_index,
            self.row(offset),
            annotation()
        );
        self.synthesizer.enable_selector(selector, self.row(offset));
        Ok(())
    }

    fn name_column(&mut self, _: &(dyn Fn() -> String + '_), _: Column<Any>) {}

    fn assign_advice(
        &mut self,
        annotation: &(dyn Fn() -> String + '_),
        column: Column<Advice>,
        offset: usize,
        _: &mut (dyn FnMut() -> Option<F> + '_),
    ) -> Result<Cell, E> {
        log::debug!(
            "{}> Assigned advice to Adv:{} @ R{}+{offset}(={}) (note: {:?})",
            "-".repeat(self.group_depth),
            column.index(),
            *self.region_index,
            self.row(offset),
            annotation()
        );
        self.synthesizer
            .on_advice_assigned(column, self.row(offset));

        Ok(Cell {
            region_index: self.region_index,
            row_offset: offset,
            column: column.into(),
        })
    }

    fn assign_advice_from_constant(
        &mut self,
        annotation: &(dyn Fn() -> String + '_),
        column: Column<Advice>,
        offset: usize,
        constant: F,
    ) -> Result<Cell, E> {
        log::debug!(
            "{}> Assigned advice to Adv:{} @ R{}+{offset}(={}) with constant (note: {:?})",
            "-".repeat(self.group_depth),
            column.index(),
            *self.region_index,
            self.row(offset),
            annotation()
        );
        let advice = self.assign_advice(annotation, column, offset, &mut || Some(constant))?;
        self.constrain_constant(advice, constant)?;

        Ok(advice)
    }

    fn assign_advice_from_instance(
        &mut self,
        annotation: &(dyn Fn() -> String + '_),
        instance: Column<Instance>,
        row: usize,
        advice: Column<Advice>,
        offset: usize,
    ) -> Result<(Cell, Option<F>), E> {
        log::debug!(
            "{}> Assigned advice to Adv:{} @ R{}+{offset}(={}) with instance (Ins:{}, {row}) (note: {:?})",
            "-".repeat(self.group_depth),
            advice.index(),
            *self.region_index,
            self.row(offset),
            instance.index(),
            annotation()
        );
        let cell = self.assign_advice(annotation, advice, offset, &mut || None)?;

        self.synthesizer.copy(
            cell.column,
            self.row_at(cell.region_index, cell.row_offset),
            instance,
            row,
        );

        Ok((cell, None))
    }

    fn instance_value(&mut self, _: Column<Instance>, _: usize) -> Result<Option<F>, E> {
        Ok(None)
    }

    fn assign_fixed(
        &mut self,
        annotation: &(dyn Fn() -> String + '_),
        column: Column<Fixed>,
        offset: usize,
        to: &mut (dyn FnMut() -> Option<F> + '_),
    ) -> Result<Cell, E> {
        log::debug!(
            "{}> Assigned fixed to Fix:{} @ R{}+{offset}(={}) (note: {:?})",
            "-".repeat(self.group_depth),
            column.index(),
            *self.region_index,
            self.row(offset),
            annotation()
        );

        self.synthesizer.on_fixed_assigned(
            column,
            self.row(offset),
            to().ok_or(Error::MissingFixedValue(column.index(), offset).into())?,
        );

        Ok(Cell {
            region_index: self.region_index,
            row_offset: offset,
            column: column.into(),
        })
    }

    fn constrain_constant(&mut self, cell: Cell, constant: F) -> Result<(), E> {
        self.constants.push((constant, cell));
        Ok(())
    }

    fn constrain_equal(&mut self, left: Cell, right: Cell) -> Result<(), E> {
        log::debug!(
            "{}> {:?}(={}) === {:?}(={})",
            "-".repeat(self.group_depth),
            CellDbg(left),
            self.row_at(left.region_index, left.row_offset),
            CellDbg(right),
            self.row_at(right.region_index, right.row_offset),
        );
        self.synthesizer.copy(
            left.column,
            self.row_at(left.region_index, left.row_offset),
            right.column,
            self.row_at(right.region_index, right.row_offset),
        );

        Ok(())
    }
}

#[derive(Debug)]
struct ExtractionTable<'s, 'r, F: Field, E> {
    synthesizer: &'s mut Synthesizer<F>,
    used_columns: &'r [Column<Fixed>],
    /// maps from a fixed column to a pair (default value, vector saying which
    /// rows are assigned)
    #[allow(clippy::type_complexity)]
    pub default_and_assigned: HashMap<Column<Fixed>, (Option<Option<F>>, Vec<bool>)>,
    _error: PhantomData<E>,
}

impl<'s, 'r, F: Field, E> ExtractionTable<'s, 'r, F, E> {
    pub fn new(synthesizer: &'s mut Synthesizer<F>, used_columns: &'r [Column<Fixed>]) -> Self {
        Self {
            synthesizer,
            used_columns,
            default_and_assigned: HashMap::default(),
            _error: PhantomData,
        }
    }
}

impl<F: Field, E: From<Error>> TableLayouter<F, E> for ExtractionTable<'_, '_, F, E> {
    fn assign_cell(
        &mut self,
        _: &(dyn Fn() -> String + '_),
        column: Column<Fixed>,
        offset: usize,
        to: &mut (dyn FnMut() -> Option<F> + '_),
    ) -> Result<(), E> {
        if self.used_columns.contains(&column) {
            return Err(Error::TableError(TableError::UsedColumn(column)).into());
        }

        let entry = self.default_and_assigned.entry(column).or_default();

        let value = to();
        self.synthesizer.on_fixed_assigned(
            column,
            offset, // tables are always assigned starting at row 0
            value.ok_or(Error::MissingTableValue.into())?,
        );

        match (entry.0.is_none(), offset) {
            // Use the value at offset 0 as the default value for this table column.
            (true, 0) => entry.0 = Some(value),
            // Since there is already an existing default value for this table column,
            // the caller should not be attempting to assign another value at offset 0.
            (false, 0) => {
                return Err(Error::TableError(TableError::OverwriteDefault(
                    column,
                    format!("{:?}", entry.0.unwrap()),
                    format!("{value:?}"),
                ))
                .into());
            }
            _ => (),
        }
        if entry.1.len() <= offset {
            entry.1.resize(offset + 1, false);
        }
        entry.1[offset] = true;

        Ok(())
    }
}

struct CellDbg(Cell);

impl std::fmt::Debug for CellDbg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let cell = &self.0;
        write!(
            f,
            "({}:{}, R{}+{})",
            match cell.column.column_type() {
                Any::Advice => "Adv",
                Any::Fixed => "Fix",
                Any::Instance => "Ins",
            },
            cell.column.index(),
            *cell.region_index,
            cell.row_offset
        )
    }
}

#[allow(clippy::type_complexity)]
fn compute_table_lengths<F, E>(
    default_and_assigned: &HashMap<Column<Fixed>, (Option<Option<F>>, Vec<bool>)>,
) -> Result<usize, E>
where
    F: std::fmt::Debug,
    E: From<Error>,
{
    let column_lengths: Result<Vec<_>, Error> = default_and_assigned
        .iter()
        .map(|(col, (default_value, assigned))| {
            if default_value.is_none() || assigned.is_empty() {
                return Err(Error::TableError(TableError::ColumnNotAssigned(*col)));
            }
            if assigned.iter().all(|b| *b) {
                // All values in the column have been assigned
                Ok((col, assigned.len()))
            } else {
                Err(Error::TableError(TableError::ColumnNotAssigned(*col)))
            }
        })
        .collect();
    let column_lengths = column_lengths?;
    Ok(column_lengths
        .into_iter()
        .try_fold((None, 0), |acc, (col, col_len)| {
            if acc.1 == 0 || acc.1 == col_len {
                Ok((Some(*col), col_len))
            } else {
                let mut cols = [(*col, col_len), (acc.0.unwrap(), acc.1)];
                cols.sort();
                Err(Error::TableError(TableError::UnevenColumnLengths(
                    cols[0].0, cols[0].1, cols[1].0, cols[1].1,
                )))
            }
        })
        .map(|col_len| col_len.1)?)
}

/// The shape of a region. For a region at a certain index, we track
/// the set of columns it uses as well as the number of rows it uses.
#[derive(Clone, Debug)]
pub struct RegionShape {
    pub(super) region_index: RegionIndex,
    pub(super) columns: HashSet<RegionColumn>,
    pub(super) row_count: usize,
}

/// The virtual column involved in a region. This includes concrete columns,
/// as well as selectors that are not concrete columns at this stage.
#[derive(Eq, PartialEq, Copy, Clone, Debug, Hash)]
pub enum RegionColumn {
    /// Concrete column
    Column(Column<Any>),
    /// Virtual column representing a (boolean) selector
    Selector(usize),
}

impl From<Column<Any>> for RegionColumn {
    fn from(column: Column<Any>) -> RegionColumn {
        RegionColumn::Column(column)
    }
}

impl From<&dyn SelectorInfo> for RegionColumn {
    fn from(selector: &dyn SelectorInfo) -> RegionColumn {
        RegionColumn::Selector(selector.id())
    }
}

impl Ord for RegionColumn {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        match (self, other) {
            (Self::Column(a), Self::Column(b)) => a.cmp(b),
            (Self::Selector(a), Self::Selector(b)) => a.cmp(b),
            (Self::Column(_), Self::Selector(_)) => cmp::Ordering::Less,
            (Self::Selector(_), Self::Column(_)) => cmp::Ordering::Greater,
        }
    }
}

impl PartialOrd for RegionColumn {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl RegionShape {
    /// Create a new `RegionShape` for a region at `region_index`.
    pub fn new(region_index: RegionIndex) -> Self {
        RegionShape {
            region_index,
            columns: HashSet::default(),
            row_count: 0,
        }
    }

    /// Get the `region_index` of a `RegionShape`.
    pub fn region_index(&self) -> RegionIndex {
        self.region_index
    }

    /// Get a reference to the set of `columns` used in a `RegionShape`.
    pub fn columns(&self) -> &HashSet<RegionColumn> {
        &self.columns
    }

    /// Get the `row_count` of a `RegionShape`.
    pub fn row_count(&self) -> usize {
        self.row_count
    }
}

impl<F: Field, E> RegionLayouter<F, E> for RegionShape {
    fn enable_selector<'v>(
        &'v mut self,
        _: &'v (dyn Fn() -> String + 'v),
        selector: &dyn SelectorInfo,
        offset: usize,
    ) -> Result<(), E> {
        // Track the selector's fixed column as part of the region's shape.
        self.columns.insert(selector.into());
        self.row_count = cmp::max(self.row_count, offset + 1);
        Ok(())
    }

    fn assign_advice<'v>(
        &'v mut self,
        _: &'v (dyn Fn() -> String + 'v),
        column: Column<Advice>,
        offset: usize,
        _to: &'v mut (dyn FnMut() -> Option<F> + 'v),
    ) -> Result<Cell, E> {
        self.columns.insert(Column::<Any>::from(column).into());
        self.row_count = cmp::max(self.row_count, offset + 1);

        Ok(Cell {
            region_index: self.region_index,
            row_offset: offset,
            column: column.into(),
        })
    }

    fn assign_advice_from_constant<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Advice>,
        offset: usize,
        constant: F,
    ) -> Result<Cell, E> {
        // The rest is identical to witnessing an advice cell.
        self.assign_advice(annotation, column, offset, &mut || Some(constant))
    }

    fn assign_advice_from_instance<'v>(
        &mut self,
        _: &'v (dyn Fn() -> String + 'v),
        _: Column<Instance>,
        _: usize,
        advice: Column<Advice>,
        offset: usize,
    ) -> Result<(Cell, Option<F>), E> {
        self.columns.insert(Column::<Any>::from(advice).into());
        self.row_count = cmp::max(self.row_count, offset + 1);

        Ok((
            Cell {
                region_index: self.region_index,
                row_offset: offset,
                column: advice.into(),
            },
            None,
        ))
    }

    fn instance_value(&mut self, _instance: Column<Instance>, _row: usize) -> Result<Option<F>, E> {
        Ok(None)
    }

    fn assign_fixed<'v>(
        &'v mut self,
        _: &'v (dyn Fn() -> String + 'v),
        column: Column<Fixed>,
        offset: usize,
        _to: &'v mut (dyn FnMut() -> Option<F> + 'v),
    ) -> Result<Cell, E> {
        self.columns.insert(Column::<Any>::from(column).into());
        self.row_count = cmp::max(self.row_count, offset + 1);

        Ok(Cell {
            region_index: self.region_index,
            row_offset: offset,
            column: column.into(),
        })
    }

    fn name_column<'v>(
        &'v mut self,
        _annotation: &'v (dyn Fn() -> String + 'v),
        _column: Column<Any>,
    ) {
        // Do nothing
    }

    fn constrain_constant(&mut self, _cell: Cell, _constant: F) -> Result<(), E> {
        // Global constants don't affect the region shape.
        Ok(())
    }

    fn constrain_equal(&mut self, _left: Cell, _right: Cell) -> Result<(), E> {
        // Equality constraints don't affect the region shape.
        Ok(())
    }
}
