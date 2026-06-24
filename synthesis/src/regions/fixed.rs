use std::{
    collections::{HashMap, HashSet},
    ops::RangeFrom,
};

use ff::Field;

use crate::error::Error;
use haloumi_core::{query::Fixed, table::Column};

type BlanketFills<F> = Vec<(RangeFrom<usize>, F)>;

/// Represents a collection of fixed values, usually representing a lookup table.
#[derive(Default, Debug, Clone)]
pub struct FixedData<F: Copy + std::fmt::Debug + Default> {
    /// Constant values assigned to fixed columns in the region.
    fixed: HashMap<usize, HashMap<usize, F>>,
    /// Set of columns for which there is data.
    columns: HashSet<Column<Fixed>>,
    /// Represents the circuit filling rows with a single value.
    /// Row start offsets are maintained in chronological order, so when
    /// querying a row the latest that matches is the correct value.
    blanket_fills: HashMap<usize, BlanketFills<F>>,
}

pub type FixedAssigned<F> = HashMap<(usize, usize), F>;
pub type FixedBlanket<F> = HashMap<usize, BlanketFills<F>>;

impl<F: Copy + std::fmt::Debug + Default> FixedData<F> {
    pub(crate) fn take(self) -> (FixedAssigned<F>, FixedBlanket<F>) {
        (
            self.fixed
                .into_iter()
                .flat_map(|(col, values)| {
                    values
                        .into_iter()
                        .map(move |(row, value)| ((col, row), value))
                })
                .collect(),
            self.blanket_fills,
        )
    }

    pub(crate) fn blanket_fill(&mut self, column: Column<Fixed>, row: usize, value: F) {
        self.columns.insert(column);
        self.blanket_fills
            .entry(column.index())
            .or_default()
            .push((row.., value));
    }

    pub(crate) fn assign_fixed(&mut self, fixed: Column<Fixed>, row: usize, value: F)
    where
        F: Field,
    {
        log::debug!(
            "Recording fixed assignment @ col = {}, row = {row}, value = {value:?}",
            fixed.index()
        );
        self.columns.insert(fixed);
        self.fixed
            .entry(fixed.index())
            .or_default()
            .insert(row, value);
    }

    fn resolve_from_blanket_fills(&self, column: usize, row: usize) -> Option<F>
    where
        F: Field,
    {
        self.blanket_fills
            .get(&column)
            .and_then(|values| values.iter().rfind(|(range, _)| range.contains(&row)))
            .map(|(_, v)| *v)
    }

    /// Resolves the fixed value at the given cell.
    ///
    /// If the value was not assigned returns `F::ZERO`.
    pub fn resolve_fixed(&self, column: usize, row: usize) -> F
    where
        F: Field,
    {
        self.fixed
            .get(&column)
            .and_then(|cols| cols.get(&row))
            .inspect(|v| log::debug!(" For ({column}, {row}) we got value {v:?}",))
            .cloned()
            .or_else(|| self.resolve_from_blanket_fills(column, row))
            // Default to zero if all else fails
            .unwrap_or(F::ZERO)
    }

    /// Returns a copy of itself by selecting only the given columns.
    ///
    /// If a column is not in the fixed data returns an error.
    pub(crate) fn subset(&self, columns: HashSet<Column<Fixed>>) -> Result<Self, Error> {
        let mut selected = Self::default();
        if !self.columns.is_superset(&columns) {
            return Err(Error::InvalidTableColumns);
        }
        selected.columns = columns;
        for col in &selected.columns {
            if let Some(fill) = self.blanket_fills.get(&col.index()) {
                selected.blanket_fills.insert(col.index(), fill.clone());
            }
            if let Some(values) = self.fixed.get(&col.index()) {
                selected.fixed.insert(col.index(), values.clone());
            }
        }

        Ok(selected)
    }
}

//impl<F: Field> FixedQueryResolver<F> for FixedData<F> {
//    fn resolve_query(&self, query: &dyn QueryInfo<Kind = Fixed>, row: usize) -> anyhow::Result<F> {
//        Ok(self.resolve_fixed(query.column_index(), row))
//    }
//}
