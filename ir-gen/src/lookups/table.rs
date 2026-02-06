//! Types related to the tables read by lookups.

use ff::Field;
use haloumi_synthesis::{SynthesizedCircuit, lookups::Lookup};
use std::{cell::LazyCell, ops::Index, sync::Arc};

use haloumi_core::{
    expressions::{ExpressionInfo, ExpressionTypes},
    info_traits::QueryInfo,
    query::Fixed,
};

/// Table generation error.
#[derive(Debug, thiserror::Error, Clone)]
#[error("failed to generate the table: {0}")]
pub struct TableError(Arc<dyn std::error::Error + Sync + Send + 'static>);

/// Type alias for a result of creating a boxed slice representing the rows in the table.
pub type LookupTableBox<F> = Result<Box<[LookupTableRow<F>]>, TableError>;

/// Implementations of this trait compute the complete table for a lookup.
pub trait LookupTableGenerator<F> {
    /// Returns the lookup table.
    fn table(&self) -> Result<&[LookupTableRow<F>], TableError>;
}

/// Lazy lookup table generator.
pub(crate) struct LazyLookupTableGenerator<F, FN>
where
    FN: FnOnce() -> LookupTableBox<F>,
{
    table: LazyCell<LookupTableBox<F>, FN>,
}

impl<F, FN> LazyLookupTableGenerator<F, FN>
where
    FN: FnOnce() -> LookupTableBox<F>,
{
    fn new(f: FN) -> Self {
        Self {
            table: LazyCell::new(f),
        }
    }
}

impl<F, FN> LookupTableGenerator<F> for LazyLookupTableGenerator<F, FN>
where
    F: Field,
    FN: FnOnce() -> LookupTableBox<F>,
{
    fn table(&self) -> Result<&[LookupTableRow<F>], TableError> {
        (*self.table)
            .as_ref()
            .map(AsRef::as_ref)
            .map_err(Clone::clone)
    }
}

impl<F, FN: FnOnce() -> LookupTableBox<F>> std::fmt::Debug for LazyLookupTableGenerator<F, FN> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LazyLookupTableGenerator").finish()
    }
}

/// Represents a row in the lookup table that can be indexed by the columns participating in the
/// lookup.
#[derive(Debug)]
pub struct LookupTableRow<F> {
    // Maps the n-th index of the slice to the n-th column
    columns: Vec<usize>,
    table: Vec<F>,
}

impl<F: Copy> LookupTableRow<F> {
    pub(crate) fn new(columns: &[usize], table: Vec<F>) -> Self {
        Self {
            columns: columns.to_vec(),
            table,
        }
    }
}

impl<F> LookupTableRow<F> {
    fn col_to_index(&self, col: usize) -> Option<usize> {
        self.columns.iter().find(|c| **c == col).copied()
    }
}

impl<F, Q: QueryInfo<Kind = Fixed>> Index<Q> for LookupTableRow<F> {
    type Output = F;

    fn index(&self, index: Q) -> &Self::Output {
        let index = self.col_to_index(index.column_index()).unwrap_or_else(|| {
            panic!(
                "Can't index with a column outside of the valid range {:?}",
                self.columns
            )
        });
        &self.table[index]
    }
}

#[derive(Debug, thiserror::Error)]
pub(crate) enum TableGenError {
    #[error("could not get values from table")]
    NotFound,
    #[error("consistency check failed: Lookup has {lookup} columns but table yielded {table}")]
    InconsistentLookup { lookup: usize, table: usize },
    #[error(transparent)]
    Synthesis(#[from] haloumi_synthesis::error::Error),
}

pub(crate) fn tables_for_lookup<F, E>(
    syn: &SynthesizedCircuit<F, E>,
    l: &Lookup<E>,
) -> LazyLookupTableGenerator<F, impl FnOnce() -> LookupTableBox<F>>
where
    F: Field,
    E: ExpressionInfo,
{
    LazyLookupTableGenerator::new(move || {
        tables_for_lookup_impl(syn, l)
            .map(|table| table.into_boxed_slice())
            .map_err(|e| TableError(Arc::new(e)))
    })
}

pub(crate) fn tables_for_lookup_impl<F, E>(
    syn: &SynthesizedCircuit<F, E>,
    l: &Lookup<E>,
) -> Result<Vec<LookupTableRow<F>>, TableGenError>
where
    E: ExpressionInfo,
    F: Field,
{
    fn transpose<T>(v: Vec<Vec<T>>) -> Vec<Vec<T>> {
        assert!(!v.is_empty());
        let len = v[0].len();
        let mut iters: Vec<_> = v.into_iter().map(|n| n.into_iter()).collect();
        (0..len)
            .map(|_| {
                iters
                    .iter_mut()
                    .map(|n| n.next().unwrap())
                    .collect::<Vec<T>>()
            })
            .collect()
    }

    fn find_table<F, E>(
        syn: &SynthesizedCircuit<F, E>,
        q: &[E::FixedQuery],
    ) -> Result<Vec<Vec<F>>, TableGenError>
    where
        E: ExpressionTypes,
        F: Field,
    {
        Ok(syn
            .tables()
            .iter()
            .find_map(|table| table.get_rows(q))
            .ok_or_else(|| TableGenError::NotFound)??)
    }

    let q = l.table_queries()?;
    // For each table region look if they have the columns we are looking for and
    // collect all the fixed values
    let columns = q.iter().map(|q| q.column_index()).collect::<Vec<_>>();
    let table = find_table(syn, &q)?;
    if q.len() != table.len() {
        return Err(TableGenError::InconsistentLookup {
            lookup: q.len(),
            table: table.len(),
        });
    }

    // The table needs to be transposed from [row,col] to [col,row].
    Ok(transpose(table)
        .into_iter()
        .map(|row| LookupTableRow::new(&columns, row))
        .collect())
}
