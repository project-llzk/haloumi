//! Types and traits for handling lookups from the client side.

use std::{borrow::Cow, sync::Arc};

use crate::{
    lookups::table::LookupTableGenerator,
    temps::{ExprOrTemp, Temps},
};
use ff::Field;
use haloumi_ir::stmt::IRStmt;

use haloumi_synthesis::lookups::Lookup;

/// Error type for lookups.
#[derive(Debug, Clone)]
pub struct LookupError(Arc<dyn std::error::Error + Send + Sync + 'static>);

impl<E: std::error::Error + Send + Sync + 'static> From<E> for LookupError {
    fn from(value: E) -> Self {
        LookupError(Arc::new(value))
    }
}

impl std::fmt::Display for LookupError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.0.as_ref(), f)
    }
}

/// Result type of a [`LookupCallbacks`] implementation.
pub type LookupResult<'syn, E> = Result<LookupStmt<'syn, E>, LookupError>;

/// Type for statements emitted by [`LookupCallbacks`].
pub type LookupStmt<'syn, E> = IRStmt<ExprOrTemp<Cow<'syn, E>>>;

/// Callback trait for defering to the client how to handle the logic of a lookup.
pub trait LookupCallbacks<F: Field, E> {
    /// Called on the list of lookups the circuit defines.
    ///
    /// While generating IR in a circuit with multiple lookups it could be the case that two
    /// lookups are related. For example, the circuit could call the same lookup in the same row
    /// for two values. The client that is extracting the circuit may want to handle these pairs of
    /// lookups in a special manner. This method enables the possibility for callbacks of handling
    /// the lookups in the circuit as a whole. With only calls to [`LookupCallbacks::on_lookup`]
    /// for each lookup is not possible to do that since the callback would receive each
    /// lookup indepedently.
    ///
    /// For example, consider a lookup for a sha256 implementation that returns the plain and
    /// spreaded version of a value (i.e. for 5 the spreaded value would be 17) and for each row where
    /// the lookup is enabled it invokes it twice (returning spreaded values `x` and `y`).
    /// For verifying with Picus, it helps annotating that if `x + 2*y` is deterministic, then `x`
    /// and `y` are deterministic. Emitting IR that encodes that axiom requires working with both
    /// lookups (each would be a different [`Lookup`]) at the same time.
    ///
    /// The implementation of this method is optional if the callback does not need to do any
    /// inter-lookup work and by default loops over the lookups and calls [`LookupCallbacks::on_lookup`] on each.
    fn on_lookups<'syn>(
        &self,
        lookups: &[&'syn Lookup<E>],
        tables: &[&dyn LookupTableGenerator<F>],
        temps: &mut Temps,
    ) -> LookupResult<'syn, E>
    where
        E: Clone,
    {
        lookups
            .iter()
            .zip(tables.iter())
            .map(|(lookup, table)| {
                let lookup_stmt = self.on_lookup(*lookup, *table, temps)?;
                let comment = LookupStmt::comment(format!("Lookup \"{}\"", lookup.name()));
                Ok(LookupStmt::seq([comment, lookup_stmt]))
            })
            .collect()
    }

    /// Called on each lookup the circuit defines.
    fn on_lookup<'syn>(
        &self,
        lookup: &'syn Lookup<E>,
        table: &dyn LookupTableGenerator<F>,
        temps: &mut Temps,
    ) -> LookupResult<'syn, E>
    where
        E: Clone;
}

pub(crate) struct DefaultLookupCallbacks;

#[derive(Debug, thiserror::Error)]
#[error("target circuit has lookups but their behavior was not specified")]
pub(crate) struct NoLookupError;

impl<F: Field, E: Clone> LookupCallbacks<F, E> for DefaultLookupCallbacks {
    fn on_lookup<'syn>(
        &self,
        _lookup: &'syn Lookup<E>,
        _table: &dyn LookupTableGenerator<F>,
        _temps: &mut Temps,
    ) -> LookupResult<'syn, E> {
        Err(NoLookupError.into())
    }
}
