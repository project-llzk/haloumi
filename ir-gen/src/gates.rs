//! Types and traits related to IR generation of PLONK gates.

use std::{fmt, ops::Range};

use ff::{Field, PrimeField};
use haloumi_core::{
    expressions::{EvaluableExpr, ExprBuilder, ExpressionInfo},
    table::RegionIndex,
};
use haloumi_synthesis::{
    gates::Gate,
    io::{AdviceIO, InstanceIO},
    regions::RegionData,
};

use crate::{
    expressions::{ScopedExpression, constant_folding::ConstantFolding},
    regions::region_row::RegionRow,
    resolvers::FixedQueryResolver,
};

pub mod callbacks;
pub mod rewrite;

/// Error raise by [`GateScope`].
#[derive(Debug, thiserror::Error)]
#[error("row {row} is not within the rows of the scope [{start}, {end}]")]
pub struct GateScopeError {
    row: usize,
    start: usize,
    end: usize,
}

/// Result of constant-folding an expression for `n` rows.
pub type FoldedExpressions<E> = Vec<(usize, E)>;

/// Scope in which a gate is being called
pub struct GateScope<'syn, 'io, F, E>
where
    F: Field,
{
    gate: &'syn Gate<E>,
    region: RegionData<'syn>,
    /// The bounds are [start,end).
    row_bounds: (usize, usize),
    advice_io: &'io AdviceIO,
    instance_io: &'io InstanceIO,
    fqr: &'syn dyn FixedQueryResolver<F>,
}

impl<'syn, 'io, F: Field, E> GateScope<'syn, 'io, F, E> {
    /// Constructs a new gate scope.
    ///
    /// Since this class is passed to a callback its constructor is protected.
    pub(crate) fn new(
        gate: &'syn Gate<E>,
        region: RegionData<'syn>,
        row_bounds: (usize, usize),
        advice_io: &'io AdviceIO,
        instance_io: &'io InstanceIO,
        fqr: &'syn dyn FixedQueryResolver<F>,
    ) -> Self {
        Self {
            gate,
            region,
            row_bounds,
            advice_io,
            instance_io,
            fqr,
        }
    }

    pub(crate) fn region(&self) -> RegionData<'syn> {
        self.region
    }

    pub(crate) fn region_row(
        &self,
        row: usize,
    ) -> Result<RegionRow<'syn, 'io, 'syn, F>, GateScopeError> {
        if !self.rows().contains(&row) {
            return Err(GateScopeError {
                row,
                start: self.start_row(),
                end: self.end_row(),
            });
        }
        Ok(RegionRow::new(
            self.region(),
            row,
            self.advice_io,
            self.instance_io,
            self.fqr,
        ))
    }

    pub(crate) fn region_rows(&self) -> impl Iterator<Item = RegionRow<'syn, 'io, 'syn, F>> {
        self.rows().map(|row| {
            RegionRow::new(
                self.region(),
                row,
                self.advice_io,
                self.instance_io,
                self.fqr,
            )
        })
    }

    /// Returns the name assigned to the gate.
    pub fn gate_name(&self) -> &str {
        self.gate.name()
    }

    /// Returns the polynomials defined during circuit configuration.
    pub fn polynomials(&self) -> &'syn [E] {
        self.gate.polynomials()
    }

    /// Returns the list of polynomials once per row. The polynomials per row are constant-folded
    /// first.
    pub fn polynomials_per_row(
        &self,
    ) -> Result<Vec<(&'syn E, FoldedExpressions<E>)>, GateScopeError>
    where
        E: Clone + EvaluableExpr<F> + ExpressionInfo + ExprBuilder<F>,
    {
        self.polynomials()
            .iter()
            .map(|e| {
                let rows = self
                    .rows()
                    .map(|row| {
                        let folded = self.fold_polynomial_in_row(e, row)?;
                        Ok((row, folded))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok((e, rows))
            })
            .collect()
    }

    fn fold_polynomial_in_row(&self, e: &E, row: usize) -> Result<E, GateScopeError>
    where
        E: Clone + EvaluableExpr<F> + ExpressionInfo + ExprBuilder<F>,
    {
        let region_row = self.region_row(row)?;
        let scoped = ScopedExpression::from_ref(e, region_row);
        Ok(ConstantFolding::new(scoped.resolvers()).constant_fold(scoped.as_ref()))
    }

    /// Returns the name of the region where this gate was called.
    pub fn region_name(&self) -> &str {
        self.region.name()
    }

    /// Returns the index of the region where this gate was called.
    pub fn region_index(&self) -> Option<RegionIndex> {
        self.region.index()
    }

    /// Returns a string summary of the region.
    ///
    /// It's intended for debugging purposes and the
    /// text representation should not be relied upon.
    pub fn region_header(&self) -> impl ToString {
        self.region.header()
    }

    /// Returns the first row of the region.
    pub fn start_row(&self) -> usize {
        self.row_bounds.0
    }

    /// The last row of the region.
    pub fn end_row(&self) -> usize {
        let end = self.row_bounds.1;
        if end == 0 {
            return end;
        }
        end - 1
    }

    /// Returns the rows in the region.
    pub fn rows(&self) -> Range<usize> {
        (self.row_bounds.0)..(self.row_bounds.1)
    }
}

impl<F: Field, E> Copy for GateScope<'_, '_, F, E> {}

impl<F: Field, E> Clone for GateScope<'_, '_, F, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<F: PrimeField, E: fmt::Debug> fmt::Debug for GateScope<'_, '_, F, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("GateScope")
            .field("gate", &self.gate)
            .field("region", &self.region)
            .field("row_bounds", &self.row_bounds)
            .field("advice_io", &self.advice_io)
            .field("instance_io", &self.instance_io)
            .finish()
    }
}
