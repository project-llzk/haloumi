//! Types for working with circuits that are in the _unresolved_ stage.

use ff::{Field, PrimeField};
use haloumi_core::{expressions::EvaluableExpr, table::RegionIndex};
use haloumi_ir::diagnostics::Diagnostic;
use haloumi_ir::{
    IRCircuit, Prime, diagnostics::DiagnosticsError, expr::IRAexpr, groups::IRGroup,
    meta::HasMeta as _, stmt::IRStmt, traits::Validatable,
};
use haloumi_synthesis::SynthesizedCircuit;

use crate::{
    circuit::resolved::{ResolvedCtx, ResolvedIRCircuit},
    ctx::IRCtx,
    error::Error,
    expressions::{ExpressionInRow, ScopedExpression, UnresolvedExpr},
    groups::{self, relativize_eq_constraints},
    regions::region_data,
    temps::ExprOrTemp,
};

/// Circuit that has not resolved its expressions yet and is still tied to the lifetime
/// of the [`SynthesizedCircuit`] and the [`IRGenerationUser`](crate::IRGenerationUser).
#[derive(Debug)]
pub struct UnresolvedIRCircuit<'ctx, 'syn, 'sco, F, E>(
    IRCircuit<UnresolvedExpr<'syn, 'sco, F, E>, (&'ctx IRCtx, Vec<usize>)>,
)
where
    E: Clone,
    F: Field;

impl<'ctx, 'syn, 'sco, F, E> UnresolvedIRCircuit<'ctx, 'syn, 'sco, F, E>
where
    F: PrimeField,
    'syn: 'sco,
    'ctx: 'sco + 'syn,
    E: Clone + std::fmt::Debug,
{
    pub(crate) fn new(
        ctx: &'ctx IRCtx,
        groups: Vec<IRGroup<UnresolvedExpr<'syn, 'sco, F, E>>>,
        regions_to_groups: Vec<usize>,
    ) -> Self {
        Self(IRCircuit::new(groups, (ctx, regions_to_groups)))
    }

    fn group(
        &mut self,
        index: usize,
    ) -> &mut IRGroup<ExprOrTemp<ScopedExpression<'syn, 'sco, F, E>>> {
        &mut self.0.body_mut()[index]
    }

    fn region_to_groups(&self, index: RegionIndex) -> usize {
        self.0.context().1[*index]
    }

    fn ctx(&self) -> &'ctx IRCtx {
        self.0.context().0
    }

    /// Injects the IR into the specific regions
    pub fn inject_ir<R>(
        &mut self,
        ir: impl IntoIterator<Item = (R, IRStmt<ExpressionInRow<'syn, E, F>>)>,
        syn: &'syn SynthesizedCircuit<F, E>,
    ) -> Result<(), Error>
    where
        R: Into<RegionIndex>,
    {
        let regions = region_data(syn);
        for (index, mut stmt) in ir {
            let index = index.into();
            let region = regions[&index];
            let group_idx = self.region_to_groups(index);
            let ctx = self.ctx();
            let group = self.group(group_idx);
            let stmt_index = group.injected_count();
            stmt.meta_mut().at_inject(index, Some(stmt_index));
            stmt.propagate_meta();
            groups::inject_ir(
                group,
                region,
                stmt,
                ctx.advice_io_of_group(group_idx),
                ctx.instance_io_of_group(group_idx),
                syn.fixed_data(),
            )?;
        }
        Ok(())
    }

    /// Resolves the IR.
    pub fn resolve(self) -> Result<ResolvedIRCircuit, Error>
    where
        E: EvaluableExpr<F>,
    {
        let ctx = self.ctx().clone();
        let mut groups = self
            .0
            .take_body()
            .into_iter()
            .map(|g| g.try_map(&mut IRAexpr::try_from))
            .collect::<Result<Vec<_>, _>>()?;
        for group in &mut groups {
            relativize_eq_constraints(group, &ctx)?;
        }
        Ok(ResolvedIRCircuit(IRCircuit::new(
            groups,
            ResolvedCtx(ctx, Prime::new::<F>()),
        )))
    }

    /// Validates the IR, returning errors if it failed.
    pub fn validate(&self) -> Result<(), Error>
    where
        Circuit<'ctx, 'syn, 'sco, F, E>: Validatable<Context = ()>,
        <Circuit<'ctx, 'syn, 'sco, F, E> as Validatable>::Diagnostic:
            Diagnostic + Send + Sync + 'static,
    {
        self.0
            .validate_with_context(&())
            .map(|_| {})
            .map_err(move |errors| UnresolvedIRError {
                count: errors.len(),
                errors: DiagnosticsError::from_iter(errors),
            })?;
        Ok(())
    }
}

type Circuit<'ctx, 'syn, 'sco, F, E> =
    IRCircuit<UnresolvedExpr<'syn, 'sco, F, E>, (&'ctx IRCtx, Vec<usize>)>;

/// Unresolved IR error raised by [`UnresolvedIRCircuit::validate`].
#[derive(Debug, thiserror::Error)]
#[error("validation of unresolved IR failed with {count} errors: \n{errors}")]
pub struct UnresolvedIRError {
    /// Number of errors.
    count: usize,
    /// List of errors.
    errors: DiagnosticsError,
}

impl From<UnresolvedIRError> for Error {
    fn from(value: UnresolvedIRError) -> Self {
        Error::new(value)
    }
}
