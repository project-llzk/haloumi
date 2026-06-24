//! Structs for handling the IR of groups of regions inside the circuit.

use ff::{Field, PrimeField};
use haloumi_core::{
    expressions::{EvaluableExpr, ExprBuilder, ExpressionInfo},
    slot::Slot,
};
use haloumi_ir::{
    cell::{CellError, CellRef},
    expr::IRAexpr,
    groups::IRGroup,
    stmt::IRStmt,
};
use haloumi_synthesis::{
    groups::Group,
    io::{AdviceIO, InstanceIO},
    regions::RegionData,
};

use crate::{
    ctx::{AdviceCells, GroupIRCtx, IRCtx},
    error::Error,
    expressions::{ExpressionError, ExpressionInRow, ScopedExpression},
    gates::{GateScopeError, rewrite::RewriteError},
    groups::{
        callsite::{CallsiteGenError, new_callsite},
        constraints::{
            inter_region_constraints, search_double_annotated, select_equality_constraints,
        },
        gates::lower_gates,
        lookups::codegen_lookup_invocations,
    },
    lookups::{callbacks::LookupError, table::TableGenError},
    regions::region_row::RegionRow,
    resolvers::FixedQueryResolver,
    temps::ExprOrTemp,
};

pub(crate) mod bounds;
pub mod callsite;
mod constraints;
mod gates;
mod lookups;

pub type UnresolvedIRGroup<'syn, 'sco, F, E> =
    IRGroup<ExprOrTemp<ScopedExpression<'syn, 'sco, F, E>>>;

#[derive(Debug, thiserror::Error)]
pub(crate) enum IRGroupGenError {
    #[error(transparent)]
    Callsite(#[from] CallsiteGenError),
    #[error("region does not have a base")]
    RegionWithoutBase,
    #[error("cell reference {0:?} was not found in any region")]
    CellNotFound(CellRef),
    #[error(transparent)]
    GateScope(#[from] GateScopeError),
    #[error(transparent)]
    TableGen(#[from] TableGenError),
    #[error("failed to generate ir for gate: {0}")]
    Rewrite(RewriteError),
    #[error(transparent)]
    Cell(#[from] CellError),
    #[error("failed to generate ir for lookup: {0}")]
    Lookup(LookupError),
    #[error("Gate '{name}' on region {region_index} '{region_name}' did not match any pattern")]
    UnmatchedGate {
        name: String,
        region_index: String,
        region_name: String,
    },
}

impl From<IRGroupGenError> for Error {
    fn from(value: IRGroupGenError) -> Self {
        Error::new(value)
    }
}

impl From<LookupError> for IRGroupGenError {
    fn from(value: LookupError) -> Self {
        Self::Lookup(value)
    }
}

impl From<RewriteError> for IRGroupGenError {
    fn from(value: RewriteError) -> Self {
        Self::Rewrite(value)
    }
}

pub(super) fn new_group<'cb, 'syn, 'ctx, 'sco, F, E>(
    group: &'syn Group,
    id: usize,
    ctx: &GroupIRCtx<'cb, '_, 'syn, F, E>,
    advice_io: &'ctx AdviceIO,
    instance_io: &'ctx InstanceIO,
) -> Result<UnresolvedIRGroup<'syn, 'sco, F, E>, IRGroupGenError>
where
    F: Ord,
    E: ExprBuilder<F> + ExpressionInfo + EvaluableExpr<F>,
    'cb: 'sco + 'syn,
    'syn: 'sco,
    'ctx: 'sco + 'syn,
    F: PrimeField,
    E: Clone + std::fmt::Debug,
{
    log::debug!("Lowering call-sites for group {:?}", group.name());
    let callsites = {
        group
            .children(ctx.groups())
            .into_iter()
            .enumerate()
            .map(|(call_no, (callee_id, callee))| {
                new_callsite(callee, callee_id, ctx, call_no, advice_io, instance_io)
            })
            .collect::<Result<Vec<_>, _>>()?
    };

    log::debug!("Lowering gates for group {:?}", group.name());
    let gates = IRStmt::seq(
        lower_gates(
            ctx.syn().gates(),
            &group.regions(),
            ctx.patterns(),
            advice_io,
            instance_io,
            ctx.syn().fixed_data(),
            ctx.generate_debug_comments(),
        )?
        .into_iter()
        .map(|stmt| stmt.map(&mut ExprOrTemp::Expr)),
    );

    log::debug!(
        "Lowering inter region equality constraints for group {:?}",
        group.name()
    );
    let eq_constraints = select_equality_constraints(group, ctx);

    let mut eq_constraints = inter_region_constraints(
        eq_constraints,
        advice_io,
        instance_io,
        ctx.syn().fixed_data(),
    );
    let extra_eq_constraints = search_double_annotated(
        group,
        advice_io,
        instance_io,
        ctx.syn().fixed_data(),
        ctx.regions_by_index(),
    );
    eq_constraints.extend(extra_eq_constraints);
    let eq_constraints = IRStmt::seq(
        eq_constraints
            .into_iter()
            .map(|stmt| stmt.map(&mut ExprOrTemp::Expr)),
    );

    log::debug!("Lowering lookups for group {:?}", group.name());
    let lookups = IRStmt::seq(codegen_lookup_invocations(
        ctx.syn(),
        &region_rows(group, advice_io, instance_io, ctx.syn().fixed_data()),
        ctx.lookup_cb(),
        ctx.generate_debug_comments(),
    )?);

    Ok(IRGroup::new(group.name().to_owned(), id)
        .with_input_count(instance_io.inputs().len() + advice_io.inputs().len())
        .with_output_count(instance_io.outputs().len() + advice_io.outputs().len())
        .with_key(group.key())
        .with_callsites(callsites)
        .with_gates(gates)
        .with_copy_constraints(eq_constraints)
        .with_lookups(lookups)
        .do_debug_comments(ctx.generate_debug_comments()))
}

/// Returns the regions' rows
fn region_rows<'a, 'io, 'fq, F: Field>(
    group: &'a Group,
    advice_io: &'io AdviceIO,
    instance_io: &'io InstanceIO,
    fqr: &'fq dyn FixedQueryResolver<F>,
) -> Vec<RegionRow<'a, 'io, 'fq, F>> {
    group
        .regions()
        .into_iter()
        .flat_map(move |r| {
            r.rows()
                .map(move |row| RegionRow::new(r, row, advice_io, instance_io, fqr))
        })
        .collect()
}

/// Injects IR into the group scoped by the region.
pub(super) fn inject_ir<'cb, 'syn, 'ctx, 'sco, F, E>(
    group: &mut UnresolvedIRGroup<'syn, 'sco, F, E>,
    region: RegionData<'syn>,
    ir: IRStmt<ExpressionInRow<'syn, E, F>>,
    advice_io: &'ctx AdviceIO,
    instance_io: &'ctx InstanceIO,
    fqr: &'syn dyn FixedQueryResolver<F>,
) -> Result<(), ExpressionError>
where
    'cb: 'sco + 'syn,
    'syn: 'sco,
    'ctx: 'sco + 'syn,
    F: Field,
    E: Clone + std::fmt::Debug,
{
    group.inject(ir.try_map(&mut |expr| {
        expr.scoped_in_region_row(region, advice_io, instance_io, fqr)
            .map(ExprOrTemp::Expr)
    })?);
    Ok(())
}

/// Relativizes advice cells to the regions in the group.
///
/// It is used for improving the detection of equivalent groups.
pub fn relativize_eq_constraints(
    group: &mut IRGroup<IRAexpr>,
    ctx: &IRCtx,
) -> Result<(), IRGroupGenError> {
    log::debug!("//===--------------------------------------------------------------===//");
    log::debug!(
        "// BEGIN Relativizing copy constraints for group '{}'",
        group.name()
    );
    log::debug!("//===--------------------------------------------------------------===//");
    log::debug!("COPY CONSTRAINTS:\n{:?}", group.eq_constraints_mut());
    let res = group.eq_constraints_mut().try_map_inplace(&mut |expr| {
        log::debug!("  Copy constraint arg: {expr:?}");
        expr.try_map_io(&|io| match io {
            Slot::Advice(cell) => {
                *cell = try_relativize_advice_cell(*cell, ctx.advice_cells().values())?;
                Ok(())
            }
            _ => Ok(()),
        })
    });

    log::debug!("//===--------------------------------------------------------------===//");
    log::debug!(
        "// END   Relativizing copy constraints for group '{}' (ok? {})",
        group.name(),
        res.is_ok()
    );
    log::debug!("//===--------------------------------------------------------------===//");
    res
}

/// Searches to what region the advice cell belongs to and converts it to a relative reference from
/// that region.
///
/// Fails if the advice cell could not be found in any region.
fn try_relativize_advice_cell<'a>(
    cell: CellRef,
    regions: impl IntoIterator<Item = &'a AdviceCells>,
) -> Result<CellRef, IRGroupGenError> {
    if !cell.is_absolute() {
        return Ok(cell);
    }
    for region in regions {
        if !region.contains_advice_cell(cell.col(), cell.row()) {
            continue;
        }
        let start = region.start().ok_or_else(
            || IRGroupGenError::RegionWithoutBase, //anyhow::anyhow!("Region does not have a base")
        )?;
        return Ok(cell.try_relativize(start)?);
    }

    Err(IRGroupGenError::CellNotFound(cell))
}

/// If the given statement is not empty prepends a comment
/// with contextual information.
#[inline]
pub fn prepend_comment<E>(
    stmt: IRStmt<E>,
    comment: impl FnOnce() -> IRStmt<E>,
    generate_debug_comments: bool,
) -> IRStmt<E> {
    if stmt.is_empty() || !generate_debug_comments {
        return stmt;
    }
    [comment(), stmt].into_iter().collect()
}
