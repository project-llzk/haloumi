use ff::{Field, PrimeField};
use haloumi_core::{
    constraints::CopyConstraint,
    expressions::ExprBuilder,
    table::{Any, Rotation, RotationExt as _},
};
use haloumi_ir::{Felt, meta::HasMeta as _, stmt::IRStmt};
use haloumi_synthesis::{
    eq_constraint::EqConstraint,
    groups::{Group, GroupCell},
    io::{AdviceIO, InstanceIO},
};

use crate::{
    ctx::GroupIRCtx,
    expressions::ScopedExpression,
    groups::bounds::{Bound, EqConstraintCheck, GroupBounds},
    regions::{RegionByIndex, region_row::RegionRow, row::Row},
    resolvers::FixedQueryResolver,
    utils,
};

/// Select the equality constraints that concern this group.
pub fn select_equality_constraints<F: Field, E>(
    group: &Group,
    ctx: &GroupIRCtx<'_, '_, '_, F, E>,
) -> Vec<EqConstraint<F>> {
    let bounds = GroupBounds::new(group, ctx.groups(), ctx.regions_by_index());

    ctx.syn()
        .constraints()
        .edges()
        .into_iter()
        .filter(|c| {
            log::debug!("Checking if eq constraint should go: {c:?}");
            match bounds.check_eq_constraint(c) {
                EqConstraintCheck::AnyToAny(left, l, right, r) => match (left, right) {
                    (Bound::Within, Bound::Within) => true,
                    (Bound::Within, Bound::ForeignIO) => true,
                    (Bound::ForeignIO, Bound::Within) => true,
                    (Bound::Within, Bound::IO) => true,
                    (Bound::IO, Bound::Within) => true,
                    (Bound::IO, Bound::IO) => true,
                    (Bound::IO, Bound::ForeignIO) => true,
                    (Bound::ForeignIO, Bound::IO) => true,
                    (Bound::ForeignIO, Bound::ForeignIO) => false,
                    (Bound::ForeignIO, Bound::Outside) => false,
                    (Bound::Outside, Bound::ForeignIO) => false,
                    (Bound::Outside, Bound::Outside) => false,
                    (Bound::IO, Bound::Outside) => false,
                    (Bound::Outside, Bound::IO) => false,
                    (Bound::Within, Bound::Outside) => matches!(r.0.column_type(), Any::Fixed),
                    (Bound::Outside, Bound::Within) => matches!(l.0.column_type(), Any::Fixed),
                },
                EqConstraintCheck::FixedToConst(bound) => match bound {
                    Bound::Within | Bound::Outside => true,
                    _ => unreachable!(),
                },
            }
        })
        .collect()
}

/// Generates constraint expressions for the equality constraints.
///
/// This function accepts an iterator of equality constraints to facilitate
/// filtering the equality constraints of a group from the global equality constraints graph.
pub fn inter_region_constraints<'e, 's, F, E>(
    constraints: impl IntoIterator<Item = EqConstraint<F>>,
    advice_io: &'s AdviceIO,
    instance_io: &'s InstanceIO,
    fixed_query_resolver: &'s dyn FixedQueryResolver<F>,
) -> Vec<IRStmt<ScopedExpression<'e, 's, F, E>>>
where
    F: PrimeField,
    E: Clone + ExprBuilder<F>,
{
    constraints
        .into_iter()
        .map(|constraint| match constraint {
            EqConstraint::AnyToAny(from, from_row, to, to_row) => {
                let lhs = ScopedExpression::new(
                    from.query_cell(Rotation::cur()),
                    Row::new(from_row, advice_io, instance_io, fixed_query_resolver),
                );
                let rhs = ScopedExpression::new(
                    to.query_cell(Rotation::cur()),
                    Row::new(to_row, advice_io, instance_io, fixed_query_resolver),
                );
                let mut stmt = IRStmt::eq(lhs, rhs);
                stmt.meta_mut()
                    .at_copy_constraint(CopyConstraint::Cells(from, from_row, to, to_row));
                stmt
            }
            EqConstraint::FixedToConst(column, row, f) => {
                let lhs = ScopedExpression::new(
                    column.query_cell(Rotation::cur()),
                    Row::new(row, advice_io, instance_io, fixed_query_resolver),
                );
                let rhs = ScopedExpression::new(
                    E::constant(f),
                    Row::new(row, advice_io, instance_io, fixed_query_resolver),
                );
                let mut stmt = IRStmt::eq(lhs, rhs);
                stmt.meta_mut().at_copy_constraint(CopyConstraint::Fixed(
                    column,
                    row,
                    Felt::new(f),
                ));
                stmt
            }
        })
        .collect()
}

/// Creates a resolver based on the type of cell.
fn mk_resolver<'r, 'io, 'fq, F: Field>(
    cell: &GroupCell,
    advice_io: &'io AdviceIO,
    instance_io: &'io InstanceIO,
    fqr: &'fq dyn FixedQueryResolver<F>,
    regions_by_index: &RegionByIndex<'r>,
) -> Result<RegionRow<'r, 'io, 'fq, F>, Row<'io, 'fq, F>> {
    cell.region_index()
        .and_then(|idx| {
            let region = regions_by_index[&idx];
            Some((region, region.start()?))
        })
        .ok_or_else(|| {
            // No region, so we return Row.
            Row::new(cell.row(), advice_io, instance_io, fqr)
        })
        .map(|(region, start)| {
            RegionRow::new(region, start + cell.row(), advice_io, instance_io, fqr)
        })
}

macro_rules! mk_side {
    (@inner $io:ident, $cell:expr $(, $args:expr)* $(,)?) => {
        match mk_resolver($cell, $($args ,)*) {
            Ok(region_row) => ScopedExpression::new($cell.to_expr(), region_row.$io()),
            Err(row) => ScopedExpression::new($cell.to_expr(), row.$io()),
        }
    };
    (@lhs $cell:expr $(, $args:expr)* $(,)?) => {
        mk_side!(@inner prioritize_inputs, $cell, $($args ,)*)
    };
    (@rhs $cell:expr $(, $args:expr)* $(,)?) => {
        mk_side!(@inner prioritize_outputs, $cell, $($args ,)*)
    };
}

/// Searches for cells that are annotated as both inputs and outputs and generates constraints that
/// connects the input variable with the output variable.
///
/// Returns a list of statements with the constraints.
pub fn search_double_annotated<'e, 'io, 'syn, 'sco, F, E>(
    group: &Group,
    advice_io: &'io AdviceIO,
    instance_io: &'io InstanceIO,
    fqr: &'syn dyn FixedQueryResolver<F>,
    regions_by_index: &RegionByIndex<'syn>,
) -> Vec<IRStmt<ScopedExpression<'e, 'sco, F, E>>>
where
    'syn: 'sco,
    'io: 'sco + 'syn,
    F: Field,
    E: Clone + ExprBuilder<F>,
{
    utils::product(group.inputs(), group.outputs())
        .filter_map(|(i, o)| {
            if i != o {
                return None;
            }

            let lhs = mk_side!(@lhs i, advice_io, instance_io, fqr, regions_by_index);
            let rhs = mk_side!(@rhs o, advice_io, instance_io, fqr, regions_by_index);
            Some(IRStmt::eq(lhs, rhs))
        })
        .collect()
}
