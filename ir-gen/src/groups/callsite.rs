//! Structs for handling calls between groups.

use crate::regions::{region_row::RegionRow, row::Row};
use crate::{expressions::ScopedExpression, temps::ExprOrTemp};
use ff::Field;
use haloumi_core::expressions::ExprBuilder;
use haloumi_ir::{Slot, groups::callsite::CallSite};
use haloumi_synthesis::io::{AdviceIO, InstanceIO};
use haloumi_synthesis::{
    groups::{Group, GroupCell},
    regions::RegionData,
};

#[derive(Debug, thiserror::Error)]
pub enum CallsiteGenError {
    #[error("Region with index {0} is not a known region")]
    UnknownRegion(usize),
    #[error("Region with index {0} does not have a start")]
    RegionWithoutStart(usize),
    #[error("Top level cannot be called by other group")]
    CalledTopLevelGroup,
}

fn cells_to_exprs<'e, 's, 'syn, 'cb, 'io, F, E>(
    cells: &[GroupCell],
    ctx: &super::GroupIRCtx<'cb, '_, 'syn, F, E>,
    advice_io: &'io AdviceIO,
    instance_io: &'io InstanceIO,
) -> Result<Vec<ExprOrTemp<ScopedExpression<'e, 's, F, E>>>, CallsiteGenError>
where
    'syn: 's,
    'io: 's,
    F: Field,
    E: Clone + ExprBuilder<F>,
{
    cells
        .iter()
        .map(|cell| {
            let region: Option<RegionData<'syn>> = cell
                .region_index()
                .map(|index| {
                    ctx.regions_by_index()
                        .get(&index)
                        .ok_or_else(|| CallsiteGenError::UnknownRegion(*index))
                })
                .transpose()?
                .copied();

            let expr = cell.to_expr::<F, E>();
            let row = match cell {
                GroupCell::Assigned(cell) => {
                    let start = ctx.regions_by_index()[&cell.region_index]
                        .start()
                        .ok_or_else(|| CallsiteGenError::RegionWithoutStart(*cell.region_index))?;
                    cell.row_offset + start
                }
                GroupCell::InstanceIO((_, row)) => *row,
                GroupCell::AdviceIO((_, row)) => *row,
            };
            log::debug!(
                "Lowering cell {cell:?} (We have region? {})",
                region.is_some()
            );
            Ok(match region {
                Some(region) => ScopedExpression::new(
                    expr,
                    RegionRow::new(region, row, advice_io, instance_io, ctx.syn().fixed_data()),
                ),
                None => ScopedExpression::new(
                    expr,
                    Row::new(row, advice_io, instance_io, ctx.syn().fixed_data()),
                ),
            })
        })
        .map(|e| e.map(ExprOrTemp::Expr))
        .collect()
}

pub(super) fn new_callsite<'s, 'e, 'syn, 'ctx, F, E>(
    callee: &Group,
    callee_id: usize,
    ctx: &super::GroupIRCtx<'_, '_, 'syn, F, E>,
    call_no: usize,
    advice_io: &'ctx AdviceIO,
    instance_io: &'ctx InstanceIO,
) -> Result<CallSite<ExprOrTemp<ScopedExpression<'e, 's, F, E>>>, CallsiteGenError>
where
    'syn: 's,
    'ctx: 's,
    F: Field,
    E: Clone + ExprBuilder<F>,
{
    let callee_key = callee.key().ok_or_else(
        || CallsiteGenError::CalledTopLevelGroup, //anyhow::anyhow!("Top level cannot be called by other group")
    )?;

    let inputs = cells_to_exprs(callee.inputs(), ctx, advice_io, instance_io)?;
    let outputs = cells_to_exprs(callee.outputs(), ctx, advice_io, instance_io)?;
    let output_vars: Vec<_> = callee
        .outputs()
        .iter()
        .enumerate()
        .map(|(n, _)| Slot::CallOutput(call_no, n))
        .collect();

    Ok(CallSite::new(
        callee.name().to_owned(),
        callee_key,
        callee_id,
        inputs,
        output_vars,
        outputs,
    ))
}
