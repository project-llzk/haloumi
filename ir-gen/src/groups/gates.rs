use ff::Field;
use haloumi_ir::{meta::HasMeta, stmt::IRStmt};
use haloumi_synthesis::{
    gates::Gate,
    io::{AdviceIO, InstanceIO},
    regions::RegionData,
};

use crate::{
    expressions::ScopedExpression,
    gates::{
        GateScope,
        rewrite::{GateRewritePattern as _, RewritePatternSet},
    },
    groups::{IRGroupGenError, prepend_comment},
    resolvers::FixedQueryResolver,
    utils,
};

/// Uses the given rewrite patterns to lower the gates on each region.
pub fn lower_gates<'sco, 'syn, 'io, F, E>(
    gates: &'syn [Gate<E>],
    regions: &[RegionData<'syn>],
    patterns: &RewritePatternSet<F, E>,
    advice_io: &'io AdviceIO,
    instance_io: &'io InstanceIO,
    fqr: &'syn dyn FixedQueryResolver<F>,
    generate_debug_comments: bool,
) -> Result<Vec<IRStmt<ScopedExpression<'syn, 'sco, F, E>>>, IRGroupGenError>
where
    'syn: 'sco,
    'io: 'sco + 'syn,
    F: Field,
    E: Clone,
{
    log::debug!("Got {} gates and {} regions", gates.len(), regions.len());
    utils::product(regions, gates)
        .map(|(r, g)| {
            log::debug!("Lowering gate {} in region {}", g.name(), r.name());
            let rows = r.rows();
            let scope = GateScope::new(g, *r, (rows.start, rows.end), advice_io, instance_io, fqr);

            let stmt = patterns.match_and_rewrite(scope)?.ok_or_else(|| {
                IRGroupGenError::UnmatchedGate {
                    name: scope.gate_name().to_owned(),
                    region_index: scope
                        .region_index()
                        .as_deref()
                        .map(ToString::to_string)
                        .unwrap_or("unk".to_string()),
                    region_name: scope.region_name().to_owned(),
                }
            })?;

            let mut stmt = stmt.try_map(&mut |(row, expr)| -> Result<_, IRGroupGenError> {
                let rr = scope.region_row(row)?;
                Ok(ScopedExpression::from_cow(expr, rr))
            })?;
            stmt.meta_mut().at_gate(
                scope.gate_name(),
                scope.region_header(),
                scope.region_index(),
                None,
            );
            stmt.propagate_meta();
            Ok(prepend_comment(
                stmt,
                || {
                    IRStmt::comment(format!(
                        "gate '{}' @ {} @ rows {}..={}",
                        scope.gate_name(),
                        scope.region_header().to_string(),
                        scope.start_row(),
                        scope.end_row()
                    ))
                },
                generate_debug_comments,
            ))
        })
        .collect()
}
