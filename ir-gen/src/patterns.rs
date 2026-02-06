use ff::Field;
use haloumi_synthesis::selector::SelectorSet;

use haloumi_core::{
    expressions::{EvalExpression, EvaluableExpr, ExprBuilder, ExpressionTypes},
    info_traits::SelectorInfo as _,
};
use haloumi_ir::{CmpOp, meta::HasMeta as _, stmt::IRStmt};
use std::{borrow::Cow, cell::RefCell};

use crate::gates::{
    GateScope,
    callbacks::GateCallbacks,
    rewrite::{GateRewritePattern, Match, MatchResult, RewritePatternSet, RewriteResult},
};

/// Default gate pattern that transforms each polynomial in a gate into an equality statement for
/// each row in the region.
struct FallbackGateRewriter {
    ignore_disabled_gates: bool,
}

impl FallbackGateRewriter {
    pub fn new(ignore_disabled_gates: bool) -> Self {
        Self {
            ignore_disabled_gates,
        }
    }
}

impl<F, E> GateRewritePattern<F, E> for FallbackGateRewriter
where
    E: std::fmt::Debug + EvaluableExpr<F> + ExprBuilder<F>,
{
    fn match_gate(&self, _gate: GateScope<'_, '_, F, E>) -> MatchResult
    where
        F: Field,
    {
        Ok(Match::Match) // Match all
    }

    fn rewrite_gate<'syn>(&self, gate: GateScope<'syn, '_, F, E>) -> RewriteResult<'syn, E>
    where
        F: Field,
        E: Clone,
    {
        log::debug!(
            "Generating gate '{}' on region '{}' with the fallback rewriter",
            gate.gate_name(),
            gate.region_name()
        );
        let rows = gate.region_rows();
        log::debug!("The region has {} rows", gate.rows().count());
        Ok(rows
            .flat_map(move |row| {
                log::debug!("Creating constraints for row {}", row.row_number());

                gate.polynomials()
                    .iter()
                    .filter(move |e| {
                        let set = find_selectors(*e);
                        if self.ignore_disabled_gates && row.gate_is_disabled(&set) {
                            log::debug!(
                                "Expression {e:?} was ignored because its selectors are disabled",
                            );
                            return false;
                        }
                        true
                    })
                    .map(Cow::Borrowed)
                    .map(move |lhs| {
                        let mut constraint =
                            IRStmt::constraint(CmpOp::Eq, lhs, Cow::Owned(E::constant(F::ZERO)));
                        constraint.meta_mut().at_row(row.row_number());
                        constraint
                    })
                    .map(move |s| s.map(&mut |e: Cow<'syn, _>| (row.row_number(), e)))
                //.collect()
            })
            .collect())
    }
}

/// Configures a rewrite pattern set from patterns potentially provided by the user and
/// the fallback pattern for gates that don't require special handling.
pub fn load_patterns<F, E>(gate_cbs: &dyn GateCallbacks<F, E>) -> RewritePatternSet<F, E>
where
    F: Field,
    E: ExprBuilder<F> + EvaluableExpr<F> + std::fmt::Debug,
{
    let mut patterns = RewritePatternSet::default();
    let user_patterns = gate_cbs.patterns();
    log::debug!("Loading {} user patterns", user_patterns.len());
    patterns.extend(user_patterns);
    log::debug!(
        "Loading fallback pattern {}",
        std::any::type_name::<FallbackGateRewriter>()
    );
    patterns.add(FallbackGateRewriter::new(gate_cbs.ignore_disabled_gates()));
    patterns
}

fn find_selectors<F: Field, E: EvaluableExpr<F>>(poly: &E) -> SelectorSet {
    struct Eval(RefCell<SelectorSet>);

    impl<F, E: ExpressionTypes> EvalExpression<F, E> for Eval {
        type Output = ();

        fn selector(&self, selector: &E::Selector) -> Self::Output {
            self.0.borrow_mut().insert(selector.id());
        }

        fn constant(&self, _: &F) -> Self::Output {}
        fn fixed(&self, _: &E::FixedQuery) -> Self::Output {}
        fn advice(&self, _: &E::AdviceQuery) -> Self::Output {}
        fn instance(&self, _: &E::InstanceQuery) -> Self::Output {}
        fn challenge(&self, _: &E::Challenge) -> Self::Output {}
        fn negated(&self, _: Self::Output) -> Self::Output {}
        fn sum(&self, _: Self::Output, _: Self::Output) -> Self::Output {}
        fn product(&self, _: Self::Output, _: Self::Output) -> Self::Output {}
        fn scaled(&self, _: Self::Output, _: &F) -> Self::Output {}
    }
    let e = Eval(Default::default());
    poly.evaluate(&e);
    e.0.take()
}
