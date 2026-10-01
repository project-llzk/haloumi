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
pub fn load_patterns<'gc, F, E>(
    gate_cbs: &'gc dyn GateCallbacks<F, E>,
) -> RewritePatternSet<'gc, F, E>
where
    F: Field,
    E: ExprBuilder<F> + EvaluableExpr<F> + std::fmt::Debug,
{
    log::debug!(
        "Loading fallback pattern {}",
        std::any::type_name::<FallbackGateRewriter>()
    );
    let mut patterns =
        RewritePatternSet::new(FallbackGateRewriter::new(gate_cbs.ignore_disabled_gates()));
    let user_patterns = gate_cbs.patterns();
    log::debug!("Loading {} user patterns", user_patterns.len());
    patterns.extend(user_patterns);

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

/// Returns the selectors that are factors of the whole expression, i.e. the expression is zero
/// whenever one of them is disabled.
pub(crate) fn find_selector_factors<F, E: EvaluableExpr<F>>(poly: &E) -> SelectorSet {
    struct Eval;

    impl<F, E: ExpressionTypes> EvalExpression<F, E> for Eval {
        type Output = SelectorSet;

        fn selector(&self, selector: &E::Selector) -> Self::Output {
            let mut set = SelectorSet::default();
            set.insert(selector.id());
            set
        }

        fn constant(&self, _: &F) -> Self::Output {
            SelectorSet::default()
        }
        fn fixed(&self, _: &E::FixedQuery) -> Self::Output {
            SelectorSet::default()
        }
        fn advice(&self, _: &E::AdviceQuery) -> Self::Output {
            SelectorSet::default()
        }
        fn instance(&self, _: &E::InstanceQuery) -> Self::Output {
            SelectorSet::default()
        }
        fn challenge(&self, _: &E::Challenge) -> Self::Output {
            SelectorSet::default()
        }
        fn negated(&self, expr: Self::Output) -> Self::Output {
            expr
        }
        fn sum(&self, mut lhs: Self::Output, rhs: Self::Output) -> Self::Output {
            // A selector factors a sum only if it factors both sides.
            lhs.intersect_with(&rhs);
            lhs
        }
        fn product(&self, mut lhs: Self::Output, rhs: Self::Output) -> Self::Output {
            lhs.union_with(&rhs);
            lhs
        }
        fn scaled(&self, expr: Self::Output, _: &F) -> Self::Output {
            expr
        }
    }
    poly.evaluate(&Eval)
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use haloumi_core::{
        info_traits::{ChallengeInfo, CreateQuery, QueryInfo, SelectorInfo},
        query::{Advice, Fixed, Instance, QueryKind},
        table::Rotation,
    };

    use super::*;

    /// Minimal expression type for exercising expression visitors.
    #[derive(Debug, Clone)]
    enum Expr {
        Constant,
        Selector(Sel),
        Advice(Query<Advice>),
        Negated(Box<Expr>),
        Sum(Box<Expr>, Box<Expr>),
        Product(Box<Expr>, Box<Expr>),
        Scaled(Box<Expr>),
    }

    #[derive(Debug, Clone, Copy)]
    struct Sel(usize);

    impl SelectorInfo for Sel {
        fn id(&self) -> usize {
            self.0
        }
    }

    #[derive(Debug, Clone, Copy)]
    struct Query<K>(usize, PhantomData<K>);

    impl<K: QueryKind> QueryInfo for Query<K> {
        type Kind = K;

        fn rotation(&self) -> Rotation {
            0
        }

        fn column_index(&self) -> usize {
            self.0
        }
    }

    impl<K> CreateQuery<Expr> for Query<K> {
        fn query_expr(index: usize, _: Rotation) -> Expr {
            Expr::Advice(Query(index, PhantomData))
        }
    }

    #[derive(Debug, Clone, Copy)]
    struct Challenge;

    impl ChallengeInfo for Challenge {
        fn index(&self) -> usize {
            0
        }

        fn phase(&self) -> u8 {
            0
        }
    }

    impl ExpressionTypes for Expr {
        type Selector = Sel;
        type FixedQuery = Query<Fixed>;
        type AdviceQuery = Query<Advice>;
        type InstanceQuery = Query<Instance>;
        type Challenge = Challenge;
    }

    impl EvaluableExpr<()> for Expr {
        fn evaluate<E: EvalExpression<(), Self>>(&self, evaluator: &E) -> E::Output {
            match self {
                Expr::Constant => evaluator.constant(&()),
                Expr::Selector(s) => evaluator.selector(s),
                Expr::Advice(q) => evaluator.advice(q),
                Expr::Negated(e) => evaluator.negated(e.evaluate(evaluator)),
                Expr::Sum(l, r) => evaluator.sum(l.evaluate(evaluator), r.evaluate(evaluator)),
                Expr::Product(l, r) => {
                    evaluator.product(l.evaluate(evaluator), r.evaluate(evaluator))
                }
                Expr::Scaled(e) => evaluator.scaled(e.evaluate(evaluator), &()),
            }
        }
    }

    fn sel(id: usize) -> Expr {
        Expr::Selector(Sel(id))
    }

    fn adv(col: usize) -> Expr {
        Expr::Advice(Query(col, PhantomData))
    }

    fn sum(l: Expr, r: Expr) -> Expr {
        Expr::Sum(Box::new(l), Box::new(r))
    }

    fn prod(l: Expr, r: Expr) -> Expr {
        Expr::Product(Box::new(l), Box::new(r))
    }

    fn factors(e: &Expr) -> Vec<usize> {
        find_selector_factors::<(), _>(e).iter().collect()
    }

    #[test]
    fn selector_times_cell_is_gated() {
        assert_eq!(factors(&prod(sel(0), adv(1))), [0]);
    }

    #[test]
    fn nested_products_collect_every_selector() {
        assert_eq!(factors(&prod(sel(0), prod(adv(1), sel(2)))), [0, 2]);
    }

    #[test]
    fn negation_and_scaling_keep_factors() {
        let e = Expr::Negated(Box::new(Expr::Scaled(Box::new(prod(sel(3), adv(0))))));
        assert_eq!(factors(&e), [3]);
    }

    #[test]
    fn sum_is_gated_only_by_common_selectors() {
        assert_eq!(
            factors(&sum(prod(sel(0), adv(1)), prod(sel(0), adv(2)))),
            [0]
        );
        assert_eq!(
            factors(&sum(prod(sel(0), adv(1)), adv(2))),
            Vec::<usize>::new()
        );
    }

    #[test]
    fn selector_outside_a_factor_does_not_gate() {
        // q * a + (1 - q) * b is live on rows where q is disabled.
        let not_q = sum(Expr::Constant, Expr::Negated(Box::new(sel(0))));
        let e = sum(prod(sel(0), adv(1)), prod(not_q, adv(2)));
        assert_eq!(factors(&e), Vec::<usize>::new());
    }

    #[test]
    fn leaves_without_selectors_are_not_gated() {
        assert_eq!(factors(&Expr::Constant), Vec::<usize>::new());
        assert_eq!(factors(&adv(0)), Vec::<usize>::new());
        assert_eq!(factors(&sel(4)), [4]);
    }
}
