//! Macros for implementing the expression traits in a Halo2 implementation.

/// Implements the required traits for supporting an expression type.
#[macro_export]
macro_rules! __impl_expression_support {
    ($expr:path, $field:path, $selector:ty, $fixed_query:ty, $advice_query:ty, $instance_query:ty, $challenge:ty) => {
        impl<F: $field> $crate::core::expressions::ExpressionTypes for $expr<F> {
            type Selector = $selector;
            type FixedQuery = $fixed_query;
            type AdviceQuery = $advice_query;
            type InstanceQuery = $instance_query;
            type Challenge = $challenge;
        }

        impl<F: $field> $crate::core::expressions::ExpressionInfo for $expr<F> {
            fn as_negation(&self) -> Option<&Self> {
                match self {
                    $expr::Negated(e) => Some(e.as_ref()),
                    _ => None,
                }
            }

            fn as_fixed_query(&self) -> Option<&Self::FixedQuery> {
                match self {
                    $expr::Fixed(q) => Some(q),
                    _ => None,
                }
            }
        }

        impl<F: $field> $crate::core::expressions::EvaluableExpr<F> for $expr<F> {
            fn evaluate<E: $crate::core::expressions::EvalExpression<F, Self>>(
                &self,
                evaluator: &E,
            ) -> E::Output {
                self.evaluate(
                    &|f| evaluator.constant(&f),
                    &|s| evaluator.selector(&s),
                    &|fq| evaluator.fixed(&fq),
                    &|aq| evaluator.advice(&aq),
                    &|iq| evaluator.instance(&iq),
                    &|c| evaluator.challenge(&c),
                    &|e| evaluator.negated(e),
                    &|lhs, rhs| evaluator.sum(lhs, rhs),
                    &|lhs, rhs| evaluator.product(lhs, rhs),
                    &|lhs, rhs| evaluator.scaled(lhs, &rhs),
                )
            }
        }

        impl<F: $field> $crate::core::expressions::ExprBuilder<F> for $expr<F> {
            fn constant(f: F) -> Self {
                Self::Constant(f)
            }

            fn selector(
                selector: <Self as $crate::core::expressions::ExpressionTypes>::Selector,
            ) -> Self {
                Self::Selector(selector)
            }

            fn fixed(fixed_query: Self::FixedQuery) -> Self {
                Self::Fixed(fixed_query)
            }

            fn advice(advice_query: Self::AdviceQuery) -> Self {
                Self::Advice(advice_query)
            }

            fn instance(instance_query: Self::InstanceQuery) -> Self {
                Self::Instance(instance_query)
            }

            fn challenge(
                challenge: <Self as haloumi_core::expressions::ExpressionTypes>::Challenge,
            ) -> Self {
                Self::Challenge(challenge)
            }

            fn negated(expr: Self) -> Self {
                Self::Negated(Box::new(expr))
            }

            fn sum(lhs: Self, rhs: Self) -> Self {
                Self::Sum(Box::new(lhs), Box::new(rhs))
            }

            fn product(lhs: Self, rhs: Self) -> Self {
                Self::Product(Box::new(lhs), Box::new(rhs))
            }

            fn scaled(lhs: Self, rhs: F) -> Self {
                Self::Scaled(Box::new(lhs), rhs)
            }
        }
    };
}
