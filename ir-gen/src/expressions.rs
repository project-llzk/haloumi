//! Traits and types related to expressions.

use std::{borrow::Cow, convert::Infallible, marker::PhantomData, rc::Rc};

use ff::{Field, PrimeField};
use haloumi_core::expressions::{
    EvalExpression, EvaluableExpr, ExprBuilder, ExpressionInfo, ExpressionTypes,
};
use haloumi_ir::{
    Felt,
    expr::{ExprProperties, ExprProperty, IRAexpr},
    traits::Evaluate,
};
use haloumi_synthesis::io::{AdviceIO, InstanceIO};
use haloumi_synthesis::regions::RegionData;

use crate::{
    error::Error,
    expressions::constant_folding::ConstantFolding,
    regions::region_row::RegionRow,
    resolvers::{
        ChallengeResolver, FixedQueryResolver, QueryResolver, ResolutionError, ResolvedQuery,
        ResolvedSelector, ResolversProvider, SelectorResolver, boxed_resolver,
    },
    temps::ExprOrTemp,
};

pub(crate) type UnresolvedExpr<'syn, 'sco, F, E> = ExprOrTemp<ScopedExpression<'syn, 'sco, F, E>>;

pub(crate) mod constant_folding;

/// Errors related to expressions.
#[derive(Debug, thiserror::Error)]
pub enum ExpressionError {
    /// The starting row of a region couldn't be computed.
    #[error("region {index:?} (\"{name}\") does not have a start row")]
    MissingRegionStart {
        /// Index of the region.
        index: Option<usize>,
        /// Name of the region.
        name: String,
    },
    /// Error raised while resolving an expression.
    #[error("failed to resolved expression: {0}")]
    Resolution(#[from] ResolutionError),
}

impl From<ExpressionError> for Error {
    fn from(value: ExpressionError) -> Self {
        Error::new(value)
    }
}

/// Indicates to the driver that the expression should be scoped in that row of the circuit.
///
/// The expression is internally handled by a [`std::borrow::Cow`] and can be a reference or owned.
#[derive(Debug, Clone)]
pub struct ExpressionInRow<'e, E: Clone, F> {
    expr: Cow<'e, E>,
    row: usize,
    _marker: PhantomData<F>,
}

impl<'e, E: Clone, F> ExpressionInRow<'e, E, F> {
    /// Creates a new struct owning the expression.
    pub fn new(row: usize, expr: E) -> Self {
        Self {
            expr: Cow::Owned(expr),
            row,
            _marker: PhantomData,
        }
    }

    /// Creates a new struct from a reference to an expression.
    pub fn from_ref(expr: &'e E, row: usize) -> Self {
        Self {
            expr: Cow::Borrowed(expr),
            row,
            _marker: PhantomData,
        }
    }

    /// Creates a [`ScopedExpression`] scoped by a
    /// [`RegionRow`].
    pub(crate) fn scoped_in_region_row<'r>(
        self,
        region: RegionData<'r>,
        advice_io: &'r AdviceIO,
        instance_io: &'r InstanceIO,
        fqr: &'r dyn FixedQueryResolver<F>,
    ) -> Result<ScopedExpression<'e, 'r, F, E>, ExpressionError>
    where
        F: Field,
    {
        // Rows in injected IR are relative offsets to the region but RegionRow expects the absolute
        // row number.
        let start = region
            .start()
            .ok_or_else(|| ExpressionError::MissingRegionStart {
                index: region.index().map(|i| *i),
                name: region.name().to_owned(),
            })?;
        Ok(ScopedExpression::from_cow(
            self.expr,
            RegionRow::new(region, start + self.row, advice_io, instance_io, fqr),
        ))
    }
}

impl<F, E> Evaluate<ExprProperties> for ExpressionInRow<'_, E, F>
where
    F: Field,
    E: EvaluableExpr<F> + ExpressionInfo + Clone,
{
    fn evaluate(&self) -> ExprProperties {
        struct Eval;

        impl<F: Field, E: ExpressionTypes> EvalExpression<F, E> for Eval {
            type Output = ExprProperties;

            fn constant(&self, _: &F) -> Self::Output {
                ExprProperty::Const.into()
            }

            fn selector(&self, _: &E::Selector) -> Self::Output {
                // Selectors should resolved to a boolean.
                ExprProperty::Const.into()
            }

            fn fixed(&self, _: &E::FixedQuery) -> Self::Output {
                // Fixed queries should resolved to the collected fixed value.
                ExprProperty::Const.into()
            }

            fn advice(&self, _: &E::AdviceQuery) -> Self::Output {
                Default::default()
            }

            fn instance(&self, _: &E::InstanceQuery) -> Self::Output {
                Default::default()
            }

            fn challenge(&self, _: &E::Challenge) -> Self::Output {
                Default::default()
            }

            fn negated(&self, expr: Self::Output) -> Self::Output {
                expr
            }

            fn sum(&self, lhs: Self::Output, rhs: Self::Output) -> Self::Output {
                lhs & rhs
            }

            fn product(&self, lhs: Self::Output, rhs: Self::Output) -> Self::Output {
                lhs & rhs
            }

            fn scaled(&self, lhs: Self::Output, _: &F) -> Self::Output {
                lhs & ExprProperty::Const
            }
        }

        self.expr.as_ref().evaluate(&Eval)
    }
}

/// Represents an expression associated to a scope.
///
/// The scope is represented by a [`ResolversProvider`] that returns
/// the resolvers required for lowering the expression.
///
/// The expression can be either a reference or owned.
#[derive(Clone)]
pub struct ScopedExpression<'e, 'r, F, E>
where
    F: Field,
    E: Clone,
{
    expression: Cow<'e, E>,
    resolvers: Rc<dyn ResolversProvider<F> + 'r>,
}

impl<'e, 'r, F, E> ScopedExpression<'e, 'r, F, E>
where
    F: Field,
    E: Clone,
{
    /// Creates a new scope owning the expression
    pub(crate) fn new<R>(expression: E, resolvers: R) -> Self
    where
        R: ResolversProvider<F> + 'r,
    {
        Self {
            expression: Cow::Owned(expression),
            resolvers: boxed_resolver(resolvers),
        }
    }

    /// Creates a new scope with a refernece to an expression.
    pub(crate) fn from_ref<R>(expression: &'e E, resolvers: R) -> Self
    where
        R: ResolversProvider<F> + 'r,
    {
        Self {
            expression: Cow::Borrowed(expression),
            resolvers: boxed_resolver(resolvers),
        }
    }

    pub(crate) fn simplified<'x>(self) -> ScopedExpression<'x, 'r, F, E>
    where
        E: EvaluableExpr<F> + ExpressionInfo + ExprBuilder<F>,
    {
        let expression =
            ConstantFolding::new(self.resolvers()).constant_fold(self.expression.as_ref());
        ScopedExpression {
            expression: Cow::Owned(expression),
            resolvers: self.resolvers,
        }
    }

    pub(crate) fn simplify(&mut self)
    where
        E: EvaluableExpr<F> + ExpressionInfo + ExprBuilder<F>,
    {
        let expression =
            ConstantFolding::new(self.resolvers()).constant_fold(self.expression.as_ref());
        self.expression = Cow::Owned(expression);
    }

    pub(crate) fn from_cow<R>(expression: Cow<'e, E>, resolvers: R) -> Self
    where
        R: ResolversProvider<F> + 'r,
    {
        Self {
            expression,
            resolvers: boxed_resolver(resolvers),
        }
    }

    pub(crate) fn resolvers(&self) -> &dyn ResolversProvider<F> {
        self.resolvers.as_ref()
    }

    pub(crate) fn selector_resolver(&self) -> &dyn SelectorResolver {
        self.resolvers.selector_resolver()
    }

    pub(crate) fn query_resolver(&self) -> &dyn QueryResolver<F> {
        self.resolvers.query_resolver()
    }

    pub(crate) fn challenge_resolver(&self) -> &dyn ChallengeResolver {
        self.resolvers.challenge_resolver()
    }
}

impl<F, E> haloumi_ir::traits::ConstantFolding for ScopedExpression<'_, '_, F, E>
where
    E: EvaluableExpr<F> + ExpressionInfo + ExprBuilder<F> + Clone,
    F: Field,
{
    type Error = Infallible;

    type T = F;

    fn constant_fold(&mut self) -> Result<(), Self::Error> {
        self.simplify();
        Ok(())
    }

    fn const_value(&self) -> Option<Self::T> {
        struct ConstEval;

        impl<F: Field, E: ExpressionTypes> EvalExpression<F, E> for ConstEval {
            type Output = Option<F>;

            fn constant(&self, f: &F) -> Self::Output {
                Some(*f)
            }

            fn selector(&self, _selector: &E::Selector) -> Self::Output {
                None
            }

            fn fixed(&self, _fixed_query: &E::FixedQuery) -> Self::Output {
                None
            }

            fn advice(&self, _advice_query: &E::AdviceQuery) -> Self::Output {
                None
            }

            fn instance(&self, _instance_query: &E::InstanceQuery) -> Self::Output {
                None
            }

            fn challenge(&self, _challenge: &E::Challenge) -> Self::Output {
                None
            }

            fn negated(&self, expr: Self::Output) -> Self::Output {
                expr.map(|f| -f)
            }

            fn sum(&self, lhs: Self::Output, rhs: Self::Output) -> Self::Output {
                lhs.zip(rhs).map(|(lhs, rhs)| lhs + rhs)
            }

            fn product(&self, lhs: Self::Output, rhs: Self::Output) -> Self::Output {
                lhs.zip(rhs).map(|(lhs, rhs)| lhs * rhs)
            }

            fn scaled(&self, lhs: Self::Output, rhs: &F) -> Self::Output {
                lhs.map(|f| f * rhs)
            }
        }

        self.expression.as_ref().evaluate(&ConstEval)
    }
}

impl<F, E> Evaluate<ExprProperties> for ScopedExpression<'_, '_, F, E>
where
    E: EvaluableExpr<F> + ExpressionInfo + Clone,
    F: Field,
{
    fn evaluate(&self) -> ExprProperties {
        struct Eval<'r, F, E> {
            sr: &'r dyn SelectorResolver,
            qr: &'r dyn QueryResolver<F>,
            _marker: PhantomData<E>,
        }

        impl<F: Field, E: ExpressionTypes> EvalExpression<F, E> for Eval<'_, F, E> {
            type Output = ExprProperties;

            fn constant(&self, _: &F) -> Self::Output {
                ExprProperty::Const.into()
            }

            fn selector(&self, selector: &E::Selector) -> Self::Output {
                self.sr
                    .resolve_selector(selector)
                    .ok()
                    .map(|s| match s {
                        ResolvedSelector::Const(_) => ExprProperty::Const.into(),
                        _ => Default::default(),
                    })
                    .unwrap_or_default()
            }

            fn fixed(&self, fixed_query: &E::FixedQuery) -> Self::Output {
                self.qr
                    .resolve_fixed_query(fixed_query)
                    .ok()
                    .map(|s| match s {
                        ResolvedQuery::Lit(_) => ExprProperty::Const.into(),
                        _ => Default::default(),
                    })
                    .unwrap_or_default()
            }

            fn advice(&self, _: &E::AdviceQuery) -> Self::Output {
                Default::default()
            }

            fn instance(&self, _: &E::InstanceQuery) -> Self::Output {
                Default::default()
            }

            fn challenge(&self, _: &E::Challenge) -> Self::Output {
                Default::default()
            }

            fn negated(&self, expr: Self::Output) -> Self::Output {
                expr
            }

            fn sum(&self, lhs: Self::Output, rhs: Self::Output) -> Self::Output {
                lhs & rhs
            }

            fn product(&self, lhs: Self::Output, rhs: Self::Output) -> Self::Output {
                lhs & rhs
            }

            fn scaled(&self, lhs: Self::Output, _: &F) -> Self::Output {
                lhs & ExprProperty::Const
            }
        }

        self.expression.as_ref().evaluate(&Eval {
            sr: self.selector_resolver(),
            qr: self.query_resolver(),
            _marker: PhantomData,
        })
    }
}

impl<F, E> std::fmt::Debug for ScopedExpression<'_, '_, F, E>
where
    F: Field,
    E: std::fmt::Debug + Clone,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ScopedExpression")
            .field("expression", &self.expression)
            .finish()
    }
}

impl<F, E> AsRef<E> for ScopedExpression<'_, '_, F, E>
where
    F: Field,
    E: Clone,
{
    fn as_ref(&self) -> &E {
        self.expression.as_ref()
    }
}

impl<F, E> TryFrom<ScopedExpression<'_, '_, F, E>> for IRAexpr
where
    F: PrimeField,
    E: EvaluableExpr<F> + Clone,
{
    type Error = ExpressionError;

    fn try_from(expr: ScopedExpression<'_, '_, F, E>) -> Result<Self, Self::Error> {
        expr.as_ref().evaluate(&PolyToAexpr::new(
            expr.selector_resolver(),
            expr.query_resolver(),
            expr.challenge_resolver(),
        ))
    }
}

/// Implements the conversion logic between an [`ScopedExpression`] and [`IRAexpr`].
struct PolyToAexpr<'r, F, E> {
    sr: &'r dyn SelectorResolver,
    qr: &'r dyn QueryResolver<F>,
    cr: &'r dyn ChallengeResolver,
    _marker: PhantomData<E>,
}

impl<'r, F, E> PolyToAexpr<'r, F, E> {
    pub fn new(
        sr: &'r dyn SelectorResolver,
        qr: &'r dyn QueryResolver<F>,
        cr: &'r dyn ChallengeResolver,
    ) -> Self {
        Self {
            sr,
            qr,
            cr,
            _marker: Default::default(),
        }
    }
}

impl<F: PrimeField, E: ExpressionTypes> EvalExpression<F, E> for PolyToAexpr<'_, F, E> {
    type Output = Result<IRAexpr, ExpressionError>;

    fn constant(&self, f: &F) -> Self::Output {
        Ok(IRAexpr::constant(Felt::new(*f)))
    }

    fn selector(&self, selector: &E::Selector) -> Self::Output {
        Ok(match self.sr.resolve_selector(selector)? {
            ResolvedSelector::Const(bool) => IRAexpr::constant(Felt::new::<F>(bool.to_f())),
            ResolvedSelector::Arg(arg) => IRAexpr::slot(arg),
        })
    }

    fn fixed(&self, fixed_query: &E::FixedQuery) -> Self::Output {
        Ok(match self.qr.resolve_fixed_query(fixed_query)? {
            ResolvedQuery::IO(io) => IRAexpr::slot(io),
            ResolvedQuery::Lit(f) => IRAexpr::constant(Felt::new(f)),
        })
    }

    fn advice(&self, advice_query: &E::AdviceQuery) -> Self::Output {
        Ok(match self.qr.resolve_advice_query(advice_query)? {
            ResolvedQuery::IO(io) => IRAexpr::slot(io),
            ResolvedQuery::Lit(f) => IRAexpr::constant(Felt::new(f)),
        })
    }

    fn instance(&self, instance_query: &E::InstanceQuery) -> Self::Output {
        Ok(match self.qr.resolve_instance_query(instance_query)? {
            ResolvedQuery::IO(io) => IRAexpr::slot(io),
            ResolvedQuery::Lit(f) => IRAexpr::constant(Felt::new(f)),
        })
    }

    fn challenge(&self, challenge: &E::Challenge) -> Self::Output {
        Ok(IRAexpr::slot(self.cr.resolve_challenge(challenge)?))
    }

    fn negated(&self, expr: Self::Output) -> Self::Output {
        Ok(-expr?)
    }

    fn sum(&self, lhs: Self::Output, rhs: Self::Output) -> Self::Output {
        Ok(lhs? + rhs?)
    }

    fn product(&self, lhs: Self::Output, rhs: Self::Output) -> Self::Output {
        Ok(lhs? * rhs?)
    }

    fn scaled(&self, lhs: Self::Output, rhs: &F) -> Self::Output {
        Ok(lhs? * self.constant(rhs)?)
    }
}
