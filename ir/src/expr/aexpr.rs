//! Structs for handling arithmetic expressions.

use crate::{
    expr::{ExprProperties, ExprProperty},
    printer::IRPrintable,
    traits::{Canonicalize, ConstantFolding, Evaluate},
};
use eqv::{EqvRelation, equiv};
use haloumi_core::{eqv::SymbolicEqv, felt::Felt, slot::Slot};
use haloumi_lowering::{ExprLowering, lowerable::LowerableExpr};
use std::fmt::Write;
use std::{
    convert::Infallible,
    ops::{Add, Mul, Neg},
};

/// Represents an arithmetic expression.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct IRAexpr(pub(crate) IRAexprImpl);

#[derive(PartialEq, Eq, Clone)]
pub(crate) enum IRAexprImpl {
    /// Constant value.
    Constant(Felt),
    /// IO element of the circuit; inputs, outputs, cells, etc.
    IO(Slot),
    /// Represents the negation of the inner expression.
    Negated(Box<IRAexpr>),
    /// Represents the sum of the inner expressions.
    Sum(Box<IRAexpr>, Box<IRAexpr>),
    /// Represents the product of the inner expresions.
    Product(Box<IRAexpr>, Box<IRAexpr>),
}

impl IRAexpr {
    /// Creates a constant expression.
    pub fn constant(felt: Felt) -> Self {
        Self(IRAexprImpl::Constant(felt))
    }

    /// Creates an expression pointing to a slot.
    pub fn slot(s: impl Into<Slot>) -> Self {
        Self(IRAexprImpl::IO(s.into()))
    }

    /// Maps the IO in-place.
    pub fn try_map_io<E>(&mut self, f: &impl Fn(&mut Slot) -> Result<(), E>) -> Result<(), E> {
        match &mut self.0 {
            IRAexprImpl::IO(func_io) => f(func_io),
            IRAexprImpl::Negated(expr) => expr.try_map_io(f),
            IRAexprImpl::Sum(lhs, rhs) => {
                lhs.try_map_io(f)?;
                rhs.try_map_io(f)
            }
            IRAexprImpl::Product(lhs, rhs) => {
                lhs.try_map_io(f)?;
                rhs.try_map_io(f)
            }
            _ => Ok(()),
        }
    }
}

impl Neg for IRAexpr {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(IRAexprImpl::Negated(Box::new(self)))
    }
}

impl Add for IRAexpr {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(IRAexprImpl::Sum(Box::new(self), Box::new(rhs)))
    }
}

impl Mul for IRAexpr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self(IRAexprImpl::Product(Box::new(self), Box::new(rhs)))
    }
}

impl From<Felt> for IRAexpr {
    fn from(value: Felt) -> Self {
        Self(IRAexprImpl::Constant(value))
    }
}

impl From<Slot> for IRAexpr {
    fn from(value: Slot) -> Self {
        Self(IRAexprImpl::IO(value))
    }
}

impl Evaluate<Option<Felt>> for IRAexpr {
    fn evaluate(&self) -> Option<Felt> {
        match &self.0 {
            IRAexprImpl::Constant(felt) => Some(*felt),
            IRAexprImpl::IO(_) => None,
            IRAexprImpl::Negated(expr) => Evaluate::<Option<Felt>>::evaluate(expr).map(|f| -f),
            IRAexprImpl::Sum(lhs, rhs) => Evaluate::<Option<Felt>>::evaluate(lhs)
                .zip(Evaluate::<Option<Felt>>::evaluate(rhs))
                .map(|(lhs, rhs)| lhs + rhs),
            IRAexprImpl::Product(lhs, rhs) => Evaluate::<Option<Felt>>::evaluate(lhs)
                .zip(Evaluate::<Option<Felt>>::evaluate(rhs))
                .map(|(lhs, rhs)| lhs * rhs),
        }
    }
}

impl Evaluate<ExprProperties> for IRAexpr {
    fn evaluate(&self) -> ExprProperties {
        match &self.0 {
            IRAexprImpl::Constant(_) => ExprProperty::Const.into(),
            IRAexprImpl::IO(_) => Default::default(),
            IRAexprImpl::Negated(expr) => expr.evaluate(),
            IRAexprImpl::Sum(lhs, rhs) | IRAexprImpl::Product(lhs, rhs) => {
                Evaluate::<ExprProperties>::evaluate(lhs)
                    & Evaluate::<ExprProperties>::evaluate(rhs)
            }
        }
    }
}

impl ConstantFolding for IRAexpr {
    type T = Felt;

    type Error = Infallible;

    fn constant_fold(&mut self) -> Result<(), Self::Error> {
        match &mut self.0 {
            IRAexprImpl::Constant(_) => {}
            IRAexprImpl::IO(_) => {}
            IRAexprImpl::Negated(expr) => {
                expr.constant_fold()?;
                if let Some(f) = expr.const_value() {
                    *self = (-f).into();
                }
            }

            IRAexprImpl::Sum(lhs, rhs) => {
                lhs.constant_fold()?;
                rhs.constant_fold()?;

                match (lhs.const_value(), rhs.const_value()) {
                    (Some(lhs), Some(rhs)) => {
                        *self = Self(IRAexprImpl::Constant(lhs + rhs));
                    }
                    (None, Some(rhs)) if rhs == 0usize => {
                        *self = (**lhs).clone();
                    }
                    (Some(lhs), None) if lhs == 0usize => {
                        *self = (**rhs).clone();
                    }
                    _ => {}
                }
            }
            IRAexprImpl::Product(lhs, rhs) => {
                lhs.constant_fold()?;
                rhs.constant_fold()?;
                match (lhs.const_value(), rhs.const_value()) {
                    (Some(lhs), Some(rhs)) => {
                        *self = (lhs * rhs).into();
                    }
                    // (* 1 X) => X
                    (None, Some(rhs)) if rhs == 1usize => {
                        *self = (**lhs).clone();
                    }
                    (Some(lhs), None) if lhs == 1usize => {
                        *self = (**rhs).clone();
                    }
                    // (* 0 X) => 0
                    (None, Some(rhs)) if rhs == 0usize => {
                        *self = rhs.into();
                    }
                    (Some(lhs), None) if lhs == 0usize => {
                        *self = lhs.into();
                    }
                    // (* -1 X) => -X
                    (None, Some(rhs)) if rhs.is_minus_one() => {
                        *self = Self(IRAexprImpl::Negated(lhs.clone()));
                    }
                    (Some(lhs), None) if lhs.is_minus_one() => {
                        *self = Self(IRAexprImpl::Negated(rhs.clone()));
                    }
                    _ => {}
                }
            }
        }
        Ok(())
    }

    /// Returns `Some(_)` if the expression is a constant value. None otherwise.
    fn const_value(&self) -> Option<Felt> {
        match &self.0 {
            IRAexprImpl::Constant(f) => Some(*f),
            _ => None,
        }
    }
}

impl IRAexpr {
    /// Returns the inner element of the expression if it matches [`IRAexprImpl::Negated`].
    fn negated_inner(&self) -> Option<&IRAexpr> {
        match &self.0 {
            IRAexprImpl::Negated(inner) => Some(inner),
            _ => None,
        }
    }
}

impl Canonicalize for IRAexpr {
    fn canonicalize(&mut self) {
        match &mut self.0 {
            IRAexprImpl::Constant(_) => {}
            IRAexprImpl::IO(_) => {}
            IRAexprImpl::Negated(expr) => {
                expr.canonicalize();
                // (- (- X)) => X
                if let Some(inner) = expr.negated_inner() {
                    *self = inner.clone();
                }
            }
            IRAexprImpl::Sum(_, _) => todo!(),
            IRAexprImpl::Product(_, _) => todo!(),
        };
    }
}

impl std::fmt::Debug for IRAexprImpl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Constant(arg0) => write!(f, "{arg0:?}"),
            Self::IO(arg0) => write!(f, "{arg0:?}"),
            Self::Negated(arg0) => write!(f, "(- {arg0:?})"),
            Self::Sum(arg0, arg1) => write!(f, "(+ {arg0:?} {arg1:?})"),
            Self::Product(arg0, arg1) => write!(f, "(* {arg0:?} {arg1:?})"),
        }
    }
}

impl EqvRelation<IRAexpr> for SymbolicEqv {
    /// Two arithmetic expressions are equivalent if they are structurally equal, constant values
    /// equal and variables are equivalent.
    fn equivalent(lhs: &IRAexpr, rhs: &IRAexpr) -> bool {
        match (&lhs.0, &rhs.0) {
            (IRAexprImpl::Constant(lhs), IRAexprImpl::Constant(rhs)) => lhs == rhs,
            (IRAexprImpl::IO(lhs), IRAexprImpl::IO(rhs)) => equiv!(Self | lhs, rhs),
            (IRAexprImpl::Negated(lhs), IRAexprImpl::Negated(rhs)) => equiv!(Self | lhs, rhs),
            (IRAexprImpl::Sum(lhs0, lhs1), IRAexprImpl::Sum(rhs0, rhs1)) => {
                equiv!(Self | lhs0, rhs0) && equiv!(Self | lhs1, rhs1)
            }
            (IRAexprImpl::Product(lhs0, lhs1), IRAexprImpl::Product(rhs0, rhs1)) => {
                equiv!(Self | lhs0, rhs0) && equiv!(Self | lhs1, rhs1)
            }
            _ => false,
        }
    }
}

impl LowerableExpr for IRAexpr {
    fn lower<L>(self, l: &L) -> haloumi_lowering::Result<L::CellOutput>
    where
        L: ExprLowering + ?Sized,
    {
        match self.0 {
            IRAexprImpl::Constant(f) => l.lower_constant(f),
            IRAexprImpl::IO(io) => l.lower_funcio(io),
            IRAexprImpl::Negated(expr) => l.lower_neg(&expr.lower(l)?),
            IRAexprImpl::Sum(lhs, rhs) => l.lower_sum(&lhs.lower(l)?, &rhs.lower(l)?),
            IRAexprImpl::Product(lhs, rhs) => l.lower_product(&lhs.lower(l)?, &rhs.lower(l)?),
        }
    }
}

impl IRPrintable for IRAexpr {
    fn fmt(&self, ctx: &mut crate::printer::IRPrinterCtx<'_, '_>) -> crate::printer::Result {
        match &self.0 {
            IRAexprImpl::Constant(felt) => ctx.list("const", |ctx| write!(ctx, "{}", felt)),
            IRAexprImpl::IO(slot) => slot.fmt(ctx),
            IRAexprImpl::Negated(expr) => ctx.block("-", |ctx| expr.fmt(ctx)),
            IRAexprImpl::Sum(lhs, rhs) => ctx.block("+", |ctx| {
                let do_nl = lhs.depth() > 1 || rhs.depth() > 1;
                if lhs.depth() > 1 {
                    ctx.nl()?;
                }
                lhs.fmt(ctx)?;
                if do_nl {
                    ctx.nl()?;
                } else {
                    write!(ctx, " ")?;
                }
                rhs.fmt(ctx)
            }),
            IRAexprImpl::Product(lhs, rhs) => ctx.block("*", |ctx| {
                let do_nl = lhs.depth() > 1 || rhs.depth() > 1;
                if lhs.depth() > 1 {
                    ctx.nl()?;
                }
                lhs.fmt(ctx)?;
                if do_nl {
                    ctx.nl()?;
                } else {
                    write!(ctx, " ")?;
                }
                rhs.fmt(ctx)
            }),
        }
    }

    fn depth(&self) -> usize {
        match &self.0 {
            IRAexprImpl::Constant(_) | IRAexprImpl::IO(_) => 1,
            IRAexprImpl::Negated(expr) => 1 + expr.depth(),
            IRAexprImpl::Sum(lhs, rhs) | IRAexprImpl::Product(lhs, rhs) => {
                1 + std::cmp::max(lhs.depth(), rhs.depth())
            }
        }
    }
}

#[cfg(test)]
mod folding_tests {
    use super::*;
    use rstest::rstest;

    use ff::PrimeField;

    /// Implementation of BabyBear used for testing.
    #[derive(PrimeField)]
    #[PrimeFieldModulus = "2013265921"]
    #[PrimeFieldGenerator = "31"]
    #[PrimeFieldReprEndianness = "little"]
    pub struct BabyBear([u64; 1]);

    /// Creates a constant value under BabyBear
    fn c(v: impl Into<BabyBear>) -> IRAexpr {
        IRAexpr(IRAexprImpl::Constant(Felt::from(v.into())))
    }

    #[rstest]
    fn folding_constant_within_field() {
        let mut test = c(5);
        let expected = test.clone();
        test.constant_fold().unwrap();
        assert_eq!(test, expected);
    }

    #[rstest]
    fn folding_constant_outside_field() {
        let mut test = c(2013265922);
        let expected = c(1);
        test.constant_fold().unwrap();
        assert_eq!(test, expected);
    }

    #[rstest]
    fn mult_identity() {
        let lhs = c(1);
        let rhs = IRAexpr(IRAexprImpl::IO(Slot::Arg(0.into())));
        let mut mul = IRAexpr(IRAexprImpl::Product(Box::new(lhs), Box::new(rhs.clone())));
        mul.constant_fold().unwrap();
        assert_eq!(mul, rhs);
    }

    #[rstest]
    fn mult_identity_rev() {
        let rhs = c(1);
        let lhs = IRAexpr(IRAexprImpl::IO(Slot::Arg(0.into())));
        let mut mul = IRAexpr(IRAexprImpl::Product(Box::new(lhs.clone()), Box::new(rhs)));
        mul.constant_fold().unwrap();
        assert_eq!(mul, lhs);
    }

    #[rstest]
    fn mult_by_zero() {
        let lhs = c(0);
        let rhs = IRAexpr(IRAexprImpl::IO(Slot::Arg(0.into())));
        let mut mul = IRAexpr(IRAexprImpl::Product(Box::new(lhs.clone()), Box::new(rhs)));
        mul.constant_fold().unwrap();
        assert_eq!(mul, lhs);
    }

    #[rstest]
    fn mult_by_zero_rev() {
        let rhs = c(0);
        let lhs = IRAexpr(IRAexprImpl::IO(Slot::Arg(0.into())));
        let mut mul = IRAexpr(IRAexprImpl::Product(Box::new(lhs), Box::new(rhs.clone())));
        mul.constant_fold().unwrap();
        assert_eq!(mul, rhs);
    }

    #[rstest]
    fn sum_identity() {
        let lhs = c(0);
        let rhs = IRAexpr(IRAexprImpl::IO(Slot::Arg(0.into())));
        let mut sum = IRAexpr(IRAexprImpl::Sum(Box::new(lhs), Box::new(rhs.clone())));
        sum.constant_fold().unwrap();
        assert_eq!(sum, rhs);
    }

    #[rstest]
    fn sum_identity_rev() {
        let rhs = c(0);
        let lhs = IRAexpr(IRAexprImpl::IO(Slot::Arg(0.into())));
        let mut sum = IRAexpr(IRAexprImpl::Sum(Box::new(lhs.clone()), Box::new(rhs)));
        sum.constant_fold().unwrap();
        assert_eq!(sum, lhs);
    }
}
