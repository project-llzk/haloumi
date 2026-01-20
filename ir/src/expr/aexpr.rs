//! Structs for handling arithmetic expressions.

use crate::traits::{Canonicalize, ConstantFolding};
use eqv::{EqvRelation, equiv};
use haloumi_core::{
    eqv::SymbolicEqv,
    felt::{Felt, Prime},
    slot::Slot,
};
use haloumi_lowering::{ExprLowering, lowerable::LowerableExpr};
use std::convert::Infallible;

/// Represents an arithmetic expression.
#[derive(PartialEq, Eq, Clone)]
pub enum IRAexpr {
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
    /// Maps the IO in-place.
    pub fn try_map_io<E>(&mut self, f: &impl Fn(&mut Slot) -> Result<(), E>) -> Result<(), E> {
        match self {
            IRAexpr::IO(func_io) => f(func_io),
            IRAexpr::Negated(expr) => expr.try_map_io(f),
            IRAexpr::Sum(lhs, rhs) => {
                lhs.try_map_io(f)?;
                rhs.try_map_io(f)
            }
            IRAexpr::Product(lhs, rhs) => {
                lhs.try_map_io(f)?;
                rhs.try_map_io(f)
            }
            _ => Ok(()),
        }
    }
}

impl<T> From<T> for IRAexpr
where
    Felt: From<T>,
{
    fn from(value: T) -> Self {
        Self::Constant(value.into())
    }
}

impl ConstantFolding for IRAexpr {
    type T = Felt;

    type Error = Infallible;

    fn constant_fold(&mut self) -> Result<(), Self::Error> {
        match self {
            IRAexpr::Constant(_) => {}
            IRAexpr::IO(_) => {}
            IRAexpr::Negated(expr) => {
                expr.constant_fold()?;
                if let Some(f) = expr.const_value() {
                    *self = (-f).into();
                }
            }

            IRAexpr::Sum(lhs, rhs) => {
                lhs.constant_fold()?;
                rhs.constant_fold()?;

                match (lhs.const_value(), rhs.const_value()) {
                    (Some(lhs), Some(rhs)) => {
                        *self = IRAexpr::Constant(lhs + rhs);
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
            IRAexpr::Product(lhs, rhs) => {
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
                        *self = IRAexpr::Negated(lhs.clone());
                    }
                    (Some(lhs), None) if lhs.is_minus_one() => {
                        *self = IRAexpr::Negated(rhs.clone());
                    }
                    _ => {}
                }
            }
        }
        Ok(())
    }

    /// Returns `Some(_)` if the expression is a constant value. None otherwise.
    fn const_value(&self) -> Option<Felt> {
        match self {
            IRAexpr::Constant(f) => Some(*f),
            _ => None,
        }
    }
}

impl IRAexpr {
    /// Returns the inner element of the expression if it matches [`IRAexpr::Negated`].
    fn negated_inner(&self) -> Option<&IRAexpr> {
        match self {
            IRAexpr::Negated(inner) => Some(inner),
            _ => None,
        }
    }
}

impl Canonicalize for IRAexpr {
    fn canonicalize(&mut self) {
        match self {
            IRAexpr::Constant(_) => {}
            IRAexpr::IO(_) => {}
            IRAexpr::Negated(expr) => {
                expr.canonicalize();
                // (- (- X)) => X
                if let Some(inner) = expr.negated_inner() {
                    *self = inner.clone();
                }
            }
            IRAexpr::Sum(_, _) => todo!(),
            IRAexpr::Product(_, _) => todo!(),
        };
    }
}

impl std::fmt::Debug for IRAexpr {
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
        match (lhs, rhs) {
            (IRAexpr::Constant(lhs), IRAexpr::Constant(rhs)) => lhs == rhs,
            (IRAexpr::IO(lhs), IRAexpr::IO(rhs)) => equiv!(Self | lhs, rhs),
            (IRAexpr::Negated(lhs), IRAexpr::Negated(rhs)) => equiv!(Self | lhs, rhs),
            (IRAexpr::Sum(lhs0, lhs1), IRAexpr::Sum(rhs0, rhs1)) => {
                equiv!(Self | lhs0, rhs0) && equiv!(Self | lhs1, rhs1)
            }
            (IRAexpr::Product(lhs0, lhs1), IRAexpr::Product(rhs0, rhs1)) => {
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
        match self {
            IRAexpr::Constant(f) => l.lower_constant(f),
            IRAexpr::IO(io) => l.lower_funcio(io),
            IRAexpr::Negated(expr) => l.lower_neg(&expr.lower(l)?),
            IRAexpr::Sum(lhs, rhs) => l.lower_sum(&lhs.lower(l)?, &rhs.lower(l)?),
            IRAexpr::Product(lhs, rhs) => l.lower_product(&lhs.lower(l)?, &rhs.lower(l)?),
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
        IRAexpr::Constant(Felt::from(v.into()))
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
        let rhs = IRAexpr::IO(Slot::Arg(0.into()));
        let mut mul = IRAexpr::Product(Box::new(lhs), Box::new(rhs.clone()));
        mul.constant_fold().unwrap();
        assert_eq!(mul, rhs);
    }

    #[rstest]
    fn mult_identity_rev() {
        let rhs = c(1);
        let lhs = IRAexpr::IO(Slot::Arg(0.into()));
        let mut mul = IRAexpr::Product(Box::new(lhs.clone()), Box::new(rhs));
        mul.constant_fold().unwrap();
        assert_eq!(mul, lhs);
    }

    #[rstest]
    fn mult_by_zero() {
        let lhs = c(0);
        let rhs = IRAexpr::IO(Slot::Arg(0.into()));
        let mut mul = IRAexpr::Product(Box::new(lhs.clone()), Box::new(rhs));
        mul.constant_fold().unwrap();
        assert_eq!(mul, lhs);
    }

    #[rstest]
    fn mult_by_zero_rev() {
        let rhs = c(0);
        let lhs = IRAexpr::IO(Slot::Arg(0.into()));
        let mut mul = IRAexpr::Product(Box::new(lhs), Box::new(rhs.clone()));
        mul.constant_fold().unwrap();
        assert_eq!(mul, rhs);
    }

    #[rstest]
    fn sum_identity() {
        let lhs = c(0);
        let rhs = IRAexpr::IO(Slot::Arg(0.into()));
        let mut sum = IRAexpr::Sum(Box::new(lhs), Box::new(rhs.clone()));
        sum.constant_fold().unwrap();
        assert_eq!(sum, rhs);
    }

    #[rstest]
    fn sum_identity_rev() {
        let rhs = c(0);
        let lhs = IRAexpr::IO(Slot::Arg(0.into()));
        let mut sum = IRAexpr::Sum(Box::new(lhs.clone()), Box::new(rhs));
        sum.constant_fold().unwrap();
        assert_eq!(sum, lhs);
    }
}
