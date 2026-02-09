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
#[derive(PartialEq, Eq, Clone)]
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
            IRAexprImpl::Sum(lhs, rhs) | IRAexprImpl::Product(lhs, rhs) => {
                lhs.canonicalize();
                rhs.canonicalize();
            }
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

impl std::fmt::Debug for IRAexpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.0, f)
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
mod tests {
    use super::*;
    use crate::{
        printer::IRPrinter,
        test_utils::{MockCellOutput, MockTestExprLowering},
    };
    use haloumi_core::slot::arg::ArgNo;
    use mockall::predicate;
    use rstest::rstest;

    use ff::PrimeField;

    /// Implementation of BabyBear used for testing.
    #[derive(PrimeField)]
    #[PrimeFieldModulus = "2013265921"]
    #[PrimeFieldGenerator = "31"]
    #[PrimeFieldReprEndianness = "little"]
    pub struct BabyBear([u64; 1]);

    const BABYBEAR: u64 = 2013265921;

    /// Creates a constant felt under BabyBear
    fn f(v: impl Into<BabyBear>) -> Felt {
        Felt::from(v.into())
    }

    /// Creates a constant value under BabyBear
    fn c(v: impl Into<BabyBear>) -> IRAexpr {
        IRAexpr::constant(f(v))
    }

    /// Creates a slot expression with the given value as argument number.
    fn arg(n: usize) -> IRAexpr {
        IRAexpr::slot(ArgNo::from(n))
    }

    /// Creates a slot expression for a relative advice cell reference.
    fn rel(col: usize, base: usize, offset: usize) -> IRAexpr {
        Slot::advice_rel(col, base, offset).into()
    }

    /// Creates a slot expression for an absolute advice cell reference.
    fn abs(col: usize, row: usize) -> IRAexpr {
        Slot::advice_abs(col, row).into()
    }

    #[rstest]
    #[case::within_field(c(5), c(5))]
    #[case::outside_field(c(BABYBEAR + 1), c(1))]
    fn fold_constant(#[case] mut test: IRAexpr, #[case] expected: IRAexpr) {
        test.constant_fold().unwrap();
        assert_eq!(test, expected);
    }

    #[rstest]
    #[case(c(1), arg(0), arg(0))]
    #[case(arg(0), c(1), arg(0))]
    #[case(c(0), arg(0), c(0))]
    #[case(arg(0), c(0), c(0))]
    #[case(c(BABYBEAR - 1), arg(0), -arg(0))]
    #[case(arg(0), c(BABYBEAR - 1), -arg(0))]
    #[case(c(2), c(4), c(8))]
    #[case(c(2), arg(2), c(2) * arg(2))]
    fn fold_mult(#[case] lhs: IRAexpr, #[case] rhs: IRAexpr, #[case] expected: IRAexpr) {
        let mut mul = lhs * rhs;
        mul.constant_fold().unwrap();
        assert_eq!(mul, expected);
    }

    #[rstest]
    #[case(c(0), arg(0), arg(0))]
    #[case(arg(0), c(0), arg(0))]
    #[case(c(2), c(2), c(4))]
    #[case(c(2), arg(2), c(2) + arg(2))]
    fn fold_sum(#[case] lhs: IRAexpr, #[case] rhs: IRAexpr, #[case] expected: IRAexpr) {
        let mut sum = lhs + rhs;
        sum.constant_fold().unwrap();
        assert_eq!(sum, expected);
    }

    #[rstest]
    #[case(c(0), c(0))]
    #[case(c(10), c(BABYBEAR - 10))]
    #[case(arg(0), -arg(0))]
    fn fold_neg(#[case] expr: IRAexpr, #[case] expected: IRAexpr) {
        let mut neg = -expr;
        neg.constant_fold().unwrap();
        assert_eq!(neg, expected);
    }

    #[rstest]
    #[case(-(-c(1)), c(1))]
    #[case(-c(1), -c(1))]
    #[case(arg(1), arg(1))]
    #[case(-(-arg(1)), arg(1))]
    #[case(-(-arg(1)) + c(1), arg(1) + c(1))]
    #[case(c(2) + -(-arg(1)), c(2) + arg(1))]
    #[case(-(-arg(1)) * c(2), arg(1) * c(2))]
    #[case(c(2) * -(-arg(1)), c(2) * arg(1))]
    // Test canonicalization doesn't fold constants. That's the constant folder's job.
    #[case(arg(1) + c(0), arg(1) + c(0))]
    #[case(arg(1) * c(1), arg(1) * c(1))]
    #[case(arg(1) * c(0), arg(1) * c(0))]
    fn canon(#[case] mut expr: IRAexpr, #[case] expected: IRAexpr) {
        expr.canonicalize();
        assert_eq!(expr, expected);
    }

    #[derive(thiserror::Error, Debug)]
    #[error("mock error")]
    struct MockError;

    fn do_nothing(_: &mut Slot) -> Result<(), MockError> {
        Ok(())
    }

    fn fail(_: &mut Slot) -> Result<(), MockError> {
        Err(MockError)
    }

    #[rstest]
    #[case(c(0), c(0), do_nothing)]
    #[case(arg(0), arg(0), do_nothing)]
    #[case(-c(0), -c(0), do_nothing)]
    #[case(-arg(0), -arg(0), do_nothing)]
    #[case(c(0) + c(0), c(0) + c(0), do_nothing)]
    #[case(c(0) * c(0), c(0) * c(0), do_nothing)]
    #[case(arg(0) + c(0), arg(0) + c(0), do_nothing)]
    #[case(arg(0) * c(0), arg(0) * c(0), do_nothing)]
    #[case(c(0) + arg(0), c(0) + arg(0), do_nothing)]
    #[case(c(0) * arg(0), c(0) * arg(0), do_nothing)]
    #[case(arg(0) + arg(0), arg(0) + arg(0), do_nothing)]
    #[case(arg(0) * arg(0), arg(0) * arg(0), do_nothing)]
    #[case(c(0), c(0), fail)]
    #[should_panic(expected = "MockError")]
    #[case(arg(0), arg(0), fail)]
    #[case(-c(0), -c(0), fail)]
    #[should_panic(expected = "MockError")]
    #[case(-arg(0), -arg(0), fail)]
    #[case(c(0) + c(0), c(0) + c(0), fail)]
    #[case(c(0) * c(0), c(0) * c(0), fail)]
    #[should_panic(expected = "MockError")]
    #[case(arg(0) + c(0), arg(0) + c(0), fail)]
    #[should_panic(expected = "MockError")]
    #[case(arg(0) * c(0), arg(0) * c(0), fail)]
    #[should_panic(expected = "MockError")]
    #[case(c(0) + arg(0), c(0) + arg(0), fail)]
    #[should_panic(expected = "MockError")]
    #[case(c(0) * arg(0), c(0) * arg(0), fail)]
    #[should_panic(expected = "MockError")]
    #[case(arg(0) + arg(0), arg(0) + arg(0), fail)]
    #[should_panic(expected = "MockError")]
    #[case(arg(0) * arg(0), arg(0) * arg(0), fail)]
    fn map_io(
        #[case] mut test: IRAexpr,
        #[case] expected: IRAexpr,
        #[case] f: fn(&mut Slot) -> Result<(), MockError>,
    ) {
        test.try_map_io(&f).unwrap();
        assert_eq!(test, expected);
    }

    #[test]
    fn test_from_slot() {
        let arg = ArgNo::from(0);
        let slot = Slot::from(arg);
        let test = IRAexpr::from(slot);
        let expected = IRAexpr::slot(arg);
        assert_eq!(test, expected);
    }

    #[rstest]
    #[case(c(0), "0")]
    #[case(arg(0), "arg0")]
    #[case(-c(0), "(- 0)")]
    #[case(arg(0) + c(1), "(+ arg0 1)")]
    #[case(arg(0) * c(1), "(* arg0 1)")]
    fn test_debug(#[case] expr: IRAexpr, #[case] expected: &'static str) {
        let test = format!("{expr:?}");
        assert_eq!(test, expected);
    }

    #[rstest]
    #[case(c(0), "(const 0)")]
    #[case(arg(0), "(input 0)")]
    #[case(-arg(0), "(- (input 0))")]
    #[case(arg(0) + c(2), "(+ (input 0) (const 2))")]
    #[case(arg(0) + -c(2), "(+ (input 0)\n   (- (const 2)))")]
    #[case(arg(0) + c(2) + arg(1), "(+ \n   (+ (input 0) (const 2))\n   (input 1))")]
    #[case(arg(0) * c(2), "(* (input 0) (const 2))")]
    #[case(arg(0) * c(2) * arg(1), "(* \n   (* (input 0) (const 2))\n   (input 1))")]
    fn test_ir_printable(#[case] expr: IRAexpr, #[case] expected: &'static str) {
        let printer = IRPrinter::from(&expr);
        let test = format!("{printer}");
        assert_eq!(test, expected);
    }

    #[rstest]
    #[case(c(0), ExprProperty::Const.into())]
    #[case(-c(0), ExprProperty::Const.into())]
    #[case(c(0) + c(1), ExprProperty::Const.into())]
    #[case(c(0) * c(1), ExprProperty::Const.into())]
    #[case(arg(0), ExprProperties::default())]
    #[case(-arg(0), ExprProperties::default())]
    #[case(arg(0) + c(0), ExprProperties::default())]
    #[case(arg(0) * c(0), ExprProperties::default())]
    #[case(c(0) + arg(0), ExprProperties::default())]
    #[case(c(0) * arg(0), ExprProperties::default())]
    fn test_expr_properties(#[case] expr: IRAexpr, #[case] expected: ExprProperties) {
        let output: ExprProperties = expr.evaluate();
        assert_eq!(output, expected);
    }

    #[rstest]
    #[case(c(0), c(0), true)]
    #[case(c(0), arg(0), false)]
    #[case(c(0), c(1), false)]
    #[case(arg(0), arg(1), false)]
    #[case(arg(0), arg(0), true)]
    #[case(rel(0, 5, 3), rel(0, 5, 3), true)]
    #[case(rel(0, 5, 3), rel(0, 5, 4), false)]
    #[case(rel(0, 5, 3), rel(0, 10, 3), true)]
    #[case(rel(0, 5, 3), abs(0, 8), true)]
    #[case(rel(0, 5, 3), abs(0, 10), false)]
    #[case(-c(0), -c(0), true)]
    #[case(-c(0), -c(1), false)]
    #[case(-arg(0), -arg(1), false)]
    #[case(-arg(0), -arg(0), true)]
    #[case(-rel(0, 5, 3), -rel(0, 5, 3), true)]
    #[case(-rel(0, 5, 3), -rel(0, 5, 4), false)]
    #[case(-rel(0, 5, 3), -rel(0, 10, 3), true)]
    #[case(-rel(0, 5, 3), -abs(0, 8), true)]
    #[case(-rel(0, 5, 3), -abs(0, 10), false)]
    #[case(c(0) + c(1), c(0) + c(1), true)]
    #[case(c(0) + c(1), c(1) + c(1), false)]
    #[case(arg(0) + c(1), arg(1) + c(1), false)]
    #[case(arg(0) + c(1), arg(0) + c(1), true)]
    #[case(rel(0, 5, 3) + c(1), rel(0, 5, 3) + c(1), true)]
    #[case(rel(0, 5, 3) + c(1), rel(0, 5, 4) + c(1), false)]
    #[case(rel(0, 5, 3) + c(1), rel(0, 10, 3) + c(1), true)]
    #[case(rel(0, 5, 3) + c(1), abs(0, 8) + c(1), true)]
    #[case(rel(0, 5, 3) + c(1), abs(0, 10) + c(1), false)]
    #[case(c(0) * c(1), c(0) * c(1), true)]
    #[case(c(0) * c(1), c(1) * c(1), false)]
    #[case(arg(0) * c(1), arg(1) * c(1), false)]
    #[case(arg(0) * c(1), arg(0) * c(1), true)]
    #[case(rel(0, 5, 3) * c(1), rel(0, 5, 3) * c(1), true)]
    #[case(rel(0, 5, 3) * c(1), rel(0, 5, 4) * c(1), false)]
    #[case(rel(0, 5, 3) * c(1), rel(0, 10, 3) * c(1), true)]
    #[case(rel(0, 5, 3) * c(1), abs(0, 8) * c(1), true)]
    #[case(rel(0, 5, 3) * c(1), abs(0, 10) * c(1), false)]
    fn test_eqv(#[case] lhs: IRAexpr, #[case] rhs: IRAexpr, #[case] expected: bool) {
        let output = SymbolicEqv::equivalent(&lhs, &rhs);
        assert_eq!(output, expected);
    }

    #[rstest]
    #[case(c(0), Some(f(0)))]
    #[case(-c(1), Some(f(BABYBEAR - 1)))]
    #[case(arg(0), None)]
    #[case(-arg(0), None)]
    #[case(c(10) + c(20), Some(f(30)))]
    #[case(arg(0) + c(0), None)]
    #[case(c(0) + arg(0), None)]
    #[case(c(10) * c(2), Some(f(20)))]
    #[case(arg(0) * c(0), None)]
    #[case(c(0) * arg(0), None)]
    fn test_evaluate(#[case] expr: IRAexpr, #[case] expected: Option<Felt>) {
        let output: Option<Felt> = expr.evaluate();
        assert_eq!(output, expected);
    }

    #[test]
    fn test_lowering_const() {
        let body = |f| Ok(MockCellOutput::Const(0, f));
        let mut lowering = MockTestExprLowering::new();
        lowering
            .expect_lower_constant()
            .with(predicate::eq(f(0)))
            .times(1)
            .returning(body);
        let expr = c(0);
        let output = expr.lower(&lowering).unwrap();
        assert_eq!(output, body(f(0)).unwrap());
    }

    #[test]
    fn test_lowering_slot() {
        let body = |s| Ok(MockCellOutput::Slot(0, s));
        let mut lowering = MockTestExprLowering::new();
        lowering
            .expect_lower_funcio()
            .with(predicate::eq(Slot::from(ArgNo::from(0))))
            .times(1)
            .returning(body);
        let expr = arg(0);
        let output = expr.lower(&lowering).unwrap();
        assert_eq!(output, body(ArgNo::from(0).into()).unwrap());
    }

    #[test]
    fn test_lowering_neg() {
        let body_lower_funcio = |s| Ok(MockCellOutput::Slot(0, s));
        let body_lower_neg = |e: &MockCellOutput| Ok(MockCellOutput::Neg(1, e.id()));
        let mut lowering = MockTestExprLowering::new();
        let slot = Slot::from(ArgNo::from(0));
        lowering
            .expect_lower_funcio()
            .with(predicate::eq(slot))
            .times(1)
            .returning(body_lower_funcio);
        let slot_output = body_lower_funcio(slot).unwrap();
        lowering
            .expect_lower_neg()
            .with(predicate::eq(slot_output))
            .times(1)
            .returning(body_lower_neg);
        let expr = -arg(0);
        let output = expr.lower(&lowering).unwrap();
        assert_eq!(output, body_lower_neg(&slot_output).unwrap());
    }

    #[test]
    fn test_lowering_sum() {
        let body_lower_constant = |f| Ok(MockCellOutput::Const(0, f));
        let body_lower_funcio = |s| Ok(MockCellOutput::Slot(1, s));
        let body_lower_sum = |lhs: &MockCellOutput, rhs: &MockCellOutput| {
            Ok(MockCellOutput::Sum(2, lhs.id(), rhs.id()))
        };
        let mut lowering = MockTestExprLowering::new();
        let constant = f(0);
        let slot = Slot::from(ArgNo::from(0));
        lowering
            .expect_lower_constant()
            .with(predicate::eq(constant))
            .times(1)
            .returning(body_lower_constant);
        let constant_output = body_lower_constant(constant).unwrap();
        lowering
            .expect_lower_funcio()
            .with(predicate::eq(slot))
            .times(1)
            .returning(body_lower_funcio);
        let slot_output = body_lower_funcio(slot).unwrap();
        lowering
            .expect_lower_sum()
            .with(predicate::eq(constant_output), predicate::eq(slot_output))
            .times(1)
            .returning(body_lower_sum);
        let expr = c(0) + arg(0);
        let output = expr.lower(&lowering).unwrap();
        assert_eq!(
            output,
            body_lower_sum(&constant_output, &slot_output).unwrap()
        );
    }

    #[test]
    fn test_lowering_product() {
        let body_lower_constant = |f| Ok(MockCellOutput::Const(0, f));
        let body_lower_funcio = |s| Ok(MockCellOutput::Slot(1, s));
        let body_lower_product = |lhs: &MockCellOutput, rhs: &MockCellOutput| {
            Ok(MockCellOutput::Product(2, lhs.id(), rhs.id()))
        };
        let mut lowering = MockTestExprLowering::new();
        let constant = f(0);
        let slot = Slot::from(ArgNo::from(0));
        lowering
            .expect_lower_constant()
            .with(predicate::eq(constant))
            .times(1)
            .returning(body_lower_constant);
        let constant_output = body_lower_constant(constant).unwrap();
        lowering
            .expect_lower_funcio()
            .with(predicate::eq(slot))
            .times(1)
            .returning(body_lower_funcio);
        let slot_output = body_lower_funcio(slot).unwrap();
        lowering
            .expect_lower_product()
            .with(predicate::eq(constant_output), predicate::eq(slot_output))
            .times(1)
            .returning(body_lower_product);
        let expr = c(0) * arg(0);
        let output = expr.lower(&lowering).unwrap();
        assert_eq!(
            output,
            body_lower_product(&constant_output, &slot_output).unwrap()
        );
    }
}
