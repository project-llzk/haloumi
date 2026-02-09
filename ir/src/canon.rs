//! Functions related to canonicalization of the IR.

use crate::expr::{IRAexpr, IRAexprImpl};
use haloumi_core::cmp::CmpOp;

/// Matches the sum part of [`canonicalize_constraint`].
fn match_sum(sum_lhs: &IRAexpr, sum_rhs: &IRAexpr) -> Option<(CmpOp, IRAexpr, IRAexpr)> {
    if let IRAexprImpl::Negated(y) = &sum_rhs.0 {
        return Some((CmpOp::Eq, sum_lhs.clone(), (**y).clone()));
    }
    if let IRAexprImpl::Negated(y) = &sum_lhs.0 {
        return Some((CmpOp::Eq, (**y).clone(), sum_rhs.clone()));
    }
    None
}

pub fn canonicalize_constraint(
    op: CmpOp,
    lhs: &IRAexpr,
    rhs: &IRAexpr,
) -> Option<(CmpOp, IRAexpr, IRAexpr)> {
    match (op, &lhs.0, &rhs.0) {
        // (= (+ X (- Y)) 0) => (= X Y) OR (= (+ (- X) Y) 0) => (= X Y)
        (CmpOp::Eq, IRAexprImpl::Sum(sum_lhs, sum_rhs), IRAexprImpl::Constant(zero))
            if *zero == 0usize =>
        {
            match_sum(sum_lhs, sum_rhs)
        }
        // (= (* 1 (+ X (- Y))) 0) => (= X Y) OR (= (* 1 (+ (- X) Y)) 0) => (= X Y)
        (CmpOp::Eq, IRAexprImpl::Product(mul_lhs, mul_rhs), IRAexprImpl::Constant(zero))
            if *zero == 0usize =>
        {
            match (&mul_lhs.0, &mul_rhs.0) {
                (IRAexprImpl::Constant(one), IRAexprImpl::Sum(sum_lhs, sum_rhs))
                    if *one == 1usize =>
                {
                    match_sum(sum_lhs, sum_rhs)
                }
                _ => None,
            }
        }
        // Nothing matched
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::IRAexpr;
    use haloumi_core::cmp::CmpOp;
    use haloumi_core::felt::Felt;
    use haloumi_core::slot::Slot;

    use ff::PrimeField;
    use rstest::rstest;

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

    fn x() -> IRAexpr {
        IRAexpr(IRAexprImpl::IO(Slot::Arg(0.into())))
    }

    fn y() -> IRAexpr {
        IRAexpr(IRAexprImpl::IO(Slot::Arg(0.into())))
    }

    #[rstest]
    // (= (+ X (- Y)) 0) => (= X Y)
    #[case(x() + -y())]
    // (= (+ (- X) Y) 0) => (= X Y)
    #[case(-x() + y())]
    // (= (* 1 (+ X (- Y))) 0) => (= X Y)
    #[case(c(1) * (x() + -y()))]
    // (= (* 1 (+ (- X) Y)) 0) => (= X Y)
    #[case(c(1) * (-x() + y()))]
    fn test_subtraction_to_equal(#[case] e: IRAexpr) {
        let expected = Some((CmpOp::Eq, x(), y()));
        let output = canonicalize_constraint(CmpOp::Eq, &e, &c(0));
        similar_asserts::assert_eq!(expected, output);
    }

    #[rstest]
    #[case(x() + y())]
    #[case(x() * y())]
    #[case(c(1) * (x() + y()))]
    fn test_no_match(#[case] e: IRAexpr) {
        let output = canonicalize_constraint(CmpOp::Eq, &e, &c(0));
        similar_asserts::assert_eq!(None, output);
    }

    #[rstest]
    #[case(x() + y())]
    fn match_lhs_not_zero(#[case] e: IRAexpr) {
        let output = canonicalize_constraint(CmpOp::Eq, &e, &c(1));
        similar_asserts::assert_eq!(None, output);
    }
}
