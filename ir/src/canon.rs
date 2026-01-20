//! Functions related to canonicalization of the IR.

use crate::expr::IRAexpr;
use haloumi_core::cmp::CmpOp;

pub fn canonicalize_constraint(
    op: CmpOp,
    lhs: &IRAexpr,
    rhs: &IRAexpr,
) -> Option<(CmpOp, IRAexpr, IRAexpr)> {
    match (op, lhs, rhs) {
        // (= (+ X (- Y)) 0) => (= X Y) OR (= (+ (- X) Y) 0) => (= X Y)
        (CmpOp::Eq, IRAexpr::Sum(sum_lhs, sum_rhs), IRAexpr::Constant(zero)) if *zero == 0usize => {
            if let IRAexpr::Negated(y) = &**sum_rhs {
                return Some((CmpOp::Eq, (**sum_lhs).clone(), (**y).clone()));
            }
            if let IRAexpr::Negated(y) = &**sum_lhs {
                return Some((CmpOp::Eq, (**y).clone(), (**sum_rhs).clone()));
            }
            None
        }
        // (= (* 1 (+ X (- Y))) 0) => (= X Y) OR (= (* 1 (+ (- X) Y)) 0) => (= X Y)
        (CmpOp::Eq, IRAexpr::Product(mul_lhs, mul_rhs), IRAexpr::Constant(zero))
            if *zero == 0usize =>
        {
            match (&**mul_lhs, &**mul_rhs) {
                (IRAexpr::Constant(one), IRAexpr::Sum(sum_lhs, sum_rhs)) if *one == 1usize => {
                    if let IRAexpr::Negated(y) = &**sum_rhs {
                        return Some((CmpOp::Eq, (**sum_lhs).clone(), (**y).clone()));
                    }
                    if let IRAexpr::Negated(y) = &**sum_lhs {
                        return Some((CmpOp::Eq, (**y).clone(), (**sum_rhs).clone()));
                    }
                    None
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

    #[test]
    fn test_subtraction_to_equal() {
        let x = IRAexpr::IO(Slot::Arg(0.into()));
        let y = IRAexpr::IO(Slot::Arg(1.into()));
        {
            // (= (+ X (- Y)) 0) => (= X Y)
            let output = canonicalize_constraint(
                CmpOp::Eq,
                &IRAexpr::Sum(
                    Box::new(x.clone()),
                    Box::new(IRAexpr::Negated(Box::new(y.clone()))),
                ),
                &c(0),
            );
            let expected = Some((CmpOp::Eq, x.clone(), y.clone()));
            similar_asserts::assert_eq!(expected, output);
        }
        {
            //  (= (+ (- X) Y) 0) => (= X Y)
            let output = canonicalize_constraint(
                CmpOp::Eq,
                &IRAexpr::Sum(
                    Box::new(IRAexpr::Negated(Box::new(x.clone()))),
                    Box::new(y.clone()),
                ),
                &c(0),
            );
            let expected = Some((CmpOp::Eq, x.clone(), y.clone()));
            similar_asserts::assert_eq!(expected, output);
        }
    }
}
