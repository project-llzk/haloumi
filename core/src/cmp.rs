//! Comparison IR operator.

/// Comparison operators between arithmetic expressions.
#[derive(Copy, Clone, PartialEq, Eq, Debug, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CmpOp {
    /// Equality
    Eq,
    /// Less than
    Lt,
    /// Less than or equal
    Le,
    /// Greater than
    Gt,
    /// Greater than or equal
    Ge,
    /// Not equal
    Ne,
}

#[cfg(any(test, feature = "arbitrary"))]
impl quickcheck::Arbitrary for CmpOp {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        match u8::arbitrary(g) % 5 {
            0 => Self::Eq,
            1 => Self::Lt,
            2 => Self::Le,
            3 => Self::Gt,
            _ => Self::Ge,
        }
    }
}

impl std::fmt::Display for CmpOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                CmpOp::Eq => "==",
                CmpOp::Lt => "<",
                CmpOp::Le => "<=",
                CmpOp::Gt => ">",
                CmpOp::Ge => ">=",
                CmpOp::Ne => "!=",
            }
        )
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "serde")]
    use quickcheck_macros::quickcheck;

    use super::*;

    #[cfg(feature = "serde")]
    #[quickcheck]
    fn comparison_operator_round_trip(cmp: CmpOp) {
        assert_eq!(cmp, crate::serde_tests_helpers::round_trip(cmp));
    }
}
