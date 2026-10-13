//! Types related to circuit inputs.

use std::{fmt, ops::Deref};

/// An identifier that backends use to identify an input in the circuit.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ArgNo(usize);

impl From<usize> for ArgNo {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

#[cfg(any(test, feature = "arbitrary"))]
impl quickcheck::Arbitrary for ArgNo {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        Self::from(usize::arbitrary(g))
    }
}

impl Deref for ArgNo {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ArgNo {
    /// Offsets the argument number by the given amount.
    pub fn offset_by(self, offset: usize) -> Self {
        Self(self.0 + offset)
    }
}

impl fmt::Display for ArgNo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for ArgNo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "arg{}", self.0)
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "serde")]
    use quickcheck_macros::quickcheck;

    use super::*;

    #[cfg(feature = "serde")]
    #[quickcheck]
    fn arg_no_round_trips(value: ArgNo) {
        assert_eq!(value, crate::serde_tests_helpers::round_trip(value));
    }
}
