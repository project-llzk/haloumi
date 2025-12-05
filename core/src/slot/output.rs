//! Types related to circuit outputs.

use std::{fmt, ops::Deref};

/// An identifier that backends use to identify an output in the circuit.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct OutputId(usize);

impl From<usize> for OutputId {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

impl OutputId {
    /// Offsets the field number by the given amount.
    pub fn offset_by(self, offset: usize) -> Self {
        Self(self.0 + offset)
    }
}

impl Deref for OutputId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl fmt::Display for OutputId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for OutputId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "field{}", self.0)
    }
}
