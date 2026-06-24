//! Types related to PLONK gates.

use std::fmt;

use haloumi_core::info_traits::GateInfo;

/// Information about a gate in the constraint system.
///
/// Is parameterized by the expression type used to represent polynomials.
pub struct Gate<E> {
    name: String,
    polynomials: Vec<E>,
}

impl<E> Gate<E> {
    /// Creates a new gate.
    pub fn new(info: &dyn GateInfo<E>) -> Self
    where
        E: Clone,
    {
        Self {
            name: info.name().to_string(),
            polynomials: info.polynomials().to_vec(),
        }
    }

    /// Returns the name of the gate.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the polynomials of the gate.
    pub fn polynomials(&self) -> &[E] {
        &self.polynomials
    }
}

impl<E: fmt::Debug> fmt::Debug for Gate<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Gate")
            .field("name", &self.name)
            .field("polynomials", &self.polynomials)
            .finish()
    }
}
