//! Minimal, deterministic circuit metadata used by Haloumi extractor tests.
//!
//! This crate deliberately models only the information Haloumi consumes while
//! extracting a circuit.  It is not a Halo2 implementation and performs no
//! proving or witness validation.

use haloumi_integration::Types;

pub mod circuit;
pub mod plonk;
pub mod utils;

pub mod poly {
    pub use haloumi_core::table::Rotation;
}

#[derive(Debug)]
pub struct ExtractionSupport;

impl<F: ff::Field> Types<F> for ExtractionSupport {
    type InstanceCol = crate::plonk::Column<crate::plonk::Instance>;

    type AdviceCol = crate::plonk::Column<crate::plonk::Advice>;

    type Cell = crate::circuit::Cell;

    type AssignedCell<V> = crate::circuit::AssignedCell<V, F>;

    type Region<'a> = crate::circuit::Region<'a, F>;

    type Error = crate::plonk::Error;

    type RegionIndex = crate::circuit::RegionIndex;

    type Expression = crate::plonk::Expression<F>;

    type Rational = crate::utils::rational::Rational<F>;
}
