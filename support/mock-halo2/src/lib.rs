//! Minimal, deterministic circuit metadata used by Haloumi extractor tests.
//!
//! This crate deliberately models only the information Haloumi consumes while
//! extracting a circuit.  It is not a Halo2 implementation and performs no
//! proving or witness validation.

pub mod circuit;
pub mod plonk;

pub mod poly {
    pub use haloumi_core::table::Rotation;
}
