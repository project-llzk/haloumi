#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use haloumi_ir_gen::circuit::resolved::ResolvedIRCircuit;

use crate::extractor::Extractor;

pub mod circuit;
pub mod error;
pub mod extractor;

/// Re-export of the inventory crate.
pub mod inventory {
    pub use inventory::*;
}

/// Re-export of the anyhow crate.
pub mod anyhow {
    pub use anyhow::*;
}

/// Output produced by a harness function.
pub type Output = anyhow::Result<ResolvedIRCircuit>;

/// Type representing the harness logic.
pub type HarnessFn = fn(&Extractor) -> Output;

/// Entry in the harness table.
#[derive(Copy, Clone, Debug)]
pub struct Harness(&'static str, HarnessFn);

impl Harness {
    /// Creates a new entry
    pub const fn new(name: &'static str, harness: HarnessFn) -> Self {
        Self(name, harness)
    }

    /// Returns the name of the entry.
    pub fn name(&self) -> &'static str {
        self.0
    }

    /// Runs the harness function with the given extractor.
    pub fn run(&self, extractor: &Extractor) -> Output {
        self.1(extractor)
    }
}

::inventory::collect!(Harness);
