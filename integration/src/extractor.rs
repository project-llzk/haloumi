//! Types and macros for working with the extractor.

pub use haloumi_extractor::extractor::Extractor;

/// Re-export of haloumi_extractor::circuit
pub mod circuit {
    pub use ::haloumi_extractor::circuit::*;
}

/// Re-export of the inventory crate.
pub mod inventory {
    pub use ::inventory::*;
}

/// Re-export of the anyhow crate.
pub mod anyhow {
    pub use ::anyhow::*;
}

/// Generates a function that is expected to be in the root of the crate where the harness are
/// defined.
#[macro_export]
macro_rules! __impl_harnesses_root_function {
    ($extractor_crate:ident, $name:ident) => {
        pub fn $name() -> impl Iterator<Item = &'static $extractor_crate::Harness> {
            $extractor_crate::inventory::iter::<$extractor_crate::Harness>()
        }
    };
}

/// Output produced by a harness function.
pub type Output = ResolvedIRCircuit;

/// Type representing the harness logic.
pub type HarnessFn = fn(&Extractor) -> anyhow::Result<Output>;

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
    fn run(&self, extractor: &Extractor) -> anyhow::Result<Output> {
        self.1(extractor)
    }
}

::inventory::collect!(Harness);

/// Registers a harness in the registry.
#[macro_export]
macro_rules! register_harness {
    ($name:literal, $harness:path) => {
        $crate::inventory::submit!($crate::Harness::new($name, $harness));
    };
}
