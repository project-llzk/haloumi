//! Types and macros for working with the extractor.

#[cfg(feature = "extractor")]
pub use haloumi_extractor::*;

/// Re-export of the extractor-core crate for simplifying dependency management in downstream clients.
pub mod core {
    pub use haloumi_extractor_core::*;
}

/// Generates a function that is expected to be in the root of the crate where the harness are
/// defined.
#[macro_export]
macro_rules! __impl_harnesses_root_function {
    ($name:ident) => {
        pub fn $name() -> impl Iterator<Item = &'static $crate::extractor::Harness> {
            $crateextractor::::inventory::iter::<$crate::extractor::Harness>()
        }
    };
}

/// Registers a harness in the registry.
#[macro_export]
macro_rules! register_harness {
    ($name:literal, $harness:path) => {
        $crate::extractor::inventory::submit!($crate::Harness::new($name, $harness));
    };
}
