//! Types and macros for working with the extractor.

#[cfg(feature = "extractor")]
pub use haloumi_extractor::*;

/// Re-export of the extractor-core crate for simplifying dependency management in downstream clients.
pub mod core {
    pub use haloumi_extractor_core::*;
}

/// Generates a function that is expected to be in the root of the crate where the harness are
/// defined.
#[cfg(feature = "extractor")]
#[macro_export]
macro_rules! __impl_harnesses_root_function {
    ($name:ident) => {
        pub fn $name() -> impl Iterator<Item = &'static $crate::extractor::Harness> {
            $crateextractor::::inventory::iter::<$crate::extractor::Harness>()
        }
    };
}

/// Registers a harness in the registry.
#[cfg(feature = "extractor")]
#[macro_export]
macro_rules! register_harness {
    ($name:literal, $harness:path) => {
        $crate::extractor::inventory::submit!($crate::extractor::Harness::new($name, $harness));
    };
}

/// Registers a semantic prelude in the registry.
#[cfg(feature = "extractor")]
#[macro_export]
macro_rules! register_prelude {
    ($name:literal, $prelude:path) => {
        $crate::extractor::inventory::submit!($crate::extractor::PreludeEntry::new(
            $name, $prelude
        ));
    };
}
