//! Macros for working with the extractor.

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
