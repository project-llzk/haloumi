//! Types and macros for working with the extractor.

/// Re-export of the extractor-core crate for simplifying dependency management in downstream clients.
pub mod core {
    pub use haloumi_extractor_core::*;
}
