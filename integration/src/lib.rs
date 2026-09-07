#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

pub mod expressions;
pub mod groups;
pub mod info_traits;
pub mod table;

/// Re-export of the core crate for simplifying dependency management in downstream clients.
pub mod core {
    pub use haloumi_core::*;
}

pub use haloumi_integration_macros::*;
