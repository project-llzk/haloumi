#![doc = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/", env!("CARGO_PKG_README")))]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

pub mod driver;
pub mod error;

// This crate re-exports some of the other crates in order to reduce the number of crates clients
// may need to add to their dependencies list.

/// Re-export of `haloumi-ir`.
pub mod ir {
    pub use haloumi_ir::*;
}
/// Re-export of `haloumi-ir-gen`
pub mod ir_gen {
    pub use haloumi_ir_gen::*;
}
/// Re-export of `haloumi-synthesis`
pub mod synthesis {
    pub use haloumi_synthesis::*;
}
/// Re-export of `haloumi-core`
pub mod core {
    pub use haloumi_core::*;
}
