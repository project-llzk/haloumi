#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

pub mod auto_conf;
pub mod circuit;
pub mod cmp;
pub mod constraints;
pub mod eqv;
pub mod error;
pub mod expressions;
pub mod felt;
pub mod groups;
pub mod info_traits;
pub mod io;
pub mod layouter;
pub mod lookups;
pub mod query;
pub mod slot;
pub mod synthesis;
pub mod table;
pub mod types;
