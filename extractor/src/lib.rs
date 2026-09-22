#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use ff::PrimeField;
use haloumi_ir_gen::circuit::resolved::ResolvedIRCircuit;

use crate::extractor::Extractor;

pub mod circuit;
pub mod error;
pub mod extractor;
pub mod main_impl;
