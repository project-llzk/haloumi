#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use std::io::Write;

use codegen::LlzkCodegen;
use haloumi_backend::Backend;
use llzk::prelude::ModuleExt;
use melior::ir::Module;
use state::LlzkCodegenState;

pub use params::LlzkParams;

mod codegen;
mod counter;
pub mod error;
mod extras;
mod factory;
mod lowering;
mod params;
mod state;

/// Instance of a [`Backend`] prepared for lowering to LLZK.
pub type LlzkBackend<'c, 's> = Backend<LlzkCodegen<'c, 's>, LlzkCodegenState<'c>>;

/// Output produced by the LLZK backend.
#[derive(Debug)]
pub struct LlzkOutput<'c> {
    module: Module<'c>,
}

impl<'c> LlzkOutput<'c> {
    /// Returns the inner [`melior::ir::Module`].
    pub fn module(&self) -> &Module<'c> {
        &self.module
    }

    /// Writes the output as bytecode.
    ///
    /// This method is meant for clients that need to write the result of the LLZK backend but
    /// don't want to bring the `llzk` as a dependency.
    pub fn dump(&self, dest: &mut dyn Write) -> std::io::Result<()> {
        self.module.write_bytecode(dest)
    }
}

impl<'c> From<Module<'c>> for LlzkOutput<'c> {
    fn from(module: Module<'c>) -> Self {
        Self { module }
    }
}

impl std::fmt::Display for LlzkOutput<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.module.as_operation())
    }
}
