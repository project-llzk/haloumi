//! Core types related to LLZK.
//!
//! The types here must not bring the LLZK backend, LLZK itself or related libraries as
//! dependencies.

/// Possible output formats for LLZK
#[derive(Debug, PartialEq, Eq, Default, Hash)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Deserialize),
    serde(rename_all = "lowercase")
)]
pub enum LlzkOutputFormat {
    /// Human readable IR format used in MLIR.
    Assembly,
    /// Bytecode format used in MLIR.
    #[default]
    Bytecode,
}

impl std::fmt::Display for LlzkOutputFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                LlzkOutputFormat::Assembly => "assembly",
                LlzkOutputFormat::Bytecode => "bytecode",
            }
        )
    }
}
