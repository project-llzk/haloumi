//! Error types.

/// Generic error type emitted by the [`Driver`](crate::driver::Driver) wrapping the
/// concrete error.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Error raised during synthesis.
    #[error(transparent)]
    Synthesis(#[from] haloumi_synthesis::error::Error),
    /// Error raised during IR generation.
    #[error(transparent)]
    IRGen(#[from] haloumi_ir_gen::error::Error),
    #[cfg(feature = "picus-backend")]
    /// Error raised by the Picus backend.
    #[error(transparent)]
    Picus(#[from] haloumi_picus::PicusCodegenError),
    #[cfg(feature = "llzk-backend")]
    /// Error raise by the LLZK backend.
    #[error(transparent)]
    Llzk(#[from] haloumi_llzk::error::Error),
}
