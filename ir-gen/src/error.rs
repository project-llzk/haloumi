//! Error type.

use std::sync::Arc;

/// Errors raised during IR generation.
#[derive(Debug, thiserror::Error)]
#[error("ir generation failed: {0}")]
pub struct Error(Arc<dyn std::error::Error + Send + Sync + 'static>);

impl Error {
    pub(crate) fn new<E: std::error::Error + Send + Sync + 'static>(error: E) -> Self {
        Self(Arc::new(error))
    }
}
