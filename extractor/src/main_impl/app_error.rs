//! Tool level errors.

use std::fmt;

#[allow(clippy::enum_variant_names)]
#[derive(Debug)]
enum AppErrorKind {
    HarnessFailed,
    OptFailed,
    IRDumpFailed,
    PicusWriteFailed,
    LlzkWriteFailed,
}

/// Helper for creating errors related to the main tool.
#[derive(Debug)]
pub struct AppError {
    kind: AppErrorKind,
    name: &'static str,
    err: anyhow::Error,
}

impl AppError {
    fn create<E: Into<anyhow::Error>>(
        name: &'static str,
        kind: AppErrorKind,
    ) -> impl FnOnce(E) -> Self {
        move |err| Self {
            kind,
            name,
            err: err.into(),
        }
    }

    pub(crate) fn harness<E: Into<anyhow::Error>>(name: &'static str) -> impl FnOnce(E) -> Self {
        Self::create(name, AppErrorKind::HarnessFailed)
    }

    pub(crate) fn opt<E: Into<anyhow::Error>>(name: &'static str) -> impl FnOnce(E) -> Self {
        Self::create(name, AppErrorKind::OptFailed)
    }

    pub(crate) fn ir_dump<E: Into<anyhow::Error>>(name: &'static str) -> impl FnOnce(E) -> Self {
        Self::create(name, AppErrorKind::IRDumpFailed)
    }

    pub(crate) fn picus<E: Into<anyhow::Error>>(name: &'static str) -> impl FnOnce(E) -> Self {
        Self::create(name, AppErrorKind::PicusWriteFailed)
    }

    pub(crate) fn llzk<E: Into<anyhow::Error>>(name: &'static str) -> impl FnOnce(E) -> Self {
        Self::create(name, AppErrorKind::LlzkWriteFailed)
    }
}

impl fmt::Display for AppError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            AppErrorKind::HarnessFailed => {
                write!(f, "Harness {} failed: {:?}", self.name, self.err)
            }
            AppErrorKind::OptFailed => write!(
                f,
                "IR optimization pass failed for harness {}: {:?}",
                self.name, self.err
            ),
            AppErrorKind::IRDumpFailed => write!(
                f,
                "Failed to write IR dump of harness {}: {:?}",
                self.name, self.err
            ),
            AppErrorKind::PicusWriteFailed => write!(
                f,
                "Failed to write Picus result of harness {}: {:?}",
                self.name, self.err
            ),
            AppErrorKind::LlzkWriteFailed => write!(
                f,
                "Failed to write Llzk result of harness {}: {:?}",
                self.name, self.err
            ),
        }
    }
}

impl std::error::Error for AppError {}
unsafe impl Sync for AppError {}
unsafe impl Send for AppError {}
