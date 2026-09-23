//! Base context for IO operations.

use std::fmt;

use crate::{error::Error, io::error::IoError};

/// Context type for the [`LoadFromCells`](super::load::LoadFromCells) and
/// [`StoreIntoCells`](super::store::StoreIntoCells) traits.
pub struct BaseCtx<'io, IO> {
    io: Box<dyn Iterator<Item = IO> + 'io>,
}

impl<'io, IO> BaseCtx<'io, IO> {
    /// Creates a new IO context.
    pub fn new(io: impl Iterator<Item = IO> + 'io) -> Self {
        Self { io: Box::new(io) }
    }

    /// Returns the next IO object or fails if there aren't any more objects.
    pub fn next(&mut self) -> Result<IO, Error> {
        self.io
            .next()
            .ok_or_else(|| IoError::NotEnoughIOCells.into())
    }
}

impl<IO> fmt::Debug for BaseCtx<'_, IO> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BaseCtx")
            .field("io", &"<iterator>")
            .finish()
    }
}
