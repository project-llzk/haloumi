//! Types for handling references to cells in the PLONK table.

use std::fmt;

use thiserror::Error;

use crate::eqv::{EqvRelation, SymbolicEqv};

/// Used for comparing cells' offsets.
#[derive(Copy, Clone, Eq, PartialEq)]
enum Offset {
    Rel(usize),
    Abs(usize),
}

/// A reference to a cell in the circuit.
#[derive(Clone, Copy, Eq, PartialOrd, Ord)]
pub struct CellRef {
    col: usize,
    base: Option<usize>,
    offset: usize,
}

impl CellRef {
    /// Creates a new cell reference using absolute coordinates.
    pub fn absolute(col: usize, row: usize) -> Self {
        Self {
            col,
            base: None,
            offset: row,
        }
    }

    /// Creates a new cell reference using coordinates relative to a row (usually the region's
    /// first row).
    pub fn relative(col: usize, base: usize, offset: usize) -> Self {
        log::debug!("Creating relative reference (col: {col}, base: {base}, offset: {offset})");
        Self {
            col,
            base: Some(base),
            offset,
        }
    }

    /// Returns the absolute row the cell points to.
    pub fn row(&self) -> usize {
        self.base.unwrap_or_default() + self.offset
    }

    /// Returns the offset of the cell.
    fn offset(&self) -> Offset {
        match self.base {
            Some(_) => Offset::Rel(self.offset),
            None => Offset::Abs(self.offset),
        }
    }

    /// Returns the column number.
    pub fn col(&self) -> usize {
        self.col
    }

    /// Returns true if is an absolute reference.
    pub fn is_absolute(&self) -> bool {
        self.base.is_none()
    }

    /// Tries to convert an absolute reference into a relative reference w.r.t. the given base.
    ///
    /// For a non-panicking version see [`try_relativize`](CellRef::try_relativize).
    ///
    /// # Panics
    ///
    /// If the base is larger than the row number or if the reference is already relative.
    pub fn relativize(&self, base: usize) -> Self {
        self.try_relativize(base)
            .map_err(|e| panic!("{e}"))
            .unwrap()
    }

    /// Tries to convert an absolute reference into a relative reference w.r.t. the given base.
    ///
    /// Fails if the base is larger than the row number or if the reference is already relative.
    pub fn try_relativize(&self, base: usize) -> Result<Self, CellError> {
        match self.offset() {
            Offset::Abs(offset) => {
                if base > offset {
                    return Err(CellError::BaseAfterOffset { base, offset });
                }
                let offset = offset - base;
                Ok(Self::relative(self.col, base, offset))
            }
            Offset::Rel(_) => Err(CellError::AttemptedRelativizeRelativeCell),
        }
    }

    /// Converts the cell reference to an absolute reference.
    ///
    /// If the reference is already absolute it does nothing.
    pub fn absolutize(&self) -> Self {
        Self::absolute(self.col, self.row())
    }
}

impl fmt::Debug for CellRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.base {
            Some(base) => write!(f, "[{}, {base}(+{})]", self.col, self.offset),
            None => write!(f, "[{}, {}]", self.col, self.offset),
        }
    }
}

impl fmt::Display for CellRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.base {
            Some(base) => write!(f, "[{},{base}(+{})]", self.col, self.offset),
            None => write!(f, "[{},{}]", self.col, self.offset),
        }
    }
}

impl PartialEq for CellRef {
    fn eq(&self, other: &Self) -> bool {
        self.col() == other.col() && self.row() == other.row()
    }
}

impl std::hash::Hash for CellRef {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.col().hash(state);
        self.row().hash(state);
    }
}

impl EqvRelation<CellRef> for SymbolicEqv {
    /// Two cell refs are equivalent if they point to the same absolute cell or the point to the
    /// same relative cell regardless of their base.
    fn equivalent(lhs: &CellRef, rhs: &CellRef) -> bool {
        lhs.col() == rhs.col()
            && (
                // Either they point to the same cell
                lhs.row() == rhs.row() ||
                // Or they relatively point to the same cell
                lhs.offset() == rhs.offset()
            )
    }
}

/// Errors related to cells.
#[derive(Error, Copy, Clone, Debug)]
pub enum CellError {
    /// Happens if during [`CellRef::relativize`](crate::slot::cell::CellRef::relativize) the base
    /// was larger than the reference's offset.
    #[error("failed to relativize cell reference: offset {offset} points to a row before {base}")]
    BaseAfterOffset {
        /// Base the relativization as attempted on.
        base: usize,
        /// The cell's offset.
        offset: usize,
    },
    /// Happens when attempting to [`CellRef::relativize`](crate::slot::cell::CellRef::relativize) a
    /// relative reference.
    #[error("cannot relativize a relative cell")]
    AttemptedRelativizeRelativeCell,
}

#[cfg(test)]
mod tests {
    use std::hash::{DefaultHasher, Hash as _, Hasher as _};

    use log::LevelFilter;
    use quickcheck_macros::quickcheck;
    use simplelog::{Config, TestLogger};

    use super::*;

    macro_rules! checked {
        ($name:ident, $e:expr) => {
            let Some($name) = $e else {
                return true;
            };
        };
        ($e:expr) => {
            if let None = $e {
                return true;
            }
        };
    }

    /// Tests that a relative reference and an absolute cell that point to the same cell must be
    /// equal and any that do not are not equal.
    #[quickcheck]
    fn same_absolute_and_relative_equal(col: usize, base: usize, offset: usize) -> bool {
        let _ = TestLogger::init(LevelFilter::Debug, Config::default());
        // Ignore tests where there's overflow
        checked!(base_offset, base.checked_add(offset));
        CellRef::absolute(col, base_offset) == CellRef::relative(col, base, offset)
    }

    /// Tests that a relative reference and an absolute cell that point to the same row in different
    /// columns are not equal.
    #[quickcheck]
    fn diff_col_absolute_and_relative_not_equal(col: usize, base: usize, offset: usize) -> bool {
        let _ = TestLogger::init(LevelFilter::Debug, Config::default());
        // Ignore tests where there's overflow
        checked!(base_offset, base.checked_add(offset));
        checked!(col_1, col.checked_add(1));
        CellRef::absolute(col, base_offset) != CellRef::relative(col_1, base, offset)
    }

    /// Tests that a relative reference and an absolute cell that point to the same column in
    /// different rows are not equal.
    #[quickcheck]
    fn diff_row_absolute_and_relative_not_equal_1(col: usize, base: usize, offset: usize) -> bool {
        let _ = TestLogger::init(LevelFilter::Debug, Config::default());
        // Ignore tests where there's overflow
        checked!(base_offset, base.checked_add(offset));
        checked!(base_offset.checked_add(1));
        CellRef::absolute(col, base_offset) != CellRef::relative(col, base + 1, offset)
    }

    /// Tests that a relative reference and an absolute cell that point to the same column in
    /// different rows are not equal.
    #[quickcheck]
    fn diff_row_absolute_and_relative_not_equal_2(col: usize, base: usize, offset: usize) -> bool {
        let _ = TestLogger::init(LevelFilter::Debug, Config::default());
        // Ignore tests where there's overflow
        checked!(base_offset, base.checked_add(offset));
        checked!(base_offset.checked_add(1));
        CellRef::absolute(col, base_offset) != CellRef::relative(col, base, offset + 1)
    }

    fn hash(cell: CellRef) -> u64 {
        let mut h = DefaultHasher::new();
        cell.hash(&mut h);
        h.finish()
    }

    /// Tests that a relative reference and an absolute cell that point to the same cell must be
    /// equal and any that do not are not equal.
    #[quickcheck]
    fn same_absolute_and_relative_equal_hash(col: usize, base: usize, offset: usize) -> bool {
        let _ = TestLogger::init(LevelFilter::Debug, Config::default());
        // Ignore tests where there's overflow
        checked!(base_offset, base.checked_add(offset));
        hash(CellRef::absolute(col, base_offset)) == hash(CellRef::relative(col, base, offset))
    }

    /// Tests that a relative reference and an absolute cell that point to the same row in different
    /// columns are not equal.
    #[quickcheck]
    fn diff_col_absolute_and_relative_not_equal_hash(
        col: usize,
        base: usize,
        offset: usize,
    ) -> bool {
        let _ = TestLogger::init(LevelFilter::Debug, Config::default());
        // Ignore tests where there's overflow
        checked!(base_offset, base.checked_add(offset));
        checked!(col_1, col.checked_add(1));
        hash(CellRef::absolute(col, base_offset)) != hash(CellRef::relative(col_1, base, offset))
    }

    /// Tests that a relative reference and an absolute cell that point to the same column in
    /// different rows are not equal.
    #[quickcheck]
    fn diff_row_absolute_and_relative_not_equal_1_hash(
        col: usize,
        base: usize,
        offset: usize,
    ) -> bool {
        let _ = TestLogger::init(LevelFilter::Debug, Config::default());
        // Ignore tests where there's overflow
        checked!(base_offset, base.checked_add(offset));
        checked!(base_1, base.checked_add(1));
        checked!(base_1.checked_add(offset));
        hash(CellRef::absolute(col, base_offset)) != hash(CellRef::relative(col, base_1, offset))
    }

    /// Tests that a relative reference and an absolute cell that point to the same column in
    /// different rows are not equal.
    #[quickcheck]
    fn diff_row_absolute_and_relative_not_equal_2_hash(
        col: usize,
        base: usize,
        offset: usize,
    ) -> bool {
        let _ = TestLogger::init(LevelFilter::Debug, Config::default());
        // Ignore tests where there's overflow
        checked!(base_offset, base.checked_add(offset));
        checked!(base_offset.checked_add(1));
        checked!(offset_1, offset.checked_add(1));
        hash(CellRef::absolute(col, base_offset)) != hash(CellRef::relative(col, base, offset_1))
    }

    /// Tests that two relative references with the same column and offset are symbolically
    /// equivalent.
    #[quickcheck]
    fn same_relative_sym_eqv(col: usize, base: usize, offset: usize) -> bool {
        let _ = TestLogger::init(LevelFilter::Debug, Config::default());
        // Ignore tests where there's overflow
        checked!(base_offset, base.checked_add(offset));
        checked!(base_1, base.checked_add(1));
        checked!(base_offset.checked_add(1));
        SymbolicEqv::equivalent(
            &CellRef::relative(col, base_1, offset),
            &CellRef::relative(col, base, offset),
        )
    }
}
