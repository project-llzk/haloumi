//! Types related to inputs, outputs, and other locations in the circuit.

use std::fmt;

use crate::{
    eqv::{EqvRelation, SymbolicEqv},
    slot::{arg::ArgNo, cell::CellRef, field::FieldId},
};

pub mod arg;
pub mod cell;
pub mod field;

/// A slot represents storage locations in a circuit.
///
/// A slot can represent IO (Arg, Field, Challenge, ...) or cells in the PLONK table
/// (Advice, Fixed, TableLookup).
#[derive(Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum Slot {
    /// Points to the n-th input argument
    Arg(ArgNo),
    /// Points to the n-th output.
    Field(FieldId),
    /// Points to an advice cell.
    Advice(CellRef),
    /// Points to a fixed cell.
    Fixed(CellRef),
    /// lookup id, column, row, idx, region_idx
    TableLookup(u64, usize, usize, usize, usize),
    /// call output: (call #, output #)
    CallOutput(usize, usize),
    /// Temporary value
    Temp(usize),
    /// Challenge argument (index, phase, n-th arg)
    Challenge(usize, u8, ArgNo),
}

impl Slot {
    /// Creates the [`Slot::Advice`] case using absolute coordinates.
    ///
    /// See [`CellRef::absolute`] for more details.
    pub fn advice_abs(col: usize, row: usize) -> Self {
        Self::Advice(CellRef::absolute(col, row))
    }

    /// Creates the [`Slot::Advice`] case using relative coordinates.
    ///
    /// See [`CellRef::relative`] for more details.
    pub fn advice_rel(col: usize, base: usize, offset: usize) -> Self {
        Self::Advice(CellRef::relative(col, base, offset))
    }

    /// Creates the [`Slot::Fixed`] case using absolute coordinates.
    ///
    /// See [`CellRef::absolute`] for more details.
    pub fn fixed_abs(col: usize, row: usize) -> Self {
        Self::Fixed(CellRef::absolute(col, row))
    }

    /// Creates the [`Slot::Fixed`] case using relative coordinates.
    ///
    /// See [`CellRef::relative`] for more details.
    pub fn fixed_rel(col: usize, base: usize, offset: usize) -> Self {
        Self::Fixed(CellRef::relative(col, base, offset))
    }
}

impl EqvRelation<Slot> for SymbolicEqv {
    /// Two Slots are symbolically equivalent if they refer to the same data regardless of how is
    /// pointed to.
    ///
    /// Arguments and fields:  equivalent if they refer to the same offset.
    /// Advice and fixed cells: equivalent if they point to the same cell relative to their base.
    /// Table lookups: equivalent if they point to the same column and row.
    /// Call outputs: equivalent if they have the same output number.
    fn equivalent(lhs: &Slot, rhs: &Slot) -> bool {
        match (lhs, rhs) {
            (Slot::Arg(lhs), Slot::Arg(rhs)) => lhs == rhs,
            (Slot::Field(lhs), Slot::Field(rhs)) => lhs == rhs,
            (Slot::Advice(lhs), Slot::Advice(rhs)) => Self::equivalent(lhs, rhs),
            (Slot::Fixed(lhs), Slot::Fixed(rhs)) => Self::equivalent(lhs, rhs),
            (Slot::TableLookup(_, col0, row0, _, _), Slot::TableLookup(_, col1, row1, _, _)) => {
                col0 == col1 && row0 == row1
            }
            (Slot::CallOutput(_, o0), Slot::CallOutput(_, o1)) => o0 == o1,
            (Slot::Temp(lhs), Slot::Temp(rhs)) => lhs == rhs,
            (
                Slot::Challenge(lhs_index, lhs_phase, _),
                Slot::Challenge(rhs_index, rhs_phase, _),
            ) => lhs_index == rhs_index && lhs_phase == rhs_phase,
            _ => false,
        }
    }
}

impl std::fmt::Debug for Slot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Arg(arg) => write!(f, "{arg:?}"),
            Self::Field(field) => write!(f, "{field:?}"),
            Self::Advice(c) => write!(f, "adv{c:?}"),
            Self::Fixed(c) => write!(f, "fix{c:?}"),
            Self::TableLookup(id, col, row, idx, region_idx) => {
                write!(f, "lookup{id}[{col},{row}]@({idx},{region_idx})")
            }
            Self::CallOutput(call, out) => write!(f, "call{call}->{out}"),
            Self::Temp(id) => write!(f, "t{}", *id),
            Self::Challenge(index, phase, _) => write!(f, "challenge{index}@{phase}"),
        }
    }
}

impl std::fmt::Display for Slot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Arg(arg) => write!(f, "{arg}"),
            Self::Field(field) => write!(f, "{field}"),
            Self::Advice(c) => write!(f, "adv{c}"),
            Self::Fixed(c) => write!(f, "fix{c}"),
            Self::TableLookup(id, col, row, idx, region_idx) => {
                write!(f, "lookup{id}[{col},{row}]@({idx},{region_idx})")
            }
            Self::CallOutput(call, out) => write!(f, "call{call}->{out}"),
            Self::Temp(id) => write!(f, "t{}", *id),
            Self::Challenge(index, phase, _) => write!(f, "challenge{index}@{phase}"),
        }
    }
}

impl From<ArgNo> for Slot {
    fn from(value: ArgNo) -> Self {
        Self::Arg(value)
    }
}

impl From<FieldId> for Slot {
    fn from(value: FieldId) -> Self {
        Self::Field(value)
    }
}
