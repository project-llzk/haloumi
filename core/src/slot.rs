//! Types related to inputs, outputs, and other locations in the circuit.

use std::fmt;

#[cfg(any(test, feature = "arbitrary"))]
use quickcheck::Arbitrary;

use crate::{
    eqv::{EqvRelation, SymbolicEqv},
    slot::{arg::ArgNo, cell::CellRef, output::OutputId},
};

pub mod arg;
pub mod cell;
pub mod output;

/// A slot represents storage locations in a circuit.
///
/// A slot can represent IO (Arg, Output, Challenge, ...) or cells in the PLONK table
/// (Advice, Fixed, TableLookup).
#[derive(Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Slot {
    /// Points to the n-th input argument
    Arg(ArgNo),
    /// Points to the n-th output.
    Output(OutputId),
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

#[cfg(any(test, feature = "arbitrary"))]
impl Arbitrary for Slot {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        match u8::arbitrary(g) % 8 {
            0 => Self::Arg(ArgNo::arbitrary(g)),
            1 => Self::Output(OutputId::arbitrary(g)),
            2 => Self::Advice(CellRef::arbitrary(g)),
            3 => Self::Fixed(CellRef::arbitrary(g)),
            4 => Self::TableLookup(
                u64::arbitrary(g),
                usize::arbitrary(g),
                usize::arbitrary(g),
                usize::arbitrary(g),
                usize::arbitrary(g),
            ),
            5 => Self::CallOutput(usize::arbitrary(g), usize::arbitrary(g)),
            6 => Self::Temp(usize::arbitrary(g)),
            _ => Self::Challenge(usize::arbitrary(g), u8::arbitrary(g), ArgNo::arbitrary(g)),
        }
    }
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

    /// Creates a list of [`Slot::CallOutput`].
    pub fn call_outputs(call_no: usize, output_count: usize) -> Vec<Self> {
        log::debug!("Creating {output_count} output slots for call number {call_no}");
        (0..output_count)
            .map(|output_no| Self::CallOutput(call_no, output_no))
            .collect()
    }

    /// Creates a list of [`Slot::Arg`].
    pub fn args(count: usize) -> Vec<Self> {
        (0..count).map(|n| Self::Arg(n.into())).collect()
    }

    /// Creates a list of [`Slot::Output`].
    pub fn outputs(count: usize) -> Vec<Self> {
        (0..count).map(|n| Self::Output(n.into())).collect()
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
            (Slot::Output(lhs), Slot::Output(rhs)) => lhs == rhs,
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
            Self::Output(field) => write!(f, "{field:?}"),
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
            Self::Output(field) => write!(f, "{field}"),
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

impl From<OutputId> for Slot {
    fn from(value: OutputId) -> Self {
        Self::Output(value)
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "serde")]
    use quickcheck_macros::quickcheck;

    use super::*;

    #[derive(Debug, PartialEq, Eq)]
    enum SlotParts {
        Arg(usize),
        Output(usize),
        Advice(usize, Option<usize>, usize),
        Fixed(usize, Option<usize>, usize),
        TableLookup(u64, usize, usize, usize, usize),
        CallOutput(usize, usize),
        Temp(usize),
        Challenge(usize, u8, usize),
    }

    impl SlotParts {
        fn new(value: &Slot) -> Self {
            match value {
                Slot::Arg(arg) => SlotParts::Arg(**arg),
                Slot::Output(output) => SlotParts::Output(**output),
                Slot::Advice(cell) => {
                    let (col, base, offset) = cell.as_parts();
                    SlotParts::Advice(*col, base.copied(), *offset)
                }
                Slot::Fixed(cell) => {
                    let (col, base, offset) = cell.as_parts();
                    SlotParts::Fixed(*col, base.copied(), *offset)
                }
                Slot::TableLookup(id, column, row, index, region) => {
                    SlotParts::TableLookup(*id, *column, *row, *index, *region)
                }
                Slot::CallOutput(call, output) => SlotParts::CallOutput(*call, *output),
                Slot::Temp(id) => SlotParts::Temp(*id),
                Slot::Challenge(index, phase, arg) => SlotParts::Challenge(*index, *phase, **arg),
            }
        }
    }

    #[cfg(feature = "serde")]
    #[quickcheck]
    fn slot_round_trips(value: Slot) {
        let decoded = crate::serde_tests_helpers::round_trip(value);
        assert_eq!(SlotParts::new(&value), SlotParts::new(&decoded));
    }
}
