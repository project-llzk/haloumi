//! Context associated to IR objects.

use std::collections::{HashMap, HashSet};
use std::ops::Range;

use crate::gates::callbacks::DefaultGateCallbacks;
use crate::gates::rewrite::RewritePatternSet;
use crate::lookups::callbacks::{DefaultLookupCallbacks, LookupCallbacks};
use crate::params::IRGenParams;
use crate::patterns::load_patterns;
use crate::regions::{RegionByIndex, region_data};
use ff::Field;
use haloumi_core::expressions::{EvaluableExpr, ExprBuilder, ExpressionInfo};
use haloumi_core::table::{Any, Column, RegionIndex};
use haloumi_synthesis::SynthesizedCircuit;
use haloumi_synthesis::groups::Group;
use haloumi_synthesis::groups::GroupsIO;
use haloumi_synthesis::io::{AdviceIO, InstanceIO};
use haloumi_synthesis::regions::RegionData;

#[cfg(any(test, feature = "arbitrary"))]
use quickcheck::Arbitrary;

/// Contains information related to the IR of a circuit. Is used by the driver to lower the
/// circuit.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IRCtx {
    groups_io: GroupsIO,
    advice_cells: HashMap<RegionIndex, AdviceCells>,
}

impl IRCtx {
    pub(crate) fn new<F: Field, E>(syn: &SynthesizedCircuit<F, E>) -> Self {
        Self {
            groups_io: syn.groups().groups_io(),
            advice_cells: region_data(syn)
                .into_iter()
                .map(|(k, r)| (k, AdviceCells::new(r)))
                .collect(),
        }
    }

    /// Returns the IO advice cells for the given group.
    pub fn advice_io_of_group(&self, idx: usize) -> &AdviceIO {
        self.groups_io.advice_io(idx)
    }

    /// Returns the IO instance cells for the given group.
    pub fn instance_io_of_group(&self, idx: usize) -> &InstanceIO {
        self.groups_io.instance_io(idx)
    }

    pub(crate) fn advice_cells(&self) -> &HashMap<RegionIndex, AdviceCells> {
        &self.advice_cells
    }
}

#[cfg(any(test, feature = "arbitrary"))]
impl Arbitrary for IRCtx {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let len = usize::arbitrary(g) % g.size();
        Self {
            groups_io: GroupsIO::arbitrary(g),
            advice_cells: (0..len)
                .map(|_| (RegionIndex::arbitrary(g), AdviceCells::arbitrary(g)))
                .collect(),
        }
    }
}

/// Contains information about the advice cells in a region.
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub(crate) struct AdviceCells {
    columns: HashSet<Column<Any>>,
    rows: Range<usize>,
    start: Option<usize>,
}

#[cfg(any(test, feature = "arbitrary"))]
impl Arbitrary for AdviceCells {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let row_start = usize::arbitrary(g) % 16;
        Self {
            columns: (0..(usize::arbitrary(g) % (g.size().min(4) + 1)))
                .map(|_| Column::arbitrary(g))
                .collect(),
            rows: row_start..row_start + usize::arbitrary(g) % 16,
            start: bool::arbitrary(g).then_some(usize::arbitrary(g) % 16),
        }
    }
}

impl AdviceCells {
    pub fn new(region: RegionData) -> Self {
        let cells = Self {
            columns: region
                .columns()
                .iter()
                .filter(|c| matches!(c.column_type(), Any::Advice))
                .copied()
                .collect(),
            rows: region.rows(),
            start: region.start(),
        };
        log::debug!("{region:?} Produced the following {cells:?}");
        cells
    }

    /// Returns true if the region contains the given advice cell.
    pub fn contains_advice_cell(&self, col: usize, row: usize) -> bool {
        let in_col_set = self.columns.iter().any(|c| c.index() == col);
        let in_row_range = self.rows.contains(&row);
        in_col_set && in_row_range
    }

    /// Returns the start of the region.
    pub fn start(&self) -> Option<usize> {
        self.start
    }
}

impl std::fmt::Debug for AdviceCells {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "AdviceCells")?;
        writeln!(f, "  Rows {:?} (Start: {:?})", self.rows, self.start)?;
        write!(f, "  Columns ")?;
        crate::utils::fmt_columns(&self.columns, f)?;
        writeln!(f)
    }
}

/// Support data for creating group body IR structs
pub(crate) struct GroupIRCtx<'lc, 'gc, 'syn, F: Field, E> {
    regions_by_index: RegionByIndex<'syn>,
    syn: &'syn SynthesizedCircuit<F, E>,
    patterns: RewritePatternSet<'gc, F, E>,
    params: IRGenParams<'lc, 'gc, F, E>,
}

impl<'lc, 'gc, 'syn, F: Field, E> GroupIRCtx<'lc, 'gc, 'syn, F, E> {
    pub fn new(syn: &'syn SynthesizedCircuit<F, E>, params: IRGenParams<'lc, 'gc, F, E>) -> Self
    where
        E: Clone + ExprBuilder<F> + ExpressionInfo + EvaluableExpr<F> + std::fmt::Debug,
    {
        let patterns = load_patterns(params.gate_cb.unwrap_or(&DefaultGateCallbacks));
        let regions_by_index = region_data(syn);
        Self {
            regions_by_index,
            syn,
            patterns,
            params,
        }
    }

    pub(super) fn groups(&self) -> &'syn [Group] {
        self.syn.groups()
    }

    pub(super) fn regions_by_index(&self) -> &HashMap<RegionIndex, RegionData<'syn>> {
        &self.regions_by_index
    }

    pub(super) fn syn(&self) -> &'syn SynthesizedCircuit<F, E> {
        self.syn
    }

    pub(super) fn patterns(&self) -> &RewritePatternSet<'_, F, E> {
        &self.patterns
    }

    pub(super) fn lookup_cb(&self) -> &'lc dyn LookupCallbacks<F, E>
    where
        E: Clone,
    {
        self.params.lookup_cb.unwrap_or(&DefaultLookupCallbacks)
    }

    pub(super) fn generate_debug_comments(&self) -> bool {
        self.params.debug_comments
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(feature = "serde")]
    use quickcheck_macros::quickcheck;

    #[cfg(feature = "serde")]
    fn round_trip<T: serde::Serialize + serde::de::DeserializeOwned>(value: &T) -> T {
        serde_json::from_slice(&serde_json::to_vec(&value).unwrap()).unwrap()
    }

    #[cfg(feature = "serde")]
    #[quickcheck]
    fn advice_cells_round_trip(value: AdviceCells) {
        let decoded = round_trip(&value);
        assert_eq!(value, decoded);
    }

    #[cfg(feature = "serde")]
    #[quickcheck]
    fn context_round_trip(value: IRCtx) {
        assert_eq!(value.clone(), round_trip(&value));
    }
}
