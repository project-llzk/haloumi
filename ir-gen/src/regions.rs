use std::{collections::HashMap, num::TryFromIntError};

use ff::Field;
use haloumi_core::table::RegionIndex;
use haloumi_synthesis::{SynthesizedCircuit, regions::RegionData};

use crate::resolvers::ResolutionError;

pub mod region_row;
pub mod row;

#[derive(Debug, thiserror::Error)]
enum RegionResolutionError {
    #[error("region does not have a size")]
    SizelessRegion,

    #[error(
        "failed to resolve {type_name} cell ({col}, {rot}): fallback value was required but was not present"
    )]
    MissingFallbackValue {
        type_name: &'static str,
        col: usize,
        rot: usize,
    },

    #[error("row underflow")]
    RowUnderflow,

    #[error(transparent)]
    IntError(#[from] TryFromIntError),
}

impl From<RegionResolutionError> for ResolutionError {
    fn from(value: RegionResolutionError) -> Self {
        ResolutionError::new(value)
    }
}

/// Creates a map from region index to its data
#[inline]
pub fn region_data<F: Field, E>(syn: &SynthesizedCircuit<F, E>) -> RegionByIndex<'_> {
    syn.groups()
        .iter()
        .inspect(|g| log::debug!("[region_data] For group '{}'", g.name()))
        .flat_map(|g| g.regions())
        .inspect(|r| log::debug!("[region_data]  Region {r:?}"))
        .map(|r| {
            r.index()
                .map(|i| (i, r))
                .unwrap_or_else(|| panic!("Region {r:?} does not have an index"))
        })
        .collect()
}

pub type RegionByIndex<'s> = HashMap<RegionIndex, RegionData<'s>>;
