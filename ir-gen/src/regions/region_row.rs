use super::row::Row;
use crate::regions::RegionResolutionError;
use crate::resolvers::{
    ChallengeResolver, FixedQueryResolver, QueryResolver, ResolutionError, ResolvedQuery,
    ResolvedSelector, SelectorResolver,
};
use ff::Field;
use haloumi_core::slot::Slot as FuncIO;
use haloumi_core::{
    info_traits::{ChallengeInfo, QueryInfo, SelectorInfo},
    query::{Advice, Fixed, Instance},
};
use haloumi_synthesis::io::{AdviceIO, InstanceIO};
use haloumi_synthesis::regions::RegionData;
use haloumi_synthesis::selector::SelectorSet;
use std::borrow::Cow;

#[derive(Copy, Clone, Debug)]
pub struct RegionRow<'r, 'io, 'fq, F: Field> {
    region: RegionData<'r>,
    row: Row<'io, 'fq, F>,
}

impl<'r, 'io, 'fq, F: Field> RegionRow<'r, 'io, 'fq, F> {
    pub fn new(
        region: RegionData<'r>,
        row: usize,
        advice_io: &'io AdviceIO,
        instance_io: &'io InstanceIO,
        fqr: &'fq dyn FixedQueryResolver<F>,
    ) -> Self {
        Self {
            region,
            row: Row::new(row, advice_io, instance_io, fqr),
        }
    }

    /// Changes the priority to inputs.
    pub fn prioritize_inputs(self) -> Self {
        Self {
            region: self.region,
            row: self.row.prioritize_inputs(),
        }
    }

    /// Changes the priority to outputs.
    pub fn prioritize_outputs(self) -> Self {
        Self {
            region: self.region,
            row: self.row.prioritize_outputs(),
        }
    }

    fn enabled(&self) -> Cow<'_, SelectorSet> {
        self.region.selectors_enabled_for_row(self.row.row)
    }

    pub fn row_number(&self) -> usize {
        self.row.row
    }

    #[inline]
    pub fn gate_is_disabled(&self, selectors: &SelectorSet) -> bool {
        self.enabled().is_disjoint(selectors)
    }

    #[inline]
    pub fn header(&self) -> String {
        self.region.header()
    }
}

impl<F: Field> QueryResolver<F> for RegionRow<'_, '_, '_, F> {
    fn resolve_fixed_query(
        &self,
        query: &dyn QueryInfo<Kind = Fixed>,
    ) -> Result<ResolvedQuery<F>, ResolutionError> {
        let row = self.row.resolve_rotation(query.rotation())?;
        self.row
            .fqr
            .resolve_query(query, row)
            .map(ResolvedQuery::Lit)
    }

    fn resolve_advice_query(
        &self,
        query: &dyn QueryInfo<Kind = Advice>,
    ) -> Result<ResolvedQuery<F>, ResolutionError> {
        log::debug!(
            "Resolving query: Adv[{}]@{}",
            query.column_index(),
            query.rotation()
        );
        let base = self
            .region
            .start()
            .ok_or_else(|| RegionResolutionError::SizelessRegion)?;
        Ok(ResolvedQuery::IO(self.row.resolve_advice_query_impl(
            query,
            |col, row| match self.region.relativize(row) {
                Some(row) => FuncIO::advice_rel(col, base, row),
                None => FuncIO::advice_abs(col, row),
            },
        )?))
    }

    fn resolve_instance_query(
        &self,
        query: &dyn QueryInfo<Kind = Instance>,
    ) -> Result<ResolvedQuery<F>, ResolutionError> {
        self.row.resolve_instance_query(query)
    }
}

impl<F: Field> SelectorResolver for RegionRow<'_, '_, '_, F> {
    fn resolve_selector(
        &self,
        selector: &dyn SelectorInfo,
    ) -> Result<ResolvedSelector, ResolutionError> {
        let selected = self
            .region
            .enabled_selectors()
            .get(&self.row_number())
            .is_some_and(|selectors| selectors.contains(selector.id()));
        Ok(ResolvedSelector::Const(selected.into()))
    }
}

impl<F: Field> ChallengeResolver for RegionRow<'_, '_, '_, F> {
    fn resolve_challenge(&self, challenge: &dyn ChallengeInfo) -> Result<FuncIO, ResolutionError> {
        self.row.resolve_challenge(challenge)
    }
}
