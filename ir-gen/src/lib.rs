#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use std::collections::HashMap;

use ff::PrimeField;
use haloumi_core::expressions::{EvaluableExpr, ExprBuilder, ExpressionInfo};
use haloumi_synthesis::SynthesizedCircuit;

use crate::{
    circuit::unresolved::UnresolvedIRCircuit,
    ctx::{GroupIRCtx, IRCtx},
    error::Error,
    groups::{UnresolvedIRGroup, new_group},
};

pub mod circuit;
pub mod ctx;
pub mod error;
pub mod expressions;
pub mod gates;
mod groups;
pub mod lookups;
mod params;
mod patterns;
mod regions;
mod resolvers;
pub mod temps;
mod utils;

// Re-exports
pub use params::IRGenParams;

/// Entry point of the IR generation step in the lowering pipeline.
#[derive(Debug, Default)]
pub struct IRGenerationUser {
    ctxs: HashMap<usize, IRCtx>,
}

impl IRGenerationUser {
    /// Creates a new IR generator.
    pub fn new() -> Self {
        Self {
            ctxs: Default::default(),
        }
    }

    /// Generates the IR of the synthesized circuit.
    pub fn generate_ir<'syn, 'drv, 'cb, 'sco, F, E>(
        &'drv mut self,
        syn: &'syn SynthesizedCircuit<F, E>,
        params: IRGenParams<'cb, '_, F, E>,
    ) -> Result<UnresolvedIRCircuit<'drv, 'syn, 'sco, F, E>, Error>
    where
        F: PrimeField + Ord,
        E: Clone + ExprBuilder<F> + ExpressionInfo + EvaluableExpr<F> + std::fmt::Debug,
        'syn: 'sco,
        'drv: 'sco + 'syn,
        'cb: 'sco + 'syn,
    {
        let ctx = self.get_or_create_ir_ctx(syn);
        let ir = generate_ir(syn, params, ctx)?;
        let enumerated_groups = syn.groups().iter().enumerate().collect::<Vec<_>>();
        let mut regions_to_groups = vec![];

        for (idx, group) in &enumerated_groups {
            for region in group.regions() {
                regions_to_groups.push((region.index().unwrap(), *idx));
            }
        }
        regions_to_groups.sort_by_key(|(ri, _)| **ri);
        debug_assert!(
            regions_to_groups
                .iter()
                .enumerate()
                .all(|(n, (ri, _))| n == **ri)
        );
        let regions_to_groups = regions_to_groups
            .into_iter()
            .map(|(_, gidx)| gidx)
            .collect();
        Ok(UnresolvedIRCircuit::new(ctx, ir, regions_to_groups))
    }

    /// Creates the IR context for the synthesized circuit.
    fn get_or_create_ir_ctx<'drv, F, E>(
        &'drv mut self,
        syn: &SynthesizedCircuit<F, E>,
    ) -> &'drv IRCtx
    where
        F: PrimeField,
    {
        self.ctxs.entry(syn.id()).or_insert_with(|| IRCtx::new(syn))
    }
}

/// Generates an intermediate representation of the circuit from its synthesis.
fn generate_ir<'syn, 'ctx, 'cb, 'sco, F, E>(
    syn: &'syn SynthesizedCircuit<F, E>,
    params: IRGenParams<'cb, '_, F, E>,
    ir_ctx: &'ctx IRCtx,
) -> Result<Vec<UnresolvedIRGroup<'syn, 'sco, F, E>>, Error>
where
    F: PrimeField + Ord,
    E: Clone + ExprBuilder<F> + ExpressionInfo + EvaluableExpr<F> + std::fmt::Debug,
    'syn: 'sco,
    'ctx: 'sco + 'syn,
    'cb: 'sco + 'syn,
{
    log::debug!("Circuit synthesis has {} gates", syn.gates().len());
    let ctx = GroupIRCtx::new(syn, params);

    log::debug!("Generating IR of region groups");

    let groups_ir = ctx
        .groups()
        .iter()
        .enumerate()
        .map(|(id, g)| {
            new_group(
                g,
                id,
                &ctx,
                ir_ctx.advice_io_of_group(id),
                ir_ctx.instance_io_of_group(id),
            )
        })
        .collect::<Result<Vec<_>, _>>()
        .map_err(Error::new)?;

    // Sanity check, only one group should be considered main.
    assert_eq!(
        groups_ir.iter().filter(|g| g.is_main()).count(),
        1,
        "Only one main group is allowed"
    );

    Ok(groups_ir)
}
