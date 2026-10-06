use super::MulChip;
use crate::extraction::ExtractableFixture;
use crate::mul::MulConfig;
use ff::Field;
use halo2::circuit::{AssignedCell, Cell, Layouter, RegionIndex};
use halo2::plonk::{ConstraintSystem, Error, Expression};
use haloumi_integration::core::{
    auto_conf::AutoConfigure, default_group_key, groups::RegionsGroupHooks, layouter::LayoutAdaptor,
};
use haloumi_ir::inject::InjectedIR;
use std::marker::PhantomData;

pub mod deep_callstack;
pub mod different_bodies;
pub mod same_body;

#[derive(Default)]
pub struct MulCircuit<F>(pub PhantomData<F>);

impl<F: Field> AutoConfigure<ConstraintSystem<F>, MulConfig> for MulCircuit<F> {
    fn configure(meta: &mut ConstraintSystem<F>) -> MulConfig {
        MulChip::configure(meta)
    }
}

impl<F: ff::PrimeField> ExtractableFixture<F> for MulCircuit<F> {
    type Input = AssignedCell<F, F>;
    type Output = AssignedCell<F, F>;
    type Config = MulConfig;

    fn synthesize_extraction<L>(
        &self,
        config: &Self::Config,
        layouter: &mut LayoutAdaptor<L>,
        input: Self::Input,
        _: &mut InjectedIR<RegionIndex, Expression<F>>,
    ) -> Result<Self::Output, Error>
    where
        L: haloumi_integration::core::layouter::Layouter<F, Error>
            + RegionsGroupHooks<F, Cell, Error = Error>,
    {
        let chip = MulChip::construct(config.clone());
        layouter.group_impl(
            || "test group",
            default_group_key!(),
            |layouter, group| {
                group.annotate_input(input.cell());
                let prev_c = chip.assign_first_row(layouter.namespace(|| "first row"), &input)?;
                group.annotate_output(prev_c.cell());
                Ok(prev_c)
            },
        )
    }
}

crate::impl_extractable_fixture!(MulCircuit<F>);
