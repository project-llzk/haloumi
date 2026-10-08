use super::MulChip;
use crate::extraction::ExtractableFixture;
use crate::mul::MulConfig;
use ff::{Field, PrimeField};
use halo2::circuit::{AssignedCell, Cell, Layouter, RegionIndex};
use halo2::plonk::{ConstraintSystem, Error, Expression};
use haloumi_integration::core::{
    auto_conf::AutoConfigure, groups::RegionsGroupHooks, layouter::LayoutAdaptor,
};
use haloumi_ir::inject::InjectedIR;
use std::marker::PhantomData;

const N_IO: usize = 11;

#[derive(Default)]
pub struct MulCircuit<F>(pub PhantomData<F>);

impl<F: Field> AutoConfigure<ConstraintSystem<F>, MulConfig> for MulCircuit<F> {
    fn configure(meta: &mut ConstraintSystem<F>) -> MulConfig {
        MulChip::configure(meta)
    }
}

impl<F: PrimeField> ExtractableFixture<F> for MulCircuit<F> {
    type Input = [AssignedCell<F, F>; N_IO];
    type Output = [AssignedCell<F, F>; N_IO];
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
        let outputs = input
            .iter()
            .map(|input| chip.assign_first_row(layouter.namespace(|| "first row"), input))
            .collect::<Result<Vec<_>, _>>()?;
        match outputs.try_into() {
            Ok(outputs) => Ok(outputs),
            Err(_) => unreachable!("input count is fixed"),
        }
    }
}

crate::impl_extractable_fixture!(MulCircuit<F>);
