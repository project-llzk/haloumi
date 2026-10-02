use super::MulChip;
use crate::mul::MulConfig;
use ff::Field;
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    circuit::groups::default_group_key,
    plonk::{Circuit, ConstraintSystem, Error},
};
use std::marker::PhantomData;

pub mod deep_callstack;
pub mod different_bodies;
pub mod same_body;

#[derive(Default)]
pub struct MulCircuit<F>(pub PhantomData<F>);

impl<F: Field> Circuit<F> for MulCircuit<F> {
    type Config = MulConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        MulChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = MulChip::construct(config);
        let prev_c = layouter.group(
            || "test group",
            default_group_key!(),
            |layouter, group| {
                let prev_c = chip.assign_first_row(layouter.namespace(|| "first row"))?;
                group.annotate_output(prev_c.cell());
                Ok(prev_c)
            },
        )?;
        chip.expose_public(layouter.namespace(|| "out"), &prev_c, 1)?;

        Ok(())
    }
}

#[cfg(feature = "extraction")]
impl<F: ff::PrimeField> crate::extraction::ExtractableFixture<F> for MulCircuit<F> {
    type Input = midnight_proofs::circuit::AssignedCell<F, F>;
    type Output = midnight_proofs::circuit::AssignedCell<F, F>;

    fn synthesize_extraction<L>(
        &self,
        config: &Self::Config,
        layouter: &mut haloumi_integration::core::layouter::LayoutAdaptor<L>,
        input: Self::Input,
        _: &mut haloumi_ir::inject::InjectedIR<midnight_proofs::circuit::RegionIndex, midnight_proofs::plonk::Expression<F>>,
    ) -> Result<Self::Output, Error>
    where
        L: haloumi_integration::core::layouter::Layouter<F, Error>
            + haloumi_integration::core::groups::RegionsGroupHooks<F, midnight_proofs::circuit::Cell, Error = Error>,
    {
        let chip = MulChip::construct(config.clone());
        layouter.group(|| "test group", midnight_proofs::circuit::groups::default_group_key!(), |layouter, group| {
            group.annotate_input(input.cell());
            let output = chip.assign_first_row_from_input(layouter.namespace(|| "first row"), &input)?;
            group.annotate_output(output.cell());
            Ok(output)
        })
    }
}

#[cfg(feature = "extraction")]
crate::impl_extractable_fixture!(MulCircuit<F>);
