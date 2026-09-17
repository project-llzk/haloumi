use super::MulChip;
use crate::mul::MulConfig;
use ff::Field;
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{Circuit, ConstraintSystem, Error},
};
use std::marker::PhantomData;

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

        let prev_c = chip.assign_first_row(layouter.namespace(|| "first row"))?;

        chip.expose_public(layouter.namespace(|| "out"), &prev_c, 11)?;
        Ok(())
    }
}

#[cfg(feature = "extraction")]
impl<F: ff::PrimeField> crate::extraction::ExtractableFixture<F> for MulCircuit<F> {
    type Input = [midnight_proofs::circuit::AssignedCell<F, F>; 11];
    type Output = [midnight_proofs::circuit::AssignedCell<F, F>; 11];

    fn synthesize_extraction<L>(
        &self,
        config: &Self::Config,
        layouter: &mut haloumi_integration::core::layouter::LayoutAdaptor<L>,
        input: Self::Input,
        _: &mut haloumi_ir::inject::InjectedIR<
            midnight_proofs::circuit::RegionIndex,
            midnight_proofs::plonk::Expression<F>,
        >,
    ) -> Result<Self::Output, Error>
    where
        L: haloumi_integration::core::layouter::Layouter<F, Error>
            + haloumi_integration::core::groups::RegionsGroupHooks<
                F,
                midnight_proofs::circuit::Cell,
                Error = Error,
            >,
    {
        use std::mem::MaybeUninit;

        let mut out: [MaybeUninit<midnight_proofs::circuit::AssignedCell<F, F>>; 11] =
            [const { MaybeUninit::uninit() }; 11];
        for (n, e) in (&mut out[..]).iter_mut().enumerate() {
            e.write(
                MulChip::construct(config.clone())
                    .assign_first_row_from_input(layouter.namespace(|| "first row"), &input[n])?,
            );
        }
        Ok(out.map(|e| unsafe { e.assume_init() }))
    }
}

#[cfg(feature = "extraction")]
crate::impl_extractable_fixture!(MulCircuit<F>);
