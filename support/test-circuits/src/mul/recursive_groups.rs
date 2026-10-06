use ff::Field;
use halo2::circuit::{AssignedCell, Cell, Layouter, RegionIndex};
use halo2::plonk::{ConstraintSystem, Error, Expression};
use halo2::poly::Rotation;
use haloumi_integration::core::{
    auto_conf::AutoConfigure, default_group_key, groups::RegionsGroupHooks,
    layouter::LayoutAdaptor, table::RotationExt,
};
use haloumi_ir::inject::InjectedIR;
use std::marker::PhantomData;

use crate::extraction::ExtractableFixture;
use crate::mul::MulConfig;

const N_INPUTS: usize = 4;

#[derive(Debug, Clone)]
struct MulChip<F: Field> {
    config: MulConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> MulChip<F> {
    pub fn construct(config: MulConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> MulConfig {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let selector = meta.selector();
        let instance = meta.instance_column();

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        meta.create_gate("mul", |meta| {
            //
            // col_fixed | col_a | col_b | col_c | selector
            //      f       a      b        c       s
            //
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());

            halo2::plonk::Constraints::with_selector(selector, vec![a * b - c])
        });

        MulConfig {
            col_fixed: meta.fixed_column(),
            col_a,
            col_b,
            col_c,
            selector,
            instance,
        }
    }

    pub fn mul_many(
        &self,
        layouter: &mut impl Layouter<F>,
        operands: &[AssignedCell<F, F>],
    ) -> Result<AssignedCell<F, F>, Error> {
        if operands.len() == 1 {
            return Ok(operands[0].clone());
        }
        layouter.group_impl(
            || "mul_many",
            default_group_key!(),
            |layouter, group| {
                group.annotate_inputs(operands.iter().map(|op| op.cell()));
                let lhs = &operands[0];
                let rhs = self.mul_many(layouter, &operands[1..])?;
                layouter.assign_region(
                    || "mul",
                    |mut region| {
                        self.config.selector.enable(&mut region, 0)?;
                        assert!(operands.len() > 1);

                        let a = region.assign_advice(
                            || "a = lhs",
                            self.config.col_a,
                            0,
                            || lhs.value().copied(),
                        )?;
                        region.constrain_equal(lhs.cell(), a.cell())?;
                        let b = region.assign_advice(
                            || "b = rhs",
                            self.config.col_b,
                            0,
                            || rhs.value().copied(),
                        )?;
                        region.constrain_equal(rhs.cell(), b.cell())?;
                        let c = region.assign_advice(
                            || "a * b",
                            self.config.col_c,
                            0,
                            || a.value().copied() * b.value(),
                        )?;
                        group.annotate_output(c.cell());
                        Ok(c)
                    },
                )
            },
        )
    }

    pub fn assign_inputs(
        &self,
        inputs: &[AssignedCell<F, F>; N_INPUTS],
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        Ok(inputs.to_vec())
    }
}

#[derive(Default)]
pub struct MulCircuit<F>(pub PhantomData<F>);

impl<F: Field> AutoConfigure<ConstraintSystem<F>, MulConfig> for MulCircuit<F> {
    fn configure(meta: &mut ConstraintSystem<F>) -> MulConfig {
        MulChip::configure(meta)
    }
}

impl<F: ff::PrimeField> ExtractableFixture<F> for MulCircuit<F> {
    type Input = [AssignedCell<F, F>; N_INPUTS];
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
        let inputs = chip.assign_inputs(&input)?;
        chip.mul_many(layouter, &inputs)
    }
}

crate::impl_extractable_fixture!(MulCircuit<F>);
