use ff::Field;
use halo2::circuit::{AssignedCell, Cell, Layouter, RegionIndex, Value};
use halo2::plonk::{ConstraintSystem, Error, Expression};
use halo2::poly::Rotation;
use haloumi_integration::core::{
    auto_conf::AutoConfigure, default_group_key, groups::RegionsGroupHooks,
    info_traits::ConstraintSystemInfo, layouter::LayoutAdaptor, table::RotationExt,
};
use haloumi_ir::inject::InjectedIR;
use std::marker::PhantomData;

use crate::extraction::ExtractableFixture;
use crate::mul::MulConfig;

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
        let col_fixed = meta.fixed_column();
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let selector = meta.selector();
        let instance = meta.instance_column();

        meta.enable_constant(col_fixed);
        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        // computes c = -a^2
        meta.create_gate("mul", |meta| {
            //
            // col_fixed | col_a | col_b | col_c | selector
            //      f       a      b        c       s
            //
            let f = meta.query_fixed(col_fixed, Rotation::cur());
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());

            halo2::plonk::Constraints::with_selector(
                selector,
                vec![f * a.clone() - b.clone(), a * b - c],
            )
        });

        MulConfig {
            col_fixed,
            col_a,
            col_b,
            col_c,
            selector,
            instance,
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn assign_first_row(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let fixed_cell = region.assign_fixed(
                    || "-1",
                    self.config.col_fixed,
                    0,
                    || -> Value<F> { Value::known(-F::ONE) },
                )?;

                let a_cell = region.assign_advice(
                    || "a",
                    self.config.col_a,
                    0,
                    || input.value().copied(),
                )?;
                region.constrain_equal(input.cell(), a_cell.cell())?;

                let b_cell = region.assign_advice(
                    || "-1 * a",
                    self.config.col_b,
                    0,
                    || a_cell.value().copied() * fixed_cell.value(),
                )?;

                let c_cell = region.assign_advice(
                    || "a * b",
                    self.config.col_c,
                    0,
                    || a_cell.value().copied() * b_cell.value(),
                )?;

                Ok(c_cell)
            },
        )
    }

    pub fn call_group(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.group_impl(
            || "test group",
            // Defined here to get always the same key.
            default_group_key!(),
            |layouter, group| {
                group.annotate_input(input.cell());
                let prev_c = self.assign_first_row(layouter, input)?;
                group.annotate_output(prev_c.cell());
                Ok(prev_c)
            },
        )
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
        let c = chip.call_group(layouter, &input)?;
        chip.call_group(layouter, &c)
    }
}

crate::impl_extractable_fixture!(MulCircuit<F>);
