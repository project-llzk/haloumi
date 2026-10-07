use ff::Field;
use halo2::circuit::{AssignedCell, Cell, Layouter, RegionIndex, Value};
use halo2::plonk::{
    Advice, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector,
};
use halo2::poly::Rotation;
use haloumi_integration::core::{
    auto_conf::AutoConfigure, groups::RegionsGroupHooks, info_traits::ConstraintSystemInfo,
    layouter::LayoutAdaptor, table::RotationExt,
};
use haloumi_ir::inject::InjectedIR;
use std::marker::PhantomData;

use crate::extraction::ExtractableFixture;

#[derive(Debug, Clone)]
pub struct MulWithFixedConstraintConfig {
    pub col_fixed: Column<Fixed>,
    pub col_a: Column<Advice>,
    pub col_b: Column<Advice>,
    pub col_c: Column<Advice>,
    pub col_d: Column<Advice>,
    pub selector: Selector,
    pub instance: Column<Instance>,
}

#[derive(Debug, Clone)]
struct MulChip<F: Field> {
    config: MulWithFixedConstraintConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> MulChip<F> {
    pub fn construct(config: MulWithFixedConstraintConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> MulWithFixedConstraintConfig {
        let col_fixed = meta.fixed_column();
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let col_d = meta.advice_column();
        let selector = meta.selector();
        let instance = meta.instance_column();

        meta.enable_constant(col_fixed);
        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(col_d);
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

        meta.create_gate("equal -1", |meta| {
            let f = meta.query_fixed(col_fixed, Rotation::cur());
            let f2 = meta.query_fixed(col_fixed, Rotation::next());

            halo2::plonk::Constraints::with_selector(
                selector,
                vec![(f - f2) + Expression::Constant(F::ONE + F::ONE + F::ONE)],
            )
        });

        MulWithFixedConstraintConfig {
            col_fixed,
            col_a,
            col_b,
            col_c,
            col_d,
            selector,
            instance,
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
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

                let a_cell = input.copy_advice(|| "a", &mut region, self.config.col_a, 0)?;

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

                region.assign_advice_from_constant(
                    || "const",
                    self.config.col_d,
                    0,
                    F::ONE + F::ONE,
                )?;

                Ok(c_cell)
            },
        )
    }
}

#[derive(Default)]
pub struct MulWithFixedConstraintCircuit<F>(pub PhantomData<F>);

impl<F: Field> AutoConfigure<ConstraintSystem<F>, MulWithFixedConstraintConfig>
    for MulWithFixedConstraintCircuit<F>
{
    fn configure(meta: &mut ConstraintSystem<F>) -> MulWithFixedConstraintConfig {
        MulChip::configure(meta)
    }
}

impl<F: ff::PrimeField> ExtractableFixture<F> for MulWithFixedConstraintCircuit<F> {
    type Input = AssignedCell<F, F>;
    type Output = AssignedCell<F, F>;
    type Config = MulWithFixedConstraintConfig;

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
        MulChip::construct(config.clone())
            .assign_first_row(layouter.namespace(|| "first row"), &input)
    }
}

crate::impl_extractable_fixture!(MulWithFixedConstraintCircuit<F>);
