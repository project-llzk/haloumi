use ff::Field;
use midnight_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    plonk::{Circuit, ConstraintSystem, Error},
    poly::Rotation,
};
use std::marker::PhantomData;

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
        let col_c = meta.advice_column();
        let selector = meta.selector();
        let instance = meta.instance_column();

        meta.enable_constant(col_fixed);
        meta.enable_equality(col_a);
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
            let b = meta.query_advice(col_a, Rotation::next());
            let c = meta.query_advice(col_c, Rotation::cur());

            midnight_proofs::plonk::Constraints::with_selector(
                selector,
                vec![f * a.clone() - b.clone(), a * b - c],
            )
        });

        MulConfig {
            col_fixed,
            col_a,
            col_b: meta.advice_column(),
            col_c,
            selector,
            instance,
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
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

                let a_cell = region.assign_advice_from_instance(
                    || "a",
                    self.config.instance,
                    0,
                    self.config.col_a,
                    0,
                )?;

                let b_cell = region.assign_advice(
                    || "-1 * a",
                    self.config.col_a,
                    1,
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

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

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
        chip.expose_public(layouter.namespace(|| "out"), &prev_c, 1)?;
        let prev_c = chip.assign_first_row(layouter.namespace(|| "first row"))?;
        chip.expose_public(layouter.namespace(|| "out"), &prev_c, 2)?;
        let prev_c = chip.assign_first_row(layouter.namespace(|| "first row"))?;
        chip.expose_public(layouter.namespace(|| "out"), &prev_c, 3)?;
        Ok(())
    }
}

#[cfg(feature = "extraction")]
impl<F: ff::PrimeField> crate::extraction::ExtractableFixture<F> for MulCircuit<F> {
    type Input = AssignedCell<F, F>;
    type Output = [AssignedCell<F, F>; 3];

    fn synthesize_extraction<L>(
        &self,
        config: &Self::Config,
        layouter: &mut haloumi_integration::core::layouter::LayoutAdaptor<L>,
        input: Self::Input,
        injected_ir: &mut haloumi_ir::inject::InjectedIR<midnight_proofs::circuit::RegionIndex, midnight_proofs::plonk::Expression<F>>,
    ) -> Result<Self::Output, Error>
    where
        L: haloumi_integration::core::layouter::Layouter<F, Error>
            + haloumi_integration::core::groups::RegionsGroupHooks<F, midnight_proofs::circuit::Cell, Error = Error>,
    {
        use haloumi_ir::{CmpOp, stmt::IRStmt};

        let mut outputs = Vec::with_capacity(3);
        for _ in 0..3 {
            let output = layouter.assign_region(|| "first row", |mut region| {
                config.selector.enable(&mut region, 0)?;
                let fixed = region.assign_fixed(|| "-1", config.col_fixed, 0, || Value::known(-F::ONE))?;
                let a = input.copy_advice(|| "a", &mut region, config.col_a, 0)?;
                let b = region.assign_advice(|| "-1 * a", config.col_a, 1, || a.value().copied() * fixed.value())?;
                region.assign_advice(|| "a * b", config.col_c, 0, || a.value().copied() * b.value())
            })?;
            let region = output.cell().region_index;
            let thousand = midnight_proofs::plonk::Expression::Constant(F::from(1000));
            injected_ir.entry(region).or_default().extend([
                IRStmt::constraint(CmpOp::Lt, config.col_a.cur(), thousand.clone()).map(&mut |e| (0, e)),
                IRStmt::constraint(CmpOp::Ge, config.col_a.cur(), thousand).map(&mut |e| (1, e)),
            ]);
            outputs.push(output);
        }
        Ok(outputs.try_into().unwrap())
    }
}

#[cfg(feature = "extraction")]
crate::impl_extractable_fixture!(MulCircuit<F>);
