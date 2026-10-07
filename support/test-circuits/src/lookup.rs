use ff::Field;
use halo2::circuit::{AssignedCell, Cell, Layouter, RegionIndex, Value};
use halo2::plonk::{
    Advice, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector, TableColumn,
};
use halo2::poly::Rotation;
use haloumi_integration::core::auto_conf::AutoConfigure;
use haloumi_integration::core::groups::RegionsGroupHooks;
use haloumi_integration::core::info_traits::ConstraintSystemInfo;
use haloumi_integration::core::layouter::LayoutAdaptor;
use haloumi_integration::core::table::RotationExt;
use haloumi_ir::inject::InjectedIR;
use std::marker::PhantomData;

use crate::extraction::ExtractableFixture;

pub mod two_by_three;
pub mod two_by_three_fixed;
pub mod two_by_three_zerosel;

#[derive(Debug, Clone)]
pub struct LookupConfig {
    #[allow(dead_code)]
    pub col_fixed: Column<Fixed>,
    pub lookup_column: TableColumn,
    pub col_f: Column<Advice>,
    pub col_a: Column<Advice>,
    pub col_b: Column<Advice>,
    pub col_c: Column<Advice>,
    pub selector: Selector,
    pub instance: Column<Instance>,
}

#[derive(Debug, Clone)]
struct LookupChip<F: Field> {
    config: LookupConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> LookupChip<F> {
    pub fn construct(config: LookupConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> LookupConfig {
        let col_fixed = meta.fixed_column();
        let col_a = meta.advice_column();
        let col_f = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let selector = meta.complex_selector();
        let instance = meta.instance_column();

        meta.enable_constant(col_fixed);
        meta.enable_equality(col_a);
        meta.enable_equality(col_f);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        let lookup_column = meta.lookup_table_column();
        meta.lookup("lookup test", |meta| {
            let s = meta.query_selector(selector);
            let f = meta.query_advice(col_f, Rotation::cur());

            vec![(s * f, lookup_column)]
        });

        // computes c = -a^2
        meta.create_gate("mul", |meta| {
            //
            // col_f | col_a | col_b | col_c | selector
            //   f       a      b        c       s
            //
            let f = meta.query_advice(col_f, Rotation::cur());
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());

            halo2::plonk::Constraints::with_selector(
                selector,
                vec![f * a.clone() - b.clone(), a * b - c],
            )
        });

        LookupConfig {
            col_fixed,
            lookup_column,
            col_a,
            col_f,
            col_b,
            col_c,
            selector,
            instance,
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn assign_table(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "table",
            |mut table| {
                table.assign_cell(
                    || "lookup col",
                    self.config.lookup_column,
                    0,
                    || -> Value<F> { Value::known(-F::ONE) },
                )
            },
        )
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

                let fixed_cell = region.assign_advice(
                    || "-1",
                    self.config.col_f,
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

                Ok(c_cell)
            },
        )
    }
}

#[derive(Default)]
pub struct LookupCircuit<F>(pub PhantomData<F>);

impl<F: Field> AutoConfigure<ConstraintSystem<F>, LookupConfig> for LookupCircuit<F> {
    fn configure(meta: &mut ConstraintSystem<F>) -> LookupConfig {
        LookupChip::configure(meta)
    }
}

impl<F: ff::PrimeField> ExtractableFixture<F> for LookupCircuit<F> {
    type Input = AssignedCell<F, F>;
    type Output = AssignedCell<F, F>;
    type Config = LookupConfig;

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
        LookupChip::construct(config.clone())
            .assign_first_row(layouter.namespace(|| "first row"), &input)
    }

    fn load_extraction(
        config: &Self::Config,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        LookupChip::construct(config.clone()).assign_table(layouter.namespace(|| "table"))
    }
}

crate::impl_extractable_fixture!(LookupCircuit<F>);
