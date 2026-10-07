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
use std::{iter, marker::PhantomData};

use crate::extraction::ExtractableFixture;

#[derive(Debug, Clone)]
pub struct Lookup2x3Config {
    #[allow(dead_code)]
    pub col_fixed: Column<Fixed>,
    pub lookup_column: [TableColumn; 2],
    pub col_f: Column<Advice>,
    pub col_a: Column<Advice>,
    pub col_b: Column<Advice>,
    pub col_c: Column<Advice>,
    pub selector: Selector,
    pub instance: Column<Instance>,
}

#[derive(Debug, Clone)]
struct Lookup2x3Chip<F: Field> {
    config: Lookup2x3Config,
    _marker: PhantomData<F>,
}

impl<F: Field> Lookup2x3Chip<F> {
    pub fn construct(config: Lookup2x3Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> Lookup2x3Config {
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

        let lookup_column = [meta.lookup_table_column(), meta.lookup_table_column()];
        meta.lookup("lookup test", |meta| {
            let s = meta.query_selector(selector);
            let f = meta.query_advice(col_f, Rotation::cur());
            let a = meta.query_advice(col_a, Rotation::cur());

            vec![(s.clone() * f, lookup_column[0]), (s * a, lookup_column[1])]
        });

        Lookup2x3Config {
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

    fn f(&self, n: usize) -> Value<F> {
        Value::known(iter::repeat(F::ONE).take(n).sum())
    }

    #[allow(clippy::type_complexity)]
    pub fn assign_table(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "table",
            |mut table| {
                let fst = [10, 20, 30];
                let snd = [7, 11, 13];

                fst.into_iter()
                    .zip(snd)
                    .enumerate()
                    .flat_map(|(offset, (x, y))| [(offset, x), (offset, y)])
                    .map(|(offset, n)| (offset, self.f(n)))
                    .zip(self.config.lookup_column.iter().cycle())
                    .try_for_each(|((offset, value), table_column)| {
                        table.assign_cell(
                            || format!("lookup col {}", table_column.inner().index()),
                            *table_column,
                            offset,
                            || -> Value<F> { value },
                        )
                    })
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
pub struct Lookup2x3Circuit<F>(pub PhantomData<F>);

impl<F: Field> AutoConfigure<ConstraintSystem<F>, Lookup2x3Config> for Lookup2x3Circuit<F> {
    fn configure(meta: &mut ConstraintSystem<F>) -> Lookup2x3Config {
        Lookup2x3Chip::configure(meta)
    }
}

impl<F: ff::PrimeField> ExtractableFixture<F> for Lookup2x3Circuit<F> {
    type Input = AssignedCell<F, F>;
    type Output = AssignedCell<F, F>;
    type Config = Lookup2x3Config;

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
        Lookup2x3Chip::construct(config.clone())
            .assign_first_row(layouter.namespace(|| "first row"), &input)
    }

    fn load_extraction(
        config: &Self::Config,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        Lookup2x3Chip::construct(config.clone()).assign_table(layouter.namespace(|| "table"))
    }
}

crate::impl_extractable_fixture!(Lookup2x3Circuit<F>);
