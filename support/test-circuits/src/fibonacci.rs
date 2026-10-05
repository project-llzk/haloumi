use ff::Field;
use halo2::circuit::{AssignedCell, Cell, Layouter, RegionIndex};
use halo2::plonk::{
    Advice, Column, ConstraintSystem, Constraints, Error, Expression, Instance, Selector,
};
use halo2::poly::Rotation;
use haloumi_integration::core::auto_conf::AutoConfigure;
use haloumi_integration::core::groups::RegionsGroupHooks;
use haloumi_integration::core::layouter::LayoutAdaptor;
use haloumi_integration::core::table::RotationExt;
use haloumi_ir::inject::InjectedIR;
use std::marker::PhantomData;

use crate::extraction::ExtractableFixture;

pub mod grouped;

#[derive(Debug, Clone)]
pub struct FibonacciConfig {
    pub col_a: Column<Advice>,
    pub col_b: Column<Advice>,
    pub col_c: Column<Advice>,
    pub selector: Selector,
    pub instance: Column<Instance>,
}

pub fn fibonacci_gates<F: Field>(meta: &mut ConstraintSystem<F>) -> FibonacciConfig {
    let col_a = meta.advice_column();
    let col_b = meta.advice_column();
    let col_c = meta.advice_column();
    let selector = meta.selector();
    let instance = meta.instance_column();

    meta.enable_equality(col_a);
    meta.enable_equality(col_b);
    meta.enable_equality(col_c);
    meta.enable_equality(instance);

    meta.create_gate("add", |meta| {
        //
        // col_a | col_b | col_c | selector
        //   a      b        c       s
        //
        let a = meta.query_advice(col_a, Rotation::cur());
        let b = meta.query_advice(col_b, Rotation::cur());
        let c = meta.query_advice(col_c, Rotation::cur());

        Constraints::with_selector(selector, vec![a + b - c])
    });

    FibonacciConfig {
        col_a,
        col_b,
        col_c,
        selector,
        instance,
    }
}

#[derive(Debug, Clone)]
struct FibonacciChip<F: Field> {
    config: FibonacciConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> FibonacciChip<F> {
    pub fn new(config: FibonacciConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let a_cell = region.assign_advice_from_instance(
                    || "f(0)",
                    self.config.instance,
                    0,
                    self.config.col_a,
                    0,
                )?;

                let b_cell = region.assign_advice_from_instance(
                    || "f(1)",
                    self.config.instance,
                    1,
                    self.config.col_b,
                    0,
                )?;

                let c_cell = region.assign_advice(
                    || "a + b",
                    self.config.col_c,
                    0,
                    || a_cell.value().copied() + b_cell.value(),
                )?;

                Ok((a_cell, b_cell, c_cell))
            },
        )
    }

    pub fn step(
        &self,
        layouter: &mut impl Layouter<F>,
        prev_b: &AssignedCell<F, F>,
        prev_c: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "next row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                // Copy the value from b & c in previous row to a & b in current row
                prev_b.copy_advice(|| "a", &mut region, self.config.col_a, 0)?;
                prev_c.copy_advice(|| "b", &mut region, self.config.col_b, 0)?;

                let c_cell = region.assign_advice(
                    || "c",
                    self.config.col_c,
                    0,
                    || prev_b.value().copied() + prev_c.value(),
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

impl<F: Field> AutoConfigure<ConstraintSystem<F>, FibonacciConfig> for FibonacciCircuit<F> {
    fn configure(meta: &mut ConstraintSystem<F>) -> FibonacciConfig {
        fibonacci_gates(meta)
    }
}

#[derive(Default)]
pub struct FibonacciCircuit<F>(pub PhantomData<F>);

impl<F: ff::PrimeField> ExtractableFixture<F> for FibonacciCircuit<F> {
    type Input = [AssignedCell<F, F>; 2];
    type Output = [AssignedCell<F, F>; 2];
    type Config = FibonacciConfig;

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
        let chip = FibonacciChip::new(config.clone());
        let [mut fib0, mut fib1] = input;
        for _ in 0..7 {
            let tmp = fib1.clone();
            fib1 = chip.step(layouter, &fib0, &fib1)?;
            fib0 = tmp;
        }
        Ok([fib0, fib1])
    }
}

crate::impl_extractable_fixture!(FibonacciCircuit<F>);
