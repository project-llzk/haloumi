use ff::Field;
use halo2::circuit::{AssignedCell, Cell, Layouter, RegionIndex};
use halo2::plonk::{ConstraintSystem, Error, Expression};
use haloumi_integration::core::auto_conf::AutoConfigure;
use haloumi_integration::core::default_group_key;
use haloumi_integration::core::groups::RegionsGroupHooks;
use haloumi_integration::core::layouter::{LayoutAdaptor, Layouter as HLayouter};
use haloumi_ir::inject::InjectedIR;
use std::marker::PhantomData;

use crate::extraction::ExtractableFixture;
use crate::fibonacci::{FibonacciConfig, fibonacci_gates};

#[derive(Debug, Clone)]
struct FibonacciChip<F: Field> {
    config: FibonacciConfig,
    _marker: PhantomData<F>,
}

type FibNums<F> = (AssignedCell<F, F>, AssignedCell<F, F>);

impl<F: Field> FibonacciChip<F> {
    pub fn new(config: FibonacciConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn assign_inputs(&self, layouter: &mut impl Layouter<F>) -> Result<FibNums<F>, Error> {
        layouter.assign_region(
            || "assign inputs",
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

                Ok((a_cell, b_cell))
            },
        )
    }

    pub fn step(
        &self,
        layouter: &mut impl Layouter<F>,
        (fib0, fib1): &FibNums<F>,
    ) -> Result<FibNums<F>, Error> {
        layouter.group_impl(
            || "fib",
            default_group_key!(),
            |layouter, group| {
                group.annotate_inputs([fib0.cell(), fib1.cell()]);
                layouter.assign_region(
                    || "fib",
                    |mut region| {
                        self.config.selector.enable(&mut region, 0)?;
                        fib0.copy_advice(|| "fib0", &mut region, self.config.col_a, 0)?;
                        fib1.copy_advice(|| "fib1", &mut region, self.config.col_b, 0)?;

                        let fib2 = region.assign_advice(
                            || "fib2",
                            self.config.col_c,
                            0,
                            || fib0.value().copied() + fib1.value(),
                        )?;

                        group.annotate_outputs([fib1.cell(), fib2.cell()]);
                        Ok((fib1.clone(), fib2))
                    },
                )
            },
        )
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
        L: HLayouter<F, Error> + RegionsGroupHooks<F, Cell, Error = Error>,
    {
        let chip = FibonacciChip::new(config.clone());
        let [fib0, fib1] = input;
        let mut fib = (fib0, fib1);
        for _ in 0..7 {
            fib = chip.step(layouter, &fib)?;
        }
        Ok([fib.0, fib.1])
    }
}

crate::impl_extractable_fixture!(FibonacciCircuit<F>);
