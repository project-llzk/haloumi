use std::marker::PhantomData;

use ff::PrimeField;
use halo2::{
    circuit::{AssignedCell, Layouter as MidnightLayouter, RegionIndex, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
};
use haloumi_integration::{
    circuit::{ExtraibleChip, io::CellReprSize},
    core::{
        groups::RegionsGroupHooks,
        layouter::{LayoutAdaptor, Layouter},
    },
};
use haloumi_ir::inject::InjectedIR;

pub trait ExtractableFixture<F: PrimeField>: Circuit<F> {
    type Input: CellReprSize;
    type Output: CellReprSize;
    type Config;

    fn synthesize_extraction<L>(
        &self,
        config: &Self::Config,
        layouter: &mut LayoutAdaptor<L>,
        input: Self::Input,
        injected_ir: &mut InjectedIR<RegionIndex, Expression<F>>,
    ) -> Result<Self::Output, Error>
    where
        L: Layouter<F, Error> + RegionsGroupHooks<F, halo2::circuit::Cell, Error = Error>;

    fn load_extraction(
        _config: &Self::Config,
        _layouter: &mut impl MidnightLayouter<F>,
    ) -> Result<(), Error> {
        Ok(())
    }
}

pub fn assign_standard_mul<F: PrimeField>(
    layouter: &mut impl MidnightLayouter<F>,
    input: &AssignedCell<F, F>,
    col_fixed: Column<Fixed>,
    col_a: Column<Advice>,
    col_b: Column<Advice>,
    col_c: Column<Advice>,
    selector: Selector,
) -> Result<AssignedCell<F, F>, Error> {
    layouter.assign_region(
        || "first row",
        |mut region| {
            selector.enable(&mut region, 0)?;
            let fixed = region.assign_fixed(|| "-1", col_fixed, 0, || Value::known(-F::ONE))?;
            let a = input.copy_advice(|| "a", &mut region, col_a, 0)?;
            let b = region.assign_advice(
                || "-1 * a",
                col_b,
                0,
                || a.value().copied() * fixed.value(),
            )?;
            region.assign_advice(|| "a * b", col_c, 0, || a.value().copied() * b.value())
        },
    )
}

pub fn assign_advice_fixed_mul<F: PrimeField>(
    layouter: &mut impl MidnightLayouter<F>,
    input: &AssignedCell<F, F>,
    col_f: Column<Advice>,
    col_a: Column<Advice>,
    col_b: Column<Advice>,
    col_c: Column<Advice>,
    selector: Option<Selector>,
) -> Result<AssignedCell<F, F>, Error> {
    layouter.assign_region(
        || "first row",
        |mut region| {
            if let Some(selector) = selector {
                selector.enable(&mut region, 0)?;
            }
            let fixed = region.assign_advice(|| "-1", col_f, 0, || Value::known(-F::ONE))?;
            let a = input.copy_advice(|| "a", &mut region, col_a, 0)?;
            let b = region.assign_advice(
                || "-1 * a",
                col_b,
                0,
                || a.value().copied() * fixed.value(),
            )?;
            region.assign_advice(|| "a * b", col_c, 0, || a.value().copied() * b.value())
        },
    )
}

#[derive(Debug)]
pub struct FixtureChip<F: PrimeField, C: ExtractableFixture<F>> {
    config: C::Config,
    _marker: PhantomData<(F, C)>,
}

impl<F: PrimeField, C: ExtractableFixture<F>> FixtureChip<F, C> {
    pub fn config(&self) -> &C::Config {
        &self.config
    }
}

impl<F, C, L> ExtraibleChip<L> for FixtureChip<F, C>
where
    F: PrimeField,
    C: ExtractableFixture<F>,
    C::Config: Clone + std::fmt::Debug,
    L: MidnightLayouter<F>,
{
    type Config = C::Config;
    type Args = ();
    type ConfigCols = ();
    type CS = ConstraintSystem<F>;
    type Error = Error;

    fn new_chip(config: &Self::Config, _: Self::Args) -> Self {
        Self {
            config: config.clone(),
            _marker: PhantomData,
        }
    }

    fn configure_circuit(meta: &mut Self::CS, _: &Self::ConfigCols) -> Self::Config {
        C::configure(meta)
    }

    fn load_chip(&self, layouter: &mut L, _: &Self::Config) -> Result<(), Self::Error> {
        C::load_extraction(&self.config, layouter)
    }
}
