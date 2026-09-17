//! Collection of circuits used for testing the Halo2 frontend.

pub mod fibonacci;
pub mod lookup;
pub mod mul;

#[cfg(feature = "extraction")]
pub mod extraction {
    use std::marker::PhantomData;

    use ff::PrimeField;
    use haloumi_integration::{
        core::{groups::RegionsGroupHooks, layouter::Layouter},
        circuit::ExtraibleChip,
    };
    use midnight_proofs::{
        circuit::{AssignedCell, Layouter as MidnightLayouter, RegionIndex, Value},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    };

    pub trait ExtractableFixture<F: PrimeField>: Circuit<F> {
        type Input: haloumi_integration::circuit::io::CellReprSize;
        type Output: haloumi_integration::circuit::io::CellReprSize;

        fn synthesize_extraction<L>(
            &self,
            config: &Self::Config,
            layouter: &mut haloumi_integration::core::layouter::LayoutAdaptor<L>,
            input: Self::Input,
            injected_ir: &mut haloumi_ir::inject::InjectedIR<RegionIndex, Expression<F>>,
        ) -> Result<Self::Output, Error>
        where
            L: Layouter<F, Error> + RegionsGroupHooks<F, midnight_proofs::circuit::Cell, Error = Error>;

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
                let fixed = region.assign_fixed(
                    || "-1",
                    col_fixed,
                    0,
                    || Value::known(-F::ONE),
                )?;
                let a = input.copy_advice(|| "a", &mut region, col_a, 0)?;
                let b = region.assign_advice(
                    || "-1 * a",
                    col_b,
                    0,
                    || a.value().copied() * fixed.value(),
                )?;
                region.assign_advice(
                    || "a * b",
                    col_c,
                    0,
                    || a.value().copied() * b.value(),
                )
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
                let fixed = region.assign_advice(
                    || "-1",
                    col_f,
                    0,
                    || Value::known(-F::ONE),
                )?;
                let a = input.copy_advice(|| "a", &mut region, col_a, 0)?;
                let b = region.assign_advice(
                    || "-1 * a",
                    col_b,
                    0,
                    || a.value().copied() * fixed.value(),
                )?;
                region.assign_advice(
                    || "a * b",
                    col_c,
                    0,
                    || a.value().copied() * b.value(),
                )
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
}

#[cfg(feature = "extraction")]
macro_rules! impl_extractable_fixture {
    ($circuit:ty) => {
        impl<F: ff::PrimeField> haloumi_integration::circuit::AbstractCircuitIO for $circuit {
            type Chip = crate::extraction::FixtureChip<F, Self>;
            type Input = <Self as crate::extraction::ExtractableFixture<F>>::Input;
            type Output = <Self as crate::extraction::ExtractableFixture<F>>::Output;
            type Config = <Self as midnight_proofs::plonk::Circuit<F>>::Config;
            type ConfigCols = ();
        }

        impl<F: ff::PrimeField> haloumi_integration::circuit::AbstractCircuit<F> for $circuit {
            type Error = midnight_proofs::plonk::Error;
            type Expression = midnight_proofs::plonk::Expression<F>;
            type Cell = midnight_proofs::circuit::Cell;
            type RegionIndex = midnight_proofs::circuit::RegionIndex;

            fn synthesize<L>(
                &self,
                chip: &Self::Chip,
                layouter: &mut haloumi_integration::core::layouter::LayoutAdaptor<L>,
                input: Self::Input,
                injected_ir: &mut haloumi_ir::inject::InjectedIR<
                    Self::RegionIndex,
                    Self::Expression,
                >,
            ) -> Result<Self::Output, Self::Error>
            where
                L: haloumi_integration::core::layouter::Layouter<F, Self::Error>
                    + haloumi_integration::core::groups::RegionsGroupHooks<
                        F,
                        Self::Cell,
                        Error = Self::Error,
                    >,
            {
                <Self as crate::extraction::ExtractableFixture<F>>::synthesize_extraction(
                    self,
                    chip.config(),
                    layouter,
                    input,
                    injected_ir,
                )
            }
        }

        impl<F: ff::PrimeField> haloumi_integration::circuit::NoChipArgs for $circuit {}
    };
}

#[cfg(feature = "extraction")]
pub(crate) use impl_extractable_fixture;

#[cfg(feature = "extraction")]
macro_rules! impl_standard_mul_fixture {
    ($circuit:ty) => {
        impl<F: ff::PrimeField> crate::extraction::ExtractableFixture<F> for $circuit {
            type Input = midnight_proofs::circuit::AssignedCell<F, F>;
            type Output = midnight_proofs::circuit::AssignedCell<F, F>;

            fn synthesize_extraction<L>(
                &self,
                config: &Self::Config,
                layouter: &mut haloumi_integration::core::layouter::LayoutAdaptor<L>,
                input: Self::Input,
                _: &mut haloumi_ir::inject::InjectedIR<
                    midnight_proofs::circuit::RegionIndex,
                    midnight_proofs::plonk::Expression<F>,
                >,
            ) -> Result<Self::Output, midnight_proofs::plonk::Error>
            where
                L: haloumi_integration::core::layouter::Layouter<
                        F,
                        midnight_proofs::plonk::Error,
                    > + haloumi_integration::core::groups::RegionsGroupHooks<
                        F,
                        midnight_proofs::circuit::Cell,
                        Error = midnight_proofs::plonk::Error,
                    >,
            {
                crate::extraction::assign_standard_mul(
                    layouter,
                    &input,
                    config.col_fixed,
                    config.col_a,
                    config.col_b,
                    config.col_c,
                    config.selector,
                )
            }
        }

        crate::impl_extractable_fixture!($circuit);
    };
}

#[cfg(feature = "extraction")]
pub(crate) use impl_standard_mul_fixture;
