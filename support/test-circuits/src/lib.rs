//! Collection of circuits used for testing the Halo2 frontend.

pub mod fibonacci;
pub mod lookup;
pub mod mul;

pub mod extraction;

macro_rules! impl_extractable_fixture {
    ($circuit:ty) => {
        impl<F: ff::PrimeField> haloumi_integration::core::circuit::AbstractCircuitIO for $circuit {
            type Chip = crate::extraction::FixtureChip<F, Self>;
            type Input = <Self as crate::extraction::ExtractableFixture<F>>::Input;
            type Output = <Self as crate::extraction::ExtractableFixture<F>>::Output;
            type Config = <Self as crate::extraction::ExtractableFixture<F>>::Config;
            type ConfigCols = ();
        }

        impl<F: ff::PrimeField> haloumi_integration::extractor::circuit::AbstractCircuit<F>
            for $circuit
        {
            type Error = halo2::plonk::Error;
            type Expression = halo2::plonk::Expression<F>;
            type Cell = halo2::circuit::Cell;
            type RegionIndex = halo2::circuit::RegionIndex;

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

        impl<F: ff::PrimeField> haloumi_integration::core::circuit::NoChipArgs for $circuit {}
    };
}

pub(crate) use impl_extractable_fixture;

macro_rules! impl_standard_mul_fixture {
    ($circuit:ty) => {
        impl<F: ff::PrimeField> crate::extraction::ExtractableFixture<F> for $circuit {
            type Input = halo2::circuit::AssignedCell<F, F>;
            type Output = halo2::circuit::AssignedCell<F, F>;

            fn synthesize_extraction<L>(
                &self,
                config: &Self::Config,
                layouter: &mut haloumi_integration::core::layouter::LayoutAdaptor<L>,
                input: Self::Input,
                _: &mut haloumi_ir::inject::InjectedIR<
                    halo2::circuit::RegionIndex,
                    halo2::plonk::Expression<F>,
                >,
            ) -> Result<Self::Output, halo2::plonk::Error>
            where
                L: haloumi_integration::core::layouter::Layouter<F, halo2::plonk::Error>
                    + haloumi_integration::core::groups::RegionsGroupHooks<
                        F,
                        halo2::circuit::Cell,
                        Error = halo2::plonk::Error,
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

pub(crate) use impl_standard_mul_fixture;
