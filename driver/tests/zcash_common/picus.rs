#[cfg(feature = "picus-backend")]
mod inner {
    use crate::zcash_common::{clean_string, common_lowering};
    use ff::PrimeField;
    use haloumi::{ir::r#gen::IRGenParams, ir::r#gen::circuit::resolved::ResolvedIRCircuit};
    use haloumi_picus::{PicusParams, PicusParamsBuilder};
    use zcash_halo2_proofs::dev::haloumi::{Haloumi, SynthesizableCircuit};
    use zcash_halo2_proofs::plonk::Expression;

    pub fn picus_params() -> PicusParams {
        PicusParamsBuilder::new()
            .short_names()
            .no_optimize()
            .build()
    }

    pub fn opt_picus_params() -> PicusParams {
        PicusParamsBuilder::new().short_names().build()
    }

    pub fn picus_test<F, C>(
        circuit: C,
        params: PicusParams,
        ir_params: IRGenParams<F, Expression<F>>,
        expected: impl AsRef<str>,
        canonicalize: bool,
    ) where
        F: PrimeField + std::cmp::Ord,
        C: SynthesizableCircuit<F>,
    {
        let mut driver = Haloumi::default();
        let resolved = common_lowering(circuit, &mut driver, ir_params, canonicalize);
        check_picus(&driver, &resolved, params, expected);
    }

    pub fn check_picus(
        driver: &Haloumi,
        circuit: &ResolvedIRCircuit,
        params: PicusParams,
        expected: impl AsRef<str>,
    ) {
        let output = clean_string(
            &driver
                .generate_picus(circuit, params)
                .unwrap()
                .display()
                .to_string(),
        );
        let expected = clean_string(expected.as_ref());
        similar_asserts::assert_eq!(expected, output);
    }
}

#[cfg(feature = "picus-backend")]
pub use inner::*;

#[allow(unused_macros)]
macro_rules! basic_picus_test {
    ($name:ident, $circuit:expr, $expected:expr, $expected_opt:expr, $ir_params:expr $(,)?) => {
        paste::paste! {
        #[cfg(feature = "picus-backend")]
        mod [< $name _picus >] {
            use super::*;
            #[test]
            fn no_opt() {
                zcash_common::setup();
                zcash_common::picus::picus_test(
                    $circuit,
                    zcash_common::picus::picus_params(),
                    $ir_params,
                    $expected,
                    false,
                );
            }

            #[test]
            fn opt() {
                zcash_common::setup();
                zcash_common::picus::picus_test(
                    $circuit,
                    zcash_common::picus::opt_picus_params(),
                    $ir_params,
                    $expected_opt,
                    true,
                );
            }
        }
        }
    };
    ($name:ident, $circuit:expr, $expected:expr, $expected_opt:expr $(,)?) => {
        $crate::zcash_common::picus::basic_picus_test! {
            $name,
            $circuit,
            $expected,
            $expected_opt,
            haloumi::ir::r#gen::IRGenParams::new()
        }
    };
}

pub(crate) use basic_picus_test;
