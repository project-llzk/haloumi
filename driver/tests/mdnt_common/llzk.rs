#[cfg(feature = "llzk-backend")]
mod inner {
    use ff::PrimeField;
    use haloumi::{
        core::felt::Prime, driver::Driver, ir::r#gen::IRGenParams,
        ir::r#gen::circuit::resolved::ResolvedIRCircuit, synthesis::CircuitSynthesis,
    };
    use haloumi_llzk::LlzkParams;
    use haloumi_midnight_integration::plonk::{_Expression, ConstraintSystem};
    use llzk::prelude::{LlzkContext, OperationLike as _};

    use crate::mdnt_common::common_lowering;

    #[allow(dead_code)]
    pub fn llzk_params<F: PrimeField>(ctx: &LlzkContext) -> LlzkParams<'_> {
        LlzkParams::new(ctx)
            .no_optimize()
            .with_prime_field("f", Prime::new::<F>())
    }

    #[allow(dead_code)]
    pub fn opt_llzk_params<F: PrimeField>(ctx: &LlzkContext) -> LlzkParams<'_> {
        LlzkParams::new(ctx).with_prime_field("f", Prime::new::<F>())
    }

    #[allow(dead_code)]
    pub fn check_llzk(
        driver: &Driver,
        circuit: &ResolvedIRCircuit,
        params: LlzkParams,
        expected_llzk: impl AsRef<str>,
    ) {
        let output = driver.llzk(circuit, params).unwrap();
        assert!(output.module().as_operation().verify());
        mlir_testutils::assert_module_eq(output.module(), expected_llzk.as_ref());
    }

    #[allow(dead_code)]
    pub fn llzk_test<F, C>(
        circuit: C,
        params: LlzkParams,
        ir_params: IRGenParams<F, _Expression<F>>,
        expected_llzk: impl AsRef<str>,
        canonicalize: bool,
    ) where
        F: PrimeField + std::cmp::Ord,
        C: CircuitSynthesis<F, CS = ConstraintSystem<F>>,
    {
        let mut driver = Driver::default();
        let resolved = common_lowering(circuit, &mut driver, ir_params, canonicalize);
        log::info!("Completed IR lowering!");
        log::logger().flush();
        check_llzk(&driver, &resolved, params, expected_llzk);
        log::info!("Completed transforming IR to LLZK!");
        log::logger().flush();
    }
}

#[cfg(feature = "llzk-backend")]
#[allow(unused)]
pub use inner::*;

#[allow(unused_macros)]
macro_rules! basic_llzk_test {
    ($name:ident, $circuit:expr, $expected:expr, $expected_opt:expr, $field:ty, $ir_params:expr $(,)?) => {
        paste::paste! {
        #[cfg(feature = "llzk-backend")]
        mod [<mdnt_ $name _llzk >] {
            use super::*;
            #[test]
            fn no_opt() {
                mdnt_common::setup();
                let ctx = llzk::context::LlzkContext::new();
                mdnt_common::llzk::llzk_test(
                    $circuit,
                    mdnt_common::llzk::llzk_params::<$field>(&ctx),
                    $ir_params,
                    $expected,
                    false,
                );
            }

            #[test]
            fn opt() {
                mdnt_common::setup();
                let ctx = llzk::context::LlzkContext::new();
                mdnt_common::llzk::llzk_test(
                    $circuit,
                    mdnt_common::llzk::opt_llzk_params::<$field>(&ctx),
                    $ir_params,
                    $expected_opt,
                    true,
                );
            }
        }
        }
    };
    ($name:ident, $circuit:expr, $expected:expr, $expected_opt:expr, $field:ty $(,)?) => {
        $crate::mdnt_common::llzk::basic_llzk_test! {
            $name,
            $circuit,
            $expected,
            $expected_opt,
            $field,
            haloumi::ir::r#gen::IRGenParams::new()
        }
    };
}

#[allow(unused)]
pub(crate) use basic_llzk_test;
