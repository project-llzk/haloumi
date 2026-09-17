use haloumi_driver::driver::Driver;
use haloumi_ir_gen::circuit::resolved::ResolvedIRCircuit;
use haloumi_llzk::LlzkParams;
use llzk::prelude::{LlzkContext, OperationLike as _};

pub fn llzk_params(ctx: &LlzkContext) -> LlzkParams<'_> {
    let mut params = LlzkParams::new(ctx);
    params.no_optimize().with_builtin_field("bn254");
    params
}

pub fn opt_llzk_params(ctx: &LlzkContext) -> LlzkParams<'_> {
    let mut params = LlzkParams::new(ctx);
    params.with_builtin_field("bn254");
    params
}

pub fn check_llzk(circuit: &ResolvedIRCircuit, params: LlzkParams, expected: &str) {
    let output = Driver::default().llzk(circuit, params).unwrap();
    assert!(output.module().as_operation().verify());
    mlir_testutils::assert_module_eq(output.module(), expected);
}

macro_rules! basic_llzk_test {
    ($name:ident, $circuit:expr, $expected:expr, $expected_opt:expr, $lookups:expr $(,)?) => {
        paste::paste! {
            #[cfg(feature = "llzk-backend")]
            mod [<mdnt_ $name _llzk>] {
                use super::*;
                #[test]
                fn no_opt() {
                    mdnt_common::setup();
                    let resolved = mdnt_common::extract!($circuit, $lookups, false);
                    let ctx = llzk::context::LlzkContext::new();
                    mdnt_common::llzk::check_llzk(&resolved, mdnt_common::llzk::llzk_params(&ctx), $expected);
                }
                #[test]
                fn opt() {
                    mdnt_common::setup();
                    let resolved = mdnt_common::extract!($circuit, $lookups, true);
                    let ctx = llzk::context::LlzkContext::new();
                    mdnt_common::llzk::check_llzk(&resolved, mdnt_common::llzk::opt_llzk_params(&ctx), $expected_opt);
                }
            }
        }
    };
}
pub(crate) use basic_llzk_test;
