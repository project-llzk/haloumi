use haloumi_driver::driver::Driver;
use haloumi_ir_gen::circuit::resolved::ResolvedIRCircuit;
use haloumi_picus::{PicusParams, PicusParamsBuilder};

use crate::common::clean_string;

pub fn picus_params() -> PicusParams {
    PicusParamsBuilder::new()
        .short_names()
        .no_optimize()
        .build()
}

pub fn opt_picus_params() -> PicusParams {
    PicusParamsBuilder::new().short_names().build()
}

pub fn check_picus(circuit: &ResolvedIRCircuit, params: PicusParams, expected: &str) {
    let output = clean_string(
        &Driver::default()
            .picus(circuit, params)
            .unwrap()
            .display()
            .to_string(),
    );
    similar_asserts::assert_eq!(clean_string(expected), output);
}

macro_rules! basic_picus_test {
    ($name:ident, $circuit:expr, $expected:expr, $expected_opt:expr, $lookups:expr $(,)?) => {
        paste::paste! {
            #[cfg(feature = "picus-backend")]
            mod [<mdnt_ $name _picus>] {
                use super::*;
                #[test]
                fn no_opt() {
                    common::setup();
                    let resolved = common::extract!($circuit, $lookups, false);
                    common::picus::check_picus(&resolved, common::picus::picus_params(), $expected);
                }
                #[test]
                fn opt() {
                    common::setup();
                    let resolved = common::extract!($circuit, $lookups, true);
                    common::picus::check_picus(&resolved, common::picus::opt_picus_params(), $expected_opt);
                }
            }
        }
    };
}
pub(crate) use basic_picus_test;
