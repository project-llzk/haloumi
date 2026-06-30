use group::ff::Field;
use halo2curves::bn256::Fr;
use haloumi::{
    ir::r#gen::IRGenParams,
    ir::r#gen::lookups::callbacks::LookupCallbacks,
    ir::r#gen::lookups::table::LookupTableGenerator,
    ir::r#gen::temps::{ExprOrTemp, Temps},
    synthesis::lookups::Lookup,
};
use haloumi_ir::stmt::IRStmt;
use haloumi_ir_gen::lookups::callbacks::LookupError;
use haloumi_mdnt_test_circuits::lookup;
use haloumi_midnight_integration::plonk::_Expression;
#[cfg(feature = "picus-backend")]
use mdnt_common::picus::basic_picus_test;
use mdnt_common::synthesis_impl;
use std::borrow::Cow;

mod mdnt_common;

basic_picus_test! {
    lookup_circuit,
    LookupCircuitSynthesis::default(),
    include_str!("expected/picus/lookup.picus"),
    include_str!("expected/picus/lookup_opt.picus"),
    IRGenParams::new()
                        .lookup_callbacks(&LookupCallbackHandler)
}

basic_picus_test! {
    lookup_2x3_circuit,
    Lookup2x3CircuitSynthesis::default(),
    include_str!("expected/picus/lookup_2x3.picus"),
    include_str!("expected/picus/lookup_2x3_opt.picus"),
    IRGenParams::new()
                        .lookup_callbacks(&LookupCallbackHandler)
}

basic_picus_test! {
    lookup_2x3_fixed_circuit,
    Lookup2x3FixedCircuitSynthesis::default(),
    include_str!("expected/picus/lookup_2x3.picus"),
    include_str!("expected/picus/lookup_2x3_opt.picus"),
    IRGenParams::new()
                        .lookup_callbacks(&LookupCallbackHandler)
}

basic_picus_test! {
    lookup_2x3_zerosel_circuit,
    Lookup2x3ZeroSelCircuitSynthesis::default(),
    include_str!("expected/picus/lookup_2x3.picus"),
    include_str!("expected/picus/lookup_2x3_opt.picus"),
    IRGenParams::new()
                        .lookup_callbacks(&LookupCallbackHandler)
}

synthesis_impl!(LookupCircuitSynthesis, lookup::LookupCircuit<Fr>, [0], [1]);
synthesis_impl!(
    Lookup2x3CircuitSynthesis,
    lookup::two_by_three::Lookup2x3Circuit<Fr>,
    [0],
    [1]
);
synthesis_impl!(
    Lookup2x3FixedCircuitSynthesis,
    lookup::two_by_three_fixed::Lookup2x3Circuit<Fr>,
    [0],
    [1]
);
synthesis_impl!(
    Lookup2x3ZeroSelCircuitSynthesis,
    lookup::two_by_three_zerosel::Lookup2x3ZeroSelCircuit<Fr>,
    [0],
    [1]
);

struct LookupCallbackHandler;

impl<F: Field> LookupCallbacks<F, _Expression<F>> for LookupCallbackHandler {
    fn on_lookup<'a>(
        &self,
        _lookup: &'a Lookup<_Expression<F>>,
        _table: &dyn LookupTableGenerator<F>,
        _temps: &mut Temps,
    ) -> Result<IRStmt<ExprOrTemp<Cow<'a, _Expression<F>>>>, LookupError> {
        Ok(IRStmt::comment("Ignored lookup"))
    }
}
