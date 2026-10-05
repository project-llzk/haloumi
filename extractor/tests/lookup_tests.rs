//use std::borrow::Cow;
//
//use common::basic_test;
//use group::ff::Field;
//use halo2curves::bn256::Fr;
//use haloumi_ir::stmt::IRStmt;
//use haloumi_ir_gen::lookups::callbacks::LookupError;
//use haloumi_ir_gen::{
//    lookups::{callbacks::LookupCallbacks, table::LookupTableGenerator},
//    temps::{ExprOrTemp, Temps},
//};
//use haloumi_mock_halo2::Expression;
//use haloumi_synthesis::lookups::Lookup;
//use haloumi_test_circuits::lookup;
//
//mod common;
//
//struct LookupCallbackHandler;
//
//impl<F: Field> LookupCallbacks<F, Expression<F>> for LookupCallbackHandler {
//    fn on_lookup<'a>(
//        &self,
//        _: &'a Lookup<Expression<F>>,
//        _: &dyn LookupTableGenerator<F>,
//        _: &mut Temps,
//    ) -> Result<IRStmt<ExprOrTemp<Cow<'a, Expression<F>>>>, LookupError> {
//        Ok(IRStmt::comment("Ignored lookup"))
//    }
//}
//
//basic_test!(
//    lookup_circuit,
//    lookup::LookupCircuit::<Fr>::default(),
//    "lookup",
//    "lookup_opt",
//    Some(&LookupCallbackHandler)
//);
//basic_test!(
//    lookup_2x3_circuit,
//    lookup::two_by_three::Lookup2x3Circuit::<Fr>::default(),
//    "lookup_2x3",
//    "lookup_2x3_opt",
//    Some(&LookupCallbackHandler)
//);
//basic_test!(
//    lookup_2x3_fixed_circuit,
//    lookup::two_by_three_fixed::Lookup2x3Circuit::<Fr>::default(),
//    "lookup_2x3",
//    "lookup_2x3_opt",
//    Some(&LookupCallbackHandler)
//);
//basic_test!(
//    lookup_2x3_zerosel_circuit,
//    lookup::two_by_three_zerosel::Lookup2x3ZeroSelCircuit::<Fr>::default(),
//    "lookup_2x3",
//    "lookup_2x3_opt",
//    Some(&LookupCallbackHandler)
//);
