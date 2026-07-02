use halo2curves::bn256::Fr;
use haloumi::ir::r#gen::IRGenParams;
use haloumi_mdnt_test_circuits::mul;
use mdnt_common::basic_test;
use mdnt_common::synthesis_impl;

mod mdnt_common;

basic_test! {
    mul_circuit,
    MulCircuitSynthesis::default(),
    "mul_circuit",
    "mul_circuit_opt", Fr
}

basic_test! {
    mul_flipped,
    MulFlippedCircuitSynthesis::default(),
    "mul_flipped_constraint",
    "mul_flipped_constraint_opt", Fr
}

basic_test! {
    mul_fixed,
    MulFixedConstraintCircuitSynthesis::default(),
    "mul_with_fixed_constraint",
    "mul_with_fixed_constraint_opt", Fr
}

basic_test! {
    recursive_groups,
    RecursiveMulCircuitSynthesis::default(),
    "recursive_groups",
    "recursive_groups_opt", Fr
}

// This test makes sure that the order in which input and output variables are printed is
// the same as their declaration order.
basic_test! {
    ten_plus_io,
    TenPlusIOCircuitSynthesis::default(),
    "ten_plus_io",
    "ten_plus_io_opt", Fr
}

basic_test! {
    grouped,
    GroupedMulsCircuitSynthesis::default(),
    "grouped_muls",
    "grouped_muls_opt", Fr
}

basic_test! {
    different_bodies,
    DifferentBodiesCircuitSynthesis::default(),
    "different_bodies",
    "different_bodies_opt", Fr
}

basic_test! {
    same_body,
    SameBodyCircuitSynthesis::default(),
    "same_body",
    "same_body_opt", Fr
}

basic_test! {
    deep_callstack,
    DeepCallstackCircuitSynthesis::default(),
    "deep_callstack",
    "deep_callstack_opt", Fr
}

basic_test! {
    mul_rewriter,
    MulCircuitSynthesis::default(),
    "mul_with_rewriter",
    "mul_with_rewriter_opt", Fr,
    IRGenParams::new().gate_callbacks(&mdnt_common::GC)
}

mod mul_inject {
    use crate::ensure_validation;
    use haloumi::{
        driver::Driver,
        ir::r#gen::{
            IRGenParams, circuit::resolved::ResolvedIRCircuit, expressions::ExpressionInRow,
        },
        synthesis::CircuitSynthesis,
    };
    use haloumi_core::table::RegionIndex;
    use haloumi_ir::{CmpOp, stmt::IRStmt};
    use haloumi_midnight_integration::halo2_proofs::plonk::Expression;
    use haloumi_midnight_integration::plonk::_Expression;
    use haloumi_midnight_integration::plonk::ConstraintSystem;

    use super::*;

    const EXPECTED_PICUS: &str = include_str!("expected/picus/mul_inject.picus");
    const EXPECTED_OPT_PICUS: &str = include_str!("expected/picus/mul_inject_opt.picus");
    const EXPECTED_LLZK: &str = include_str!("expected/llzk/mul_inject.mlir");
    const EXPECTED_OPT_LLZK: &str = include_str!("expected/llzk/mul_inject_opt.mlir");

    fn ir_to_inject<'e>() -> Vec<(
        RegionIndex,
        IRStmt<ExpressionInRow<'e, _Expression<Fr>, Fr>>,
    )> {
        let mut cs = ConstraintSystem::<Fr>::default();
        let config = MulInjectCircuitSynthesis::configure(&mut cs);
        let a = config.col_a.cur();
        let hundrend = Expression::Constant(Fr::from(1000));
        let stmts = [
            IRStmt::constraint(CmpOp::Lt, a.clone(), hundrend.clone())
                .map(&mut |e| ExpressionInRow::new(0, _Expression::from(e))),
            IRStmt::constraint(CmpOp::Ge, a, hundrend)
                .map(&mut |e| ExpressionInRow::new(1, _Expression::from(e))),
        ];

        let mut injected = vec![];
        for row in 0..6 {
            let index = RegionIndex::from(row / 2);
            let offset = row % 2;

            let payload = (index, stmts[offset].clone());
            log::debug!("payload = {payload:?}");
            injected.push(payload);
        }
        injected
    }

    fn generate_ir(driver: &mut Driver) -> ResolvedIRCircuit {
        let circuit = MulInjectCircuitSynthesis::default();
        let syn = driver.synthesize(&circuit).unwrap();

        let mut unresolved = driver.generate_ir(&syn, IRGenParams::new()).unwrap();
        let ir = ir_to_inject();
        unresolved.inject_ir(ir, &syn).unwrap();
        ensure_validation!(unresolved);
        let resolved = unresolved.resolve().unwrap();
        ensure_validation!(resolved);
        resolved
    }

    #[cfg(feature = "picus-backend")]
    #[test]
    fn picus() {
        mdnt_common::setup();
        let mut driver = Driver::default();
        let resolved = generate_ir(&mut driver);

        mdnt_common::picus::check_picus(
            &driver,
            &resolved,
            mdnt_common::picus::picus_params(),
            EXPECTED_PICUS,
        );
    }

    #[cfg(feature = "picus-backend")]
    #[test]
    fn opt_picus() {
        mdnt_common::setup();
        let mut driver = Driver::default();
        let mut resolved = generate_ir(&mut driver);

        resolved.constant_fold().unwrap();
        ensure_validation!(resolved);
        resolved.canonicalize();
        ensure_validation!(resolved);

        mdnt_common::picus::check_picus(
            &driver,
            &resolved,
            mdnt_common::picus::opt_picus_params(),
            EXPECTED_OPT_PICUS,
        );
    }

    #[cfg(feature = "llzk-backend")]
    #[test]
    fn llzk() {
        mdnt_common::setup();
        let mut driver = Driver::default();
        let resolved = generate_ir(&mut driver);

        let ctx = llzk::context::LlzkContext::new();
        mdnt_common::llzk::check_llzk(
            &driver,
            &resolved,
            mdnt_common::llzk::llzk_params::<Fr>(&ctx),
            EXPECTED_LLZK,
        );
    }

    #[cfg(feature = "llzk-backend")]
    #[test]
    fn opt_llzk() {
        mdnt_common::setup();
        let mut driver = Driver::default();
        let mut resolved = generate_ir(&mut driver);

        resolved.constant_fold().unwrap();
        ensure_validation!(resolved);
        resolved.canonicalize();
        ensure_validation!(resolved);

        let ctx = llzk::context::LlzkContext::new();
        mdnt_common::llzk::check_llzk(
            &driver,
            &resolved,
            mdnt_common::llzk::opt_llzk_params::<Fr>(&ctx),
            EXPECTED_OPT_LLZK,
        );
    }
}

synthesis_impl!(MulCircuitSynthesis, mul::MulCircuit<Fr>, [0], [1]);
synthesis_impl!(
    DeepCallstackCircuitSynthesis,
    mul::grouped::deep_callstack::MulCircuit<Fr>,
    [0],
    [1]
);
synthesis_impl!(
    SameBodyCircuitSynthesis,
    mul::grouped::same_body::MulCircuit<Fr>,
    [0],
    [1]
);
synthesis_impl!(
    DifferentBodiesCircuitSynthesis,
    mul::grouped::different_bodies::MulCircuit<Fr>,
    [0],
    [1]
);
synthesis_impl!(
    GroupedMulsCircuitSynthesis,
    mul::grouped::MulCircuit<Fr>,
    [0],
    [1]
);
synthesis_impl!(
    TenPlusIOCircuitSynthesis,
    mul::ten_plus_io::MulCircuit<Fr>,
    Vec::from_iter(0..=10),
    Vec::from_iter(11..=21)
);
synthesis_impl!(
    RecursiveMulCircuitSynthesis,
    mul::recursive_groups::MulCircuit<Fr>,
    [0, 1, 2, 3],
    [4]
);
synthesis_impl!(
    MulFixedConstraintCircuitSynthesis,
    mul::fixed_constraint::MulWithFixedConstraintCircuit<Fr>,
    [0],
    [1]
);
synthesis_impl!(
    MulInjectCircuitSynthesis,
    mul::injection::MulCircuit<Fr>,
    [0],
    [1, 2, 3]
);
synthesis_impl!(
    MulFlippedCircuitSynthesis,
    mul::flipped_constraint::MulCircuit<Fr>,
    [0],
    [1]
);
