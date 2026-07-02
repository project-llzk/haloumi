use halo2curves::bn256::Fr;
use haloumi::ir::r#gen::IRGenParams;
use haloumi_zcash_test_circuits::mul;
use zcash_common::llzk::basic_llzk_test;
use zcash_common::picus::basic_picus_test;
use zcash_common::synthesis_impl;

mod zcash_common;

basic_picus_test! {
    mul_circuit,
    MulCircuitSynthesis::default(),
    include_str!("expected/picus/mul_circuit.picus"),
    include_str!("expected/picus/mul_circuit_opt.picus")
}

basic_llzk_test! {
    mul_circuit,
    MulCircuitSynthesis::default(),
    include_str!("expected/llzk/mul_circuit.mlir"),
    include_str!("expected/llzk/mul_circuit_opt.mlir"),
    Fr
}

basic_picus_test! {
    mul_flipped,
    MulFlippedCircuitSynthesis::default(),
    include_str!("expected/picus/mul_flipped_constraint.picus"),
    include_str!("expected/picus/mul_flipped_constraint_opt.picus")
}

basic_picus_test! {
    mul_fixed,
    MulFixedConstraintCircuitSynthesis::default(),
    include_str!("expected/picus/mul_with_fixed_constraint_zcash.picus"),
    include_str!("expected/picus/mul_with_fixed_constraint_opt.picus")
}

basic_picus_test! {
    recursive_groups,
    RecursiveMulCircuitSynthesis::default(),
    include_str!("expected/picus/recursive_groups.picus"),
    include_str!("expected/picus/recursive_groups_opt.picus")
}

// This test makes sure that the order in which input and output variables are printed is
// the same as their declaration order.
basic_picus_test! {
    ten_plus_io,
    TenPlusIOCircuitSynthesis::default(),
    include_str!("expected/picus/ten_plus_io.picus"),
    include_str!("expected/picus/ten_plus_io_opt.picus")
}

basic_picus_test! {
    grouped,
    GroupedMulsCircuitSynthesis::default(),
    include_str!("expected/picus/grouped_muls.picus"),
    include_str!("expected/picus/grouped_muls_opt.picus")
}

basic_picus_test! {
    different_bodies,
    DifferentBodiesCircuitSynthesis::default(),
    include_str!("expected/picus/different_bodies.picus"),
    include_str!("expected/picus/different_bodies_opt.picus")
}

basic_picus_test! {
    same_body,
    SameBodyCircuitSynthesis::default(),
    include_str!("expected/picus/same_body.picus"),
    include_str!("expected/picus/same_body_opt.picus")
}

basic_picus_test! {
    deep_callstack,
    DeepCallstackCircuitSynthesis::default(),
    include_str!("expected/picus/deep_callstack.picus"),
    include_str!("expected/picus/deep_callstack_opt.picus")
}

basic_picus_test! {
    mul_rewriter,
    MulCircuitSynthesis::default(),
    include_str!("expected/picus/mul_with_rewriter.picus"),
    include_str!("expected/picus/mul_with_rewriter_opt.picus"),
    IRGenParams::new().gate_callbacks(&zcash_common::GC)
}

#[cfg(feature = "picus-backend")]
mod mul_inject {
    use crate::ensure_validation;
    use haloumi::ir::r#gen::{
        IRGenParams, circuit::resolved::ResolvedIRCircuit, expressions::ExpressionInRow,
    };
    use haloumi_core::{
        info_traits::CreateQuery as _, query::Advice as Adv, table::Column as Col,
        table::RegionIndex,
    };
    use haloumi_ir::{CmpOp, stmt::IRStmt};
    use zcash_halo2_proofs::plonk::AdviceQuery;
    use zcash_halo2_proofs::plonk::{Circuit, ConstraintSystem};
    use zcash_halo2_proofs::{dev::haloumi::Haloumi, plonk::Expression};

    use super::*;

    const EXPECTED_PICUS: &str = include_str!("expected/picus/mul_inject.picus");
    const EXPECTED_OPT_PICUS: &str = include_str!("expected/picus/mul_inject_opt.picus");

    fn ir_to_inject<'e>() -> Vec<(RegionIndex, IRStmt<ExpressionInRow<'e, Expression<Fr>, Fr>>)> {
        let mut cs = ConstraintSystem::<Fr>::default();
        let config = MulInjectCircuitSynthesis::configure(&mut cs);
        let a = AdviceQuery::query_expr(Col::<Adv>::from(config.col_a).index(), 0);
        let hundrend = Expression::Constant(Fr::from(1000));
        let stmts = [
            IRStmt::constraint(CmpOp::Lt, a.clone(), hundrend.clone())
                .map(&mut |e| ExpressionInRow::new(0, e)),
            IRStmt::constraint(CmpOp::Ge, a, hundrend).map(&mut |e| ExpressionInRow::new(1, e)),
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

    fn generate_ir(driver: &mut Haloumi) -> ResolvedIRCircuit {
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

    #[test]
    fn picus() {
        zcash_common::setup();
        let mut driver = Haloumi::default();
        let resolved = generate_ir(&mut driver);

        zcash_common::picus::check_picus(
            &driver,
            &resolved,
            zcash_common::picus::picus_params(),
            EXPECTED_PICUS,
        );
    }

    #[test]
    fn opt_picus() {
        zcash_common::setup();
        let mut driver = Haloumi::default();
        let mut resolved = generate_ir(&mut driver);

        resolved.constant_fold().unwrap();
        ensure_validation!(resolved);
        resolved.canonicalize();
        ensure_validation!(resolved);

        zcash_common::picus::check_picus(
            &driver,
            &resolved,
            zcash_common::picus::opt_picus_params(),
            EXPECTED_OPT_PICUS,
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
