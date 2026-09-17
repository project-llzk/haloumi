use halo2curves::bn256::Fr;
use haloumi_mdnt_test_circuits::mul;
use mdnt_common::basic_test;

mod mdnt_common;

basic_test!(mul_circuit, mul::MulCircuit::<Fr>::default(), "mul_circuit", "mul_circuit_opt");
basic_test!(mul_flipped, mul::flipped_constraint::MulCircuit::<Fr>::default(), "mul_flipped_constraint", "mul_flipped_constraint_opt");
basic_test!(mul_fixed, mul::fixed_constraint::MulWithFixedConstraintCircuit::<Fr>::default(), "mul_with_fixed_constraint", "mul_with_fixed_constraint_opt");
basic_test!(recursive_groups, mul::recursive_groups::MulCircuit::<Fr>::default(), "recursive_groups", "recursive_groups_opt");
basic_test!(ten_plus_io, mul::ten_plus_io::MulCircuit::<Fr>::default(), "ten_plus_io", "ten_plus_io_opt");
basic_test!(grouped, mul::grouped::MulCircuit::<Fr>::default(), "grouped_muls", "grouped_muls_opt");
basic_test!(different_bodies, mul::grouped::different_bodies::MulCircuit::<Fr>::default(), "different_bodies", "different_bodies_opt");
basic_test!(same_body, mul::grouped::same_body::MulCircuit::<Fr>::default(), "same_body", "same_body_opt");
basic_test!(deep_callstack, mul::grouped::deep_callstack::MulCircuit::<Fr>::default(), "deep_callstack", "deep_callstack_opt");
// The extractor does not expose the legacy gate-rewriter callback yet.
basic_test!(mul_rewriter, mul::MulCircuit::<Fr>::default(), "mul_with_rewriter", "mul_with_rewriter_opt");
basic_test!(mul_inject, mul::injection::MulCircuit::<Fr>::default(), "mul_inject", "mul_inject_opt");
