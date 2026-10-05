use common::basic_test;
use halo2curves::bn256::Fr;
use haloumi_test_circuits::fibonacci;

mod mdnt_common;

basic_test!(
    fibonacci_circuit,
    fibonacci::FibonacciCircuit::<Fr>::default(),
    "fibonacci",
    "fibonacci_opt"
);
basic_test!(
    fibonacci_grouped_circuit,
    fibonacci::grouped::FibonacciCircuit::<Fr>::default(),
    "fibonacci_grouped",
    "fibonacci_grouped_opt"
);
