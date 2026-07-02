use halo2curves::bn256::Fr;
use haloumi_mdnt_test_circuits::fibonacci;
use mdnt_common::{basic_test, synthesis_impl};

mod mdnt_common;

basic_test! {
    fibonacci_circuit,
    FibonacciCircuitSynthesis::default(),
    "fibonacci",
    "fibonacci_opt"
}

basic_test! {
    fibonacci_grouped_circuit,
    GroupedFibonacciCircuitSynthesis::default(),
    "fibonacci_grouped",
    "fibonacci_grouped_opt"
}

synthesis_impl!(
    FibonacciCircuitSynthesis,
    fibonacci::FibonacciCircuit<Fr>,
    [0, 1],
    [2]
);

synthesis_impl!(
    GroupedFibonacciCircuitSynthesis,
    fibonacci::grouped::FibonacciCircuit<Fr>,
    [0, 1],
    [2, 3]
);
