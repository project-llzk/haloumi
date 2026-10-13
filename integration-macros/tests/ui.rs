#[test]
fn rejected_data_types() {
    let tests = trybuild::TestCases::new();
    tests.compile_fail("tests/ui/*/*.rs");
}
