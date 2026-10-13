#[test]
fn pass() {
    macrotest::expand_args("tests/expand/store_into_cells/pass/*.rs", ["--ugly"]);
}
