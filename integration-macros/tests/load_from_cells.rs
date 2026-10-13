#[test]
fn pass() {
    macrotest::expand_args("tests/expand/load_from_cells/pass/*.rs", ["--ugly"]);
}
