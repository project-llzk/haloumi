#[test]
fn pass() {
    macrotest::expand_args("tests/expand/cell_repr_size/pass/*.rs", ["--ugly"]);
}
