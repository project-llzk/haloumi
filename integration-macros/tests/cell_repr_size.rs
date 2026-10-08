#[test]
fn pass() {
    macrotest::expand_args("tests/expand/cell_repr_size/pass/*.rs", ["--ugly"]);
}

#[test]
fn enum_error() {
    macrotest::expand_args("tests/expand/cell_repr_size/fail/enum.rs", ["--ugly"]);
}

#[test]
fn union_error() {
    macrotest::expand_args("tests/expand/cell_repr_size/fail/union.rs", ["--ugly"]);
}
