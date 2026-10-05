#[test]
fn pass() {
    macrotest::expand_args("tests/expand/load_from_cells/pass/*.rs", ["--ugly"]);
}

#[test]
fn enum_error() {
    macrotest::expand_args("tests/expand/load_from_cells/fail/enum.rs", ["--ugly"]);
}

#[test]
fn union_error() {
    macrotest::expand_args("tests/expand/load_from_cells/fail/union.rs", ["--ugly"]);
}
