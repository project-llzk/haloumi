#[test]
fn pass() {
    macrotest::expand_args("tests/expand/store_into_cells/pass/*.rs", ["--ugly"]);
}

#[test]
fn enum_error() {
    macrotest::expand_args("tests/expand/store_into_cells/fail/enum.rs", ["--ugly"]);
}

#[test]
fn union_error() {
    macrotest::expand_args("tests/expand/store_into_cells/fail/union.rs", ["--ugly"]);
}
