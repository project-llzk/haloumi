use haloumi_integration_macros::group;

#[group]
fn grouped(layouter: &mut (), #[input] input: (), #[output] output: &mut ()) {
    let _ = layouter;
    *output = input;
}

#[group]
fn renamed_layouter(#[layouter] region: &mut (), #[input] input: ()) {
    let _ = region;
    #[allow(path_statements)]
    input;
}

// With group extraction disabled, `#[group]` must transparently forward the
// layouter. This is a smoke test for that expansion; recording groups requires
// a layouter that implements the extraction hooks.
#[test]
fn group_is_transparent_without_group_extraction() {
    let mut layouter = ();
    let mut output = ();
    grouped(&mut layouter, (), &mut output);
    renamed_layouter(&mut layouter, ());
}
