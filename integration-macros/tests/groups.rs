use haloumi_integration_macros::group;

#[group]
fn grouped(layouter: &mut (), #[input] input: (), #[output] output: &mut ()) {
    let _ = layouter;
    *output = input;
}

#[group]
fn renamed_layouter(#[layouter] region: &mut (), #[input] input: ()) {
    let _ = region;
    let _ = input;
}

#[test]
fn group_is_transparent_without_group_extraction() {
    let mut layouter = ();
    let mut output = ();
    grouped(&mut layouter, (), &mut output);
    renamed_layouter(&mut layouter, ());
}
