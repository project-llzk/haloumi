use haloumi_integration_macros::StoreIntoCells;

#[derive(StoreIntoCells)]
enum E {
    Value(usize),
}
