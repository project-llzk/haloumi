use haloumi_integration_macros::StoreIntoCells;

#[derive(StoreIntoCells)]
union U {
    value: usize,
}
