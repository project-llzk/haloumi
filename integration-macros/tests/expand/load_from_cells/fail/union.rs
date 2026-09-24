use haloumi_integration_macros::LoadFromCells;

#[derive(LoadFromCells)]
union U {
    value: usize,
}
