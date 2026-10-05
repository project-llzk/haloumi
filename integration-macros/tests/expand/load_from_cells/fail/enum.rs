use haloumi_integration_macros::LoadFromCells;

#[derive(LoadFromCells)]
enum E {
    Value(usize),
}
