use haloumi_integration_macros::CellReprSize;

#[derive(CellReprSize)]
enum E {
    Value(usize),
}
