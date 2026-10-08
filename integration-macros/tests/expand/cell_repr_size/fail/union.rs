use haloumi_integration_macros::CellReprSize;

#[derive(CellReprSize)]
union U {
    value: usize,
}
