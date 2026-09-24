use haloumi_integration_macros::{CellReprSize, LoadFromCells};

#[derive(CellReprSize, LoadFromCells)]
struct Named<A, B> {
    first: A,
    second: B,
}

#[derive(CellReprSize, LoadFromCells)]
struct Tuple<A, B>(A, B);

#[derive(CellReprSize, LoadFromCells)]
struct Unit;

#[derive(CellReprSize, LoadFromCells)]
#[field(ff::Field)]
struct WithWhere<A>
where
    A: Clone,
{
    value: A,
}
