use haloumi_integration_macros::{CellReprSize, StoreIntoCells};

#[derive(CellReprSize, StoreIntoCells)]
struct Named<A, B> {
    first: A,
    second: B,
}

#[derive(CellReprSize, StoreIntoCells)]
struct Tuple<A, B>(A, B);

#[derive(CellReprSize, StoreIntoCells)]
struct Unit;

#[derive(CellReprSize, StoreIntoCells)]
#[field(ff::Field)]
struct WithWhere<A>
where
    A: Clone,
{
    value: A,
}
