use haloumi_integration_macros::CellReprSize;

#[derive(CellReprSize)]
struct Named<A, B> {
    first: A,
    second: B,
}

#[derive(CellReprSize)]
struct Tuple<A, B>(A, B);

#[derive(CellReprSize)]
struct Unit;

#[derive(CellReprSize)]
struct WithWhere<A>
where
    A: Clone,
{
    value: A,
}
