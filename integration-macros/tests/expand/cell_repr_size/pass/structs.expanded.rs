use haloumi_integration_macros::CellReprSize;
struct Named<A, B> {
    first: A,
    second: B,
}
impl<A, B> haloumi_integration::core::table::CellReprSize for Named<A, B>
where
    A: haloumi_integration::core::table::CellReprSize,
    B: haloumi_integration::core::table::CellReprSize,
{
    const SIZE: usize = 0 + <A as haloumi_integration::core::table::CellReprSize>::SIZE
        + <B as haloumi_integration::core::table::CellReprSize>::SIZE;
}
struct Tuple<A, B>(A, B);
impl<A, B> haloumi_integration::core::table::CellReprSize for Tuple<A, B>
where
    A: haloumi_integration::core::table::CellReprSize,
    B: haloumi_integration::core::table::CellReprSize,
{
    const SIZE: usize = 0 + <A as haloumi_integration::core::table::CellReprSize>::SIZE
        + <B as haloumi_integration::core::table::CellReprSize>::SIZE;
}
struct Unit;
impl haloumi_integration::core::table::CellReprSize for Unit {
    const SIZE: usize = 0;
}
struct WithWhere<A>
where
    A: Clone,
{
    value: A,
}
impl<A> haloumi_integration::core::table::CellReprSize for WithWhere<A>
where
    A: Clone,
    A: haloumi_integration::core::table::CellReprSize,
{
    const SIZE: usize = 0 + <A as haloumi_integration::core::table::CellReprSize>::SIZE;
}
