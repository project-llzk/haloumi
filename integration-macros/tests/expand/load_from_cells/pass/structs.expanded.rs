use haloumi_integration_macros::{CellReprSize, LoadFromCells};
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
impl<
    A,
    B,
    __HaloumiField,
    __HaloumiChip,
    __HaloumiTypes,
> haloumi_integration::extractor::core::io::load::LoadFromCells<
    __HaloumiField,
    __HaloumiChip,
    __HaloumiTypes,
> for Named<A, B>
where
    __HaloumiField: ff::Field,
    __HaloumiTypes: haloumi_integration::Types<__HaloumiField>,
    A: haloumi_integration::extractor::core::io::load::LoadFromCells<
        __HaloumiField,
        __HaloumiChip,
        __HaloumiTypes,
    >,
    B: haloumi_integration::extractor::core::io::load::LoadFromCells<
        __HaloumiField,
        __HaloumiChip,
        __HaloumiTypes,
    >,
{
    fn load(
        ctx: &mut haloumi_integration::extractor::core::io::ctx::input::ICtx<
            __HaloumiField,
            __HaloumiTypes,
        >,
        chip: &__HaloumiChip,
        layouter: &mut haloumi_integration::core::layouter::LayoutAdaptor<
            '_,
            impl haloumi_integration::core::layouter::Layouter<
                __HaloumiField,
                __HaloumiTypes::Error,
            >,
        >,
        injected_ir: &mut haloumi_integration::ir::inject::InjectedIR<
            __HaloumiTypes::RegionIndex,
            __HaloumiTypes::Expression,
        >,
    ) -> Result<Self, __HaloumiTypes::Error> {
        Ok(Self {
            first: ctx.load(chip, layouter, injected_ir)?,
            second: ctx.load(chip, layouter, injected_ir)?,
        })
    }
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
impl<
    A,
    B,
    __HaloumiField,
    __HaloumiChip,
    __HaloumiTypes,
> haloumi_integration::extractor::core::io::load::LoadFromCells<
    __HaloumiField,
    __HaloumiChip,
    __HaloumiTypes,
> for Tuple<A, B>
where
    __HaloumiField: ff::Field,
    __HaloumiTypes: haloumi_integration::Types<__HaloumiField>,
    A: haloumi_integration::extractor::core::io::load::LoadFromCells<
        __HaloumiField,
        __HaloumiChip,
        __HaloumiTypes,
    >,
    B: haloumi_integration::extractor::core::io::load::LoadFromCells<
        __HaloumiField,
        __HaloumiChip,
        __HaloumiTypes,
    >,
{
    fn load(
        ctx: &mut haloumi_integration::extractor::core::io::ctx::input::ICtx<
            __HaloumiField,
            __HaloumiTypes,
        >,
        chip: &__HaloumiChip,
        layouter: &mut haloumi_integration::core::layouter::LayoutAdaptor<
            '_,
            impl haloumi_integration::core::layouter::Layouter<
                __HaloumiField,
                __HaloumiTypes::Error,
            >,
        >,
        injected_ir: &mut haloumi_integration::ir::inject::InjectedIR<
            __HaloumiTypes::RegionIndex,
            __HaloumiTypes::Expression,
        >,
    ) -> Result<Self, __HaloumiTypes::Error> {
        Ok(
            Self(
                ctx.load(chip, layouter, injected_ir)?,
                ctx.load(chip, layouter, injected_ir)?,
            ),
        )
    }
}
struct Unit;
impl haloumi_integration::core::table::CellReprSize for Unit {
    const SIZE: usize = 0;
}
impl<
    __HaloumiField,
    __HaloumiChip,
    __HaloumiTypes,
> haloumi_integration::extractor::core::io::load::LoadFromCells<
    __HaloumiField,
    __HaloumiChip,
    __HaloumiTypes,
> for Unit
where
    __HaloumiField: ff::Field,
    __HaloumiTypes: haloumi_integration::Types<__HaloumiField>,
{
    fn load(
        ctx: &mut haloumi_integration::extractor::core::io::ctx::input::ICtx<
            __HaloumiField,
            __HaloumiTypes,
        >,
        chip: &__HaloumiChip,
        layouter: &mut haloumi_integration::core::layouter::LayoutAdaptor<
            '_,
            impl haloumi_integration::core::layouter::Layouter<
                __HaloumiField,
                __HaloumiTypes::Error,
            >,
        >,
        injected_ir: &mut haloumi_integration::ir::inject::InjectedIR<
            __HaloumiTypes::RegionIndex,
            __HaloumiTypes::Expression,
        >,
    ) -> Result<Self, __HaloumiTypes::Error> {
        Ok(Self)
    }
}
#[field(ff::Field)]
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
impl<
    A,
    __HaloumiField,
    __HaloumiChip,
    __HaloumiTypes,
> haloumi_integration::extractor::core::io::load::LoadFromCells<
    __HaloumiField,
    __HaloumiChip,
    __HaloumiTypes,
> for WithWhere<A>
where
    A: Clone,
    __HaloumiField: ff::Field,
    __HaloumiTypes: haloumi_integration::Types<__HaloumiField>,
    A: haloumi_integration::extractor::core::io::load::LoadFromCells<
        __HaloumiField,
        __HaloumiChip,
        __HaloumiTypes,
    >,
{
    fn load(
        ctx: &mut haloumi_integration::extractor::core::io::ctx::input::ICtx<
            __HaloumiField,
            __HaloumiTypes,
        >,
        chip: &__HaloumiChip,
        layouter: &mut haloumi_integration::core::layouter::LayoutAdaptor<
            '_,
            impl haloumi_integration::core::layouter::Layouter<
                __HaloumiField,
                __HaloumiTypes::Error,
            >,
        >,
        injected_ir: &mut haloumi_integration::ir::inject::InjectedIR<
            __HaloumiTypes::RegionIndex,
            __HaloumiTypes::Expression,
        >,
    ) -> Result<Self, __HaloumiTypes::Error> {
        Ok(Self {
            value: ctx.load(chip, layouter, injected_ir)?,
        })
    }
}
