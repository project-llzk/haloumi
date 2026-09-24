use haloumi_integration_macros::{CellReprSize, StoreIntoCells};
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
> haloumi_integration::extractor::core::io::store::StoreIntoCells<
    __HaloumiField,
    __HaloumiChip,
    __HaloumiTypes,
> for Named<A, B>
where
    __HaloumiField: ff::Field,
    __HaloumiTypes: haloumi_integration::Types<__HaloumiField>,
    A: haloumi_integration::extractor::core::io::store::StoreIntoCells<
        __HaloumiField,
        __HaloumiChip,
        __HaloumiTypes,
    >,
    B: haloumi_integration::extractor::core::io::store::StoreIntoCells<
        __HaloumiField,
        __HaloumiChip,
        __HaloumiTypes,
    >,
{
    fn store(
        self,
        ctx: &mut haloumi_integration::extractor::core::io::ctx::output::OCtx<
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
    ) -> Result<(), __HaloumiTypes::Error> {
        let Self { first, second } = self;
        <A as haloumi_integration::extractor::core::io::store::StoreIntoCells<
            __HaloumiField,
            __HaloumiChip,
            __HaloumiTypes,
        >>::store(first, ctx, chip, layouter, injected_ir)?;
        <B as haloumi_integration::extractor::core::io::store::StoreIntoCells<
            __HaloumiField,
            __HaloumiChip,
            __HaloumiTypes,
        >>::store(second, ctx, chip, layouter, injected_ir)?;
        Ok(())
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
> haloumi_integration::extractor::core::io::store::StoreIntoCells<
    __HaloumiField,
    __HaloumiChip,
    __HaloumiTypes,
> for Tuple<A, B>
where
    __HaloumiField: ff::Field,
    __HaloumiTypes: haloumi_integration::Types<__HaloumiField>,
    A: haloumi_integration::extractor::core::io::store::StoreIntoCells<
        __HaloumiField,
        __HaloumiChip,
        __HaloumiTypes,
    >,
    B: haloumi_integration::extractor::core::io::store::StoreIntoCells<
        __HaloumiField,
        __HaloumiChip,
        __HaloumiTypes,
    >,
{
    fn store(
        self,
        ctx: &mut haloumi_integration::extractor::core::io::ctx::output::OCtx<
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
    ) -> Result<(), __HaloumiTypes::Error> {
        let Self(__haloumi_field_0, __haloumi_field_1) = self;
        <A as haloumi_integration::extractor::core::io::store::StoreIntoCells<
            __HaloumiField,
            __HaloumiChip,
            __HaloumiTypes,
        >>::store(__haloumi_field_0, ctx, chip, layouter, injected_ir)?;
        <B as haloumi_integration::extractor::core::io::store::StoreIntoCells<
            __HaloumiField,
            __HaloumiChip,
            __HaloumiTypes,
        >>::store(__haloumi_field_1, ctx, chip, layouter, injected_ir)?;
        Ok(())
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
> haloumi_integration::extractor::core::io::store::StoreIntoCells<
    __HaloumiField,
    __HaloumiChip,
    __HaloumiTypes,
> for Unit
where
    __HaloumiField: ff::Field,
    __HaloumiTypes: haloumi_integration::Types<__HaloumiField>,
{
    fn store(
        self,
        ctx: &mut haloumi_integration::extractor::core::io::ctx::output::OCtx<
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
    ) -> Result<(), __HaloumiTypes::Error> {
        Ok(())
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
> haloumi_integration::extractor::core::io::store::StoreIntoCells<
    __HaloumiField,
    __HaloumiChip,
    __HaloumiTypes,
> for WithWhere<A>
where
    A: Clone,
    __HaloumiField: ff::Field,
    __HaloumiTypes: haloumi_integration::Types<__HaloumiField>,
    A: haloumi_integration::extractor::core::io::store::StoreIntoCells<
        __HaloumiField,
        __HaloumiChip,
        __HaloumiTypes,
    >,
{
    fn store(
        self,
        ctx: &mut haloumi_integration::extractor::core::io::ctx::output::OCtx<
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
    ) -> Result<(), __HaloumiTypes::Error> {
        let Self { value } = self;
        <A as haloumi_integration::extractor::core::io::store::StoreIntoCells<
            __HaloumiField,
            __HaloumiChip,
            __HaloumiTypes,
        >>::store(value, ctx, chip, layouter, injected_ir)?;
        Ok(())
    }
}
