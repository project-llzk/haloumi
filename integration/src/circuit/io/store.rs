//! Traits and types for storing arbitrary types into cells in a circuit.

use ff::{Field, PrimeField};

use crate::{
    Types,
    circuit::io::{
        CellReprSize,
        ctx::{LayoutAdaptor, OCtx},
    },
    ir::inject::InjectedIR,
};

/// Trait for serializing arbitrary types to a set of circuit cells.
pub trait StoreIntoCells<F: Field, C, Ts: Types<F>, L>: CellReprSize {
    /// Stores an instance of Self into a set of cells.
    fn store(
        self,
        ctx: &mut OCtx<F, Ts>,
        chip: &C,
        layouter: &mut impl LayoutAdaptor<F, Ts, Adaptee = L>,
        injected_ir: &mut InjectedIR<Ts::RegionIndex, Ts::Expression>,
    ) -> Result<(), Ts::Error>;
}

impl<const N: usize, F: PrimeField, C, Ts: Types<F>, L, T: StoreIntoCells<F, C, Ts, L>>
    StoreIntoCells<F, C, Ts, L> for [T; N]
{
    fn store(
        self,
        ctx: &mut OCtx<F, Ts>,
        chip: &C,
        layouter: &mut impl LayoutAdaptor<F, Ts, Adaptee = L>,
        injected_ir: &mut InjectedIR<Ts::RegionIndex, Ts::Expression>,
    ) -> Result<(), Ts::Error> {
        self.into_iter()
            .try_for_each(|t| t.store(ctx, chip, layouter, injected_ir))
    }
}

macro_rules! store_tuple {
    () => {
        store_tuple!(@impl [] [] [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12] [0 1 2 3 4 5 6 7 8 9 10 11]);
    };

    (@impl [$($done:ident)*] [$($idxs:tt)*] [$head:ident $($rest:ident)*] [$i:tt $($is:tt)*]) => {
        // Implement for tuple ($head, $done...)
        impl<
            F: Field, C, Ts: Types<F>, L,
            $head: StoreIntoCells<F, C, Ts, L>,
            $( $done: StoreIntoCells<F, C, Ts, L>, )*
        > StoreIntoCells<F, C, Ts, L> for ($head, $( $done, )*)
        {
            fn store(
                self,
                ctx: &mut OCtx<F, Ts>,
                chip: &C,
                layouter: &mut impl LayoutAdaptor<F, Ts, Adaptee = L>,
                injected_ir: &mut InjectedIR<Ts::RegionIndex, Ts::Expression>,
            ) -> Result<(), Ts::Error> {
                // Call fields by index
                $(
                    self.$idxs.store(ctx, chip, layouter, injected_ir)?;
                )*
                self.$i.store(ctx, chip, layouter, injected_ir)?;
                Ok(())
            }
        }

        // Recurse
        store_tuple!(
            @impl [$head $($done)*] [$($idxs)* $i] [$($rest)*] [$($is)*]
        );
    };

    // Stop when no identifiers remain
    (@impl [$($done:ident)*] [$($idxs:tt)*] [] $rem:tt) => {
        // Also emit the 0-tuple base case
        impl<F: Field, C, Ts: Types<F>, L> StoreIntoCells<F, C, Ts, L> for () {
            fn store(
                self,
                _: &mut OCtx<F, Ts>,
                _: &C,
                _: &mut impl LayoutAdaptor<F, Ts, Adaptee = L>,
                _: &mut InjectedIR<Ts::RegionIndex, Ts::Expression>,
            ) -> Result<(), Ts::Error> {
                Ok(())
            }
        }
    };

}

store_tuple!();

/// Helper trait for containers of [`StoreIntoCells`] implementations.
///
/// This trait does not require implementing [`CellReprSize`] so it's
/// convenient for types such as Vec or Option.
pub trait StoreIntoCellsDyn<F: Field, C, Ts: Types<F>, L> {
    /// Stores an instance of Self into a set of cells.
    fn store_dyn(
        self,
        ctx: &mut OCtx<F, Ts>,
        chip: &C,
        layouter: &mut impl LayoutAdaptor<F, Ts, Adaptee = L>,
        injected_ir: &mut InjectedIR<Ts::RegionIndex, Ts::Expression>,
    ) -> Result<(), Ts::Error>;
}

impl<T, F, C, Ts, L> StoreIntoCellsDyn<F, C, Ts, L> for T
where
    T: StoreIntoCells<F, C, Ts, L>,
    F: Field,
    Ts: Types<F>,
{
    fn store_dyn(
        self,
        ctx: &mut OCtx<F, Ts>,
        chip: &C,
        layouter: &mut impl LayoutAdaptor<F, Ts, Adaptee = L>,
        injected_ir: &mut InjectedIR<<Ts as Types<F>>::RegionIndex, <Ts as Types<F>>::Expression>,
    ) -> Result<(), <Ts as Types<F>>::Error> {
        self.store(ctx, chip, layouter, injected_ir)
    }
}

impl<T, F, C, Ts, L> StoreIntoCellsDyn<F, C, Ts, L> for Vec<T>
where
    T: StoreIntoCellsDyn<F, C, Ts, L>,
    F: Field,
    Ts: Types<F>,
{
    fn store_dyn(
        self,
        ctx: &mut OCtx<F, Ts>,
        chip: &C,
        layouter: &mut impl LayoutAdaptor<F, Ts, Adaptee = L>,
        injected_ir: &mut InjectedIR<<Ts as Types<F>>::RegionIndex, <Ts as Types<F>>::Expression>,
    ) -> Result<(), <Ts as Types<F>>::Error> {
        self.into_iter()
            .try_for_each(|e| e.store_dyn(ctx, chip, layouter, injected_ir))
    }
}

impl<T, F, C, Ts, L> StoreIntoCellsDyn<F, C, Ts, L> for Option<T>
where
    T: StoreIntoCellsDyn<F, C, Ts, L>,
    F: Field,
    Ts: Types<F>,
{
    fn store_dyn(
        self,
        ctx: &mut OCtx<F, Ts>,
        chip: &C,
        layouter: &mut impl LayoutAdaptor<F, Ts, Adaptee = L>,
        injected_ir: &mut InjectedIR<<Ts as Types<F>>::RegionIndex, <Ts as Types<F>>::Expression>,
    ) -> Result<(), <Ts as Types<F>>::Error> {
        self.into_iter()
            .try_for_each(|e| e.store_dyn(ctx, chip, layouter, injected_ir))
    }
}

impl<T, E, F, C, Ts, L> StoreIntoCellsDyn<F, C, Ts, L> for Result<T, E>
where
    T: StoreIntoCellsDyn<F, C, Ts, L>,
    F: Field,
    Ts: Types<F>,
    Ts::Error: From<E>,
{
    fn store_dyn(
        self,
        ctx: &mut OCtx<F, Ts>,
        chip: &C,
        layouter: &mut impl LayoutAdaptor<F, Ts, Adaptee = L>,
        injected_ir: &mut InjectedIR<<Ts as Types<F>>::RegionIndex, <Ts as Types<F>>::Expression>,
    ) -> Result<(), <Ts as Types<F>>::Error> {
        self?.store_dyn(ctx, chip, layouter, injected_ir)
    }
}
