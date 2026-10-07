//! Traits and types for loading arbitrary types from cells in a circuit.

use std::mem::MaybeUninit;

use ff::{Field, PrimeField};
use haloumi_core::{
    layouter::{LayoutAdaptor, Layouter},
    table::CellReprSize,
    types::Types,
};
use haloumi_ir::inject::InjectedIR;
use num_bigint::BigUint;

use crate::io::ctx::input::ICtx;

/// Trait for deserializing arbitrary types from a set of circuit cells.
pub trait LoadFromCells<F: Field, C, Ts: Types<F>>: Sized + CellReprSize {
    /// Loads an instance of Self from a set of cells.
    fn load(
        ctx: &mut ICtx<F, Ts>,
        chip: &C,
        layouter: &mut LayoutAdaptor<'_, impl Layouter<F, Ts::Error>>,
        injected_ir: &mut InjectedIR<Ts::RegionIndex, Ts::Expression>,
    ) -> Result<Self, Ts::Error>;

    /// Loads `n` instances of Self from a set of cells.
    fn load_many(
        n: usize,
        ctx: &mut ICtx<F, Ts>,
        chip: &C,
        layouter: &mut LayoutAdaptor<'_, impl Layouter<F, Ts::Error>>,
        injected_ir: &mut InjectedIR<Ts::RegionIndex, Ts::Expression>,
    ) -> Result<Vec<Self>, Ts::Error> {
        std::iter::repeat_with(|| Self::load(ctx, chip, layouter, injected_ir))
            .take(n)
            .collect()
    }
}

impl<const N: usize, F: PrimeField, C, Ts: Types<F>, T: LoadFromCells<F, C, Ts>>
    LoadFromCells<F, C, Ts> for [T; N]
{
    fn load(
        ctx: &mut ICtx<F, Ts>,
        chip: &C,
        layouter: &mut LayoutAdaptor<'_, impl Layouter<F, Ts::Error>>,
        injected_ir: &mut InjectedIR<Ts::RegionIndex, Ts::Expression>,
    ) -> Result<Self, Ts::Error> {
        let mut out: [MaybeUninit<T>; N] = [const { MaybeUninit::uninit() }; N];
        for e in &mut out[..] {
            e.write(T::load(ctx, chip, layouter, injected_ir)?);
        }
        Ok(out.map(|e| unsafe { e.assume_init() }))
    }
}

macro_rules! load_const {
    ($t:ty) => {
        impl<C, F: PrimeField, Ts: Types<F>> LoadFromCells<F, C, Ts> for $t {
            fn load(
                ctx: &mut ICtx<F, Ts>,
                _chip: &C,
                _layouter: &mut LayoutAdaptor<'_, impl Layouter<F, Ts::Error>>,
                _injected_ir: &mut InjectedIR<Ts::RegionIndex, Ts::Expression>,
            ) -> Result<Self, Ts::Error> {
                Ok(ctx.primitive_constant()?)
            }
        }
    };
}

load_const!(bool);
load_const!(u8);
load_const!(usize);
load_const!(BigUint);

macro_rules! load_tuple {
    () => {
        impl<F: Field, C, Ts: Types<F>> LoadFromCells<F, C, Ts> for () {
            fn load(
                _: &mut ICtx<F, Ts>,
                _: &C,
                _: &mut  LayoutAdaptor<'_, impl Layouter<F, Ts::Error>>,
                _: &mut InjectedIR<Ts::RegionIndex, Ts::Expression>,
            ) -> Result<Self, Ts::Error> {
                Ok(())
            }
        }
    };

    ($h:ident $(,$t:ident)* $(,)?) => {
        load_tuple!($( $t, )*);

        impl<F, C, Ts, $h, $( $t, )*> LoadFromCells<F, C, Ts> for (
                $h, $( $t, )*
            )
        where
            F: Field,
            Ts: Types<F>,
            $h: LoadFromCells<F, C, Ts>,
            $( $t: LoadFromCells<F, C, Ts>, )*
        {
            fn load(
                ctx: &mut ICtx<F, Ts>,
                chip: &C,
                layouter: &mut LayoutAdaptor<'_, impl Layouter<F, Ts::Error>>,
                injected_ir: &mut InjectedIR<Ts::RegionIndex,Ts::Expression>,
            ) -> Result<Self, Ts::Error>
            {
                Ok((
                    $h::load(ctx, chip, layouter, injected_ir)?,
                    $( $t::load(ctx, chip, layouter, injected_ir)?, )*
                ))
            }
        }
    };
}

load_tuple!(A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12);
