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

/// Owns the initialized prefix of a [`MaybeUninit`] slice while it is being populated.
///
/// The invariant is that every slot in `slots[..initialized]` has been initialized exactly once,
/// and every remaining slot is uninitialized. `push` maintains this invariant by writing a value
/// before incrementing `initialized`.
struct InitializedPrefix<'a, T> {
    slots: &'a mut [MaybeUninit<T>],
    initialized: usize,
}

impl<'a, T> InitializedPrefix<'a, T> {
    fn new(slots: &'a mut [MaybeUninit<T>]) -> Self {
        Self {
            slots,
            initialized: 0,
        }
    }

    fn push(&mut self, value: T) {
        debug_assert!(self.initialized < self.slots.len());
        self.slots[self.initialized].write(value);
        self.initialized += 1;
    }

    /// Prevents the guard from dropping values once ownership is transferred to the array.
    fn disarm(&mut self) {
        self.initialized = 0;
    }
}

impl<T> Drop for InitializedPrefix<'_, T> {
    fn drop(&mut self) {
        for slot in &mut self.slots[..self.initialized] {
            // SAFETY: The guard invariant guarantees that every slot in this prefix was written
            // exactly once before `initialized` was incremented.
            unsafe { slot.assume_init_drop() };
        }
    }
}

/// Initializes an array without allocating, dropping its initialized prefix if initialization
/// returns an error or panics.
fn try_init_array<T, E, const N: usize>(
    mut init: impl FnMut(usize) -> Result<T, E>,
) -> Result<[T; N], E> {
    let mut out: [MaybeUninit<T>; N] = [const { MaybeUninit::uninit() }; N];
    {
        let mut initialized = InitializedPrefix::new(&mut out);
        for index in 0..N {
            initialized.push(init(index)?);
        }

        // The fully initialized array takes over responsibility for dropping its elements.
        initialized.disarm();
    }

    Ok(out.map(|slot| {
        // SAFETY: Successful completion writes all `N` slots before the guard is disarmed.
        unsafe { slot.assume_init() }
    }))
}

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
        try_init_array(|_| T::load(ctx, chip, layouter, injected_ir))
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::{cell::Cell, rc::Rc};

    struct DropSpy(Rc<Cell<usize>>);

    impl Drop for DropSpy {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    #[test]
    fn try_init_array_drops_the_initialized_prefix_on_error() {
        let drops = Rc::new(Cell::new(0));
        let result: Result<[DropSpy; 4], ()> = try_init_array(|index| {
            if index == 2 {
                Err(())
            } else {
                Ok(DropSpy(Rc::clone(&drops)))
            }
        });

        assert!(result.is_err());
        assert_eq!(drops.get(), 2);
    }

    #[test]
    fn try_init_array_transfers_elements_to_the_returned_array() {
        let drops = Rc::new(Cell::new(0));
        let array: [DropSpy; 3] = try_init_array(|_| Ok::<_, ()>(DropSpy(Rc::clone(&drops))))
            .expect("all array elements should initialize");

        assert_eq!(drops.get(), 0);
        drop(array);
        assert_eq!(drops.get(), 3);
    }
}
