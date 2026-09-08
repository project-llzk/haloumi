//! Integration support for IO related tasks in a circuit.

use num_bigint::BigUint;

pub mod ctx;
pub mod load;
pub mod store;

/// Trait for defining how many cells in a circuit's table a type would take.
pub trait CellReprSize {
    /// Number of cells the type occupies.
    const SIZE: usize;
}

impl<const N: usize, T: CellReprSize> CellReprSize for [T; N] {
    const SIZE: usize = N * T::SIZE;
}

macro_rules! zero_size_repr {
    ($t:ty) => {
        impl crate::circuit::io::CellReprSize for $t {
            const SIZE: usize = 0;
        }
    };
}

zero_size_repr!(bool);
zero_size_repr!(u8);
zero_size_repr!(usize);
zero_size_repr!(BigUint);

macro_rules! tuple_size {
    () => {
        impl CellReprSize for () {
            const SIZE: usize =  0;
        }
    };
    ($h:ident $(,$t:ident)* $(,)?) => {
        tuple_size!($( $t, )*);

        impl<$h, $( $t, )*> CellReprSize for (
                $h, $( $t, )*
            )
        where
            $h: CellReprSize,
            $( $t: CellReprSize, )*
        {
            const SIZE: usize = $h::SIZE + $( $t::SIZE + )* 0;

        }
    };
}

tuple_size!(A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12);
