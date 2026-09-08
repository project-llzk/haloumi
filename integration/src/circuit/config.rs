//! Traits related to circuit configuration.

/// Helper trait that enables composing types that can handle circuit
/// configuration.
pub trait AutoConfigure<CS, Output = Self> {
    /// Creates an instance of self using the constraint system.
    fn configure(meta: &mut CS) -> Output;
}

/// Creates an implementation of [`AutoConfigure`].
#[macro_export]
macro_rules! auto_conf_impl {
    ($T:ty, $method:ident) => {
        $crate::auto_conf_impl!($T, $method, midnight_proofs);
    };
    ($T:ty, $method:ident, $proofs:ident) => {
        impl<F: ff::Field> AutoConfigure<$proofs::plonk::ConstraintSystem<F>, $T> for $T {
            fn configure(meta: &mut $proofs::plonk::ConstraintSystem<F>) -> $T {
                meta.$method()
            }
        }
    };
}

impl<CS, T, const N: usize> AutoConfigure<CS> for [T; N]
where
    T: AutoConfigure<CS>,
{
    fn configure(meta: &mut CS) -> [T; N] {
        std::array::from_fn(|_| T::configure(meta))
    }
}

impl<CS> AutoConfigure<CS> for () {
    fn configure(_: &mut CS) -> Self {
        ()
    }
}

macro_rules! tuple_auto_conf_impl {
    () => {
        // Do nothing
    };
    ($h:ident $(,$t:ident)* $(,)?) => {
        tuple_auto_conf_impl!($( $t, )*);

        impl<CS, $h, $( $t, )*> AutoConfigure<CS> for ( $h, $( $t, )* )
        where
            $h: AutoConfigure<CS,  $h>,
            $( $t: AutoConfigure<CS,  $t>, )*
        {
            fn configure(meta: &mut CS) -> Self {
                (
                    $h::configure(meta),
                    $( $t::configure(meta), )*
                )
            }
        }
    };
}

tuple_auto_conf_impl!(A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12);
