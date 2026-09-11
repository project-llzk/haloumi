//! Traits related to circuit configuration.

pub use crate::core::auto_conf::AutoConfigure;

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

/// Creates an implementation of [`AutoConfigure`] for a root type.
#[macro_export]
macro_rules! __impl_root_auto_configure_impl {
    ($ty:ty, $method:ident, $($cs:ident)::+, $field:path) => {
        impl<F: $field> $crate::core::auto_conf::AutoConfigure<$($cs)::+<F>, $ty> for $ty {
            fn configure(meta: &mut $($cs)::+<F>) -> $ty {
                meta.$method()
            }
        }
    };
}
