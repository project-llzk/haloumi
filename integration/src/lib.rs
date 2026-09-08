#![doc = include_str!("../README.md")]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use ff::{Field, PrimeField};
pub use haloumi_integration_macros::*;
use num_bigint::{BigInt, BigUint};
use num_traits::{Num as _, Signed as _};

use crate::error::Error;

pub mod circuit;
pub mod error;
pub mod expressions;
pub mod groups;
pub mod info_traits;
pub mod table;

/// Re-export of the core crate for simplifying dependency management in downstream clients.
pub mod core {
    pub use haloumi_core::*;
}
/// Re-export of the ir crate for simplifying dependency management in downstream clients.
pub mod ir {
    pub use haloumi_ir::*;
}

/// This trait defines the halo2 types required by this crate.
/// An implementation of halo2 compatible with this crate must have
/// some type that implements this trait s.t. it can be passed to traits
/// and types in this crate.
pub trait Types<F: Field> {
    /// Type for instance columns.
    type InstanceCol: std::fmt::Debug + Copy + Clone;
    /// Type for advice columns.
    type AdviceCol: std::fmt::Debug + Copy + Clone;
    /// Type for a cell.
    type Cell: std::fmt::Debug + Copy + Clone + core::table::DecomposeIn<Self::Cell>;
    /// Type for an assigned cell.
    type AssignedCell<V>;
    /// Region type.
    type Region<'a>;
    /// Error type.
    type Error: Into<Error> + From<Error>;
    /// Region index type
    type RegionIndex: std::hash::Hash + Copy + Eq;
    /// Expression type
    type Expression;
    /// Associated type for Rational.
    type Rational;
}

/// Parses a value of F from the given string.
pub fn parse_field<F: PrimeField>(s: &str) -> Result<F, Error> {
    if s.is_empty() {
        return Err(Error::FieldParsingError);
    }
    F::from_str_vartime(s).ok_or(Error::FieldParsingError)
}

/// Returns the modulus of the field as a [`BigUint`].
fn modulus<F: PrimeField>() -> BigUint {
    BigUint::from_str_radix(&F::MODULUS[2..], 16).unwrap()
}

/// Returns the modulus of the field as a [`BigInt`].
fn modulus_signed<F: PrimeField>() -> BigInt {
    BigInt::from_str_radix(&F::MODULUS[2..], 16).unwrap()
}

/// Converts a big unsigned integer into a prime field element.
pub fn big_to_fe<F: PrimeField>(e: BigUint) -> F {
    let modulus = modulus::<F>();
    let e = e % modulus;
    F::from_str_vartime(&e.to_str_radix(10)[..]).unwrap()
}

/// Converts a big signed integer into a prime field element.
/// If the value is negative it wraps around the field's modulus.
pub fn sbig_to_fe<F: PrimeField>(mut e: BigInt) -> F {
    let modulus = modulus_signed::<F>();
    e = (e % modulus).abs();
    F::from_str_vartime(&e.to_str_radix(10)[..]).unwrap()
}

/// Converts a prime field element into a big unsigned integer.
pub fn fe_to_big<F: PrimeField>(fe: F) -> BigUint {
    BigUint::from_bytes_le(fe.to_repr().as_ref())
}

/// Creates an [`Expression`] that queries the given cell relative to the
/// beginning of the cell's region.
#[macro_export]
macro_rules! cell_to_expr {
    ($x:expr, $F:ty) => {{
        let c = $x.cell();
        i32::try_from(c.row_offset)
            .map(midnight_proofs::poly::Rotation)
            .map(|r| c.column.query_cell::<$F>(r))
            .map_err($crate::error::Error::from)
    }};
}
