//! Structs for handling expressions.

mod aexpr;
mod bexpr;

use std::{
    iter::{Product, Sum},
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign},
};

pub use aexpr::*;
pub use bexpr::*;
use bit_set::BitSet;

/// Marker enum for different properties of expressions.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ExprProperty {
    /// Constant expression
    Const,
}

impl ExprProperty {
    const fn value(self) -> usize {
        match self {
            ExprProperty::Const => 0,
        }
    }
}

impl BitOr for ExprProperty {
    type Output = ExprProperties;

    fn bitor(self, rhs: Self) -> Self::Output {
        ExprProperties(BitSet::from_iter([self.value(), rhs.value()]))
    }
}

impl BitOr<ExprProperties> for ExprProperty {
    type Output = ExprProperties;

    fn bitor(self, mut rhs: ExprProperties) -> Self::Output {
        rhs.0.insert(self.value());
        rhs
    }
}

impl PartialEq<ExprProperties> for ExprProperty {
    fn eq(&self, other: &ExprProperties) -> bool {
        other.eq(self)
    }
}

/// Set of properties for expressions.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct ExprProperties(BitSet);

impl ExprProperties {
    /// Creates a new property set.
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a new property set with only one property.
    pub fn with(prop: ExprProperty) -> Self {
        Self(BitSet::from_iter([prop.value()]))
    }

    fn full() -> Self {
        Self(BitSet::from_bytes(&std::usize::MAX.to_be_bytes()))
    }
}

impl From<ExprProperty> for ExprProperties {
    fn from(value: ExprProperty) -> Self {
        Self::with(value)
    }
}

impl BitOr for ExprProperties {
    type Output = Self;

    fn bitor(mut self, rhs: Self) -> Self::Output {
        self |= rhs;
        self
    }
}

impl BitAnd for ExprProperties {
    type Output = Self;

    fn bitand(mut self, rhs: Self) -> Self::Output {
        self &= rhs;
        self
    }
}

impl BitOr<ExprProperty> for ExprProperties {
    type Output = Self;

    fn bitor(mut self, rhs: ExprProperty) -> Self::Output {
        self |= rhs;
        self
    }
}
impl BitAnd<ExprProperty> for ExprProperties {
    type Output = Self;

    fn bitand(mut self, rhs: ExprProperty) -> Self::Output {
        self &= rhs;
        self
    }
}

impl BitOrAssign for ExprProperties {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0.union_with(&rhs.0)
    }
}

impl BitAndAssign for ExprProperties {
    fn bitand_assign(&mut self, rhs: Self) {
        self.0.intersect_with(&rhs.0)
    }
}

impl BitOrAssign<ExprProperty> for ExprProperties {
    fn bitor_assign(&mut self, rhs: ExprProperty) {
        self.0.insert(rhs.value());
    }
}

impl BitAndAssign<ExprProperty> for ExprProperties {
    fn bitand_assign(&mut self, rhs: ExprProperty) {
        self.0
            .intersect_with(&BitSet::from_bytes(&rhs.value().to_le_bytes()));
    }
}

impl PartialEq<ExprProperty> for ExprProperties {
    fn eq(&self, other: &ExprProperty) -> bool {
        self.0.contains(other.value())
    }
}

impl Sum for ExprProperties {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Default::default(), |acc, e| acc | e)
    }
}

impl Sum<ExprProperty> for ExprProperties {
    fn sum<I: Iterator<Item = ExprProperty>>(iter: I) -> Self {
        iter.fold(Default::default(), |acc, e| acc | e)
    }
}

impl Product for ExprProperties {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::full(), |acc, e| acc & e)
    }
}

impl Product<ExprProperty> for ExprProperties {
    fn product<I: Iterator<Item = ExprProperty>>(iter: I) -> Self {
        iter.fold(Self::full(), |acc, e| acc & e)
    }
}
