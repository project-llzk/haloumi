//! Felt type.

use ff::PrimeField;
use internment::Intern;
use num_bigint::BigUint;
use std::ops::{Add, AddAssign, Deref, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign};

/// Interned value of the prime of a finite field.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Prime(Intern<BigUint>);

impl Prime {
    /// Creates the prime from the given [`PrimeField`].
    fn new<F: PrimeField>() -> Self {
        let f = -F::ONE;
        Self(Intern::new(
            BigUint::from_bytes_le(f.to_repr().as_ref()) + 1usize,
        ))
    }

    fn value(&self) -> &BigUint {
        self.0.as_ref()
    }
}

/// Lightweight representation of a constant value.
///
/// The actual value is interned which allows this type to be [`Copy`] and
/// avoids duplication of commonly used values.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Felt {
    value: Intern<BigUint>,
    prime: Prime,
}

impl Felt {
    /// Creates a new felt from an implementation of [`PrimeField`].
    pub fn new<F: PrimeField>(f: F) -> Self {
        Self {
            value: Intern::new(BigUint::from_bytes_le(f.to_repr().as_ref())),
            prime: Prime::new::<F>(),
        }
    }

    /// Returns the value of the field prime.
    pub fn prime(&self) -> Prime {
        self.prime
    }

    /// Creates a felt from anything that can become a [`BigUint`].
    ///
    /// Use this method only during testing.
    #[cfg(test)]
    pub fn new_from<F: PrimeField>(i: impl Into<BigUint>) -> Self {
        Self {
            value: Intern::new(i.into()),
            prime: Prime::new::<F>(),
        }
    }

    fn replace(self, value: BigUint) -> Self {
        Self {
            value: Intern::new(value % self.prime.value()),
            prime: self.prime,
        }
    }
}

impl std::fmt::Debug for Felt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.as_ref())
    }
}

impl<T> PartialEq<T> for Felt
where
    T: Into<BigUint> + Copy,
{
    fn eq(&self, other: &T) -> bool {
        let other: BigUint = (*other).into() % self.prime.value();
        self.as_ref().eq(&other)
    }
}

impl AsRef<BigUint> for Felt {
    fn as_ref(&self) -> &BigUint {
        self.value.as_ref()
    }
}

impl Deref for Felt {
    type Target = BigUint;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl Rem for Felt {
    type Output = Self;

    /// # Panics
    ///
    /// If the primes are different.
    fn rem(self, rhs: Self) -> Self::Output {
        assert_eq!(self.prime, rhs.prime);
        if self < rhs {
            return self;
        }
        self.replace(self.as_ref() % rhs.as_ref())
    }
}

impl RemAssign for Felt {
    /// # Panics
    ///
    /// If the primes are different.
    fn rem_assign(&mut self, rhs: Self) {
        *self = *self % rhs;
    }
}

impl Sub for Felt {
    type Output = Self;

    /// # Panics
    ///
    /// If the primes are different.
    fn sub(self, rhs: Self) -> Self::Output {
        assert_eq!(self.prime, rhs.prime);
        if self < rhs {
            let diff = rhs.as_ref() - self.as_ref();
            return self.replace(self.prime.value() - diff);
        }

        self.replace(self.as_ref() - rhs.as_ref())
    }
}

impl SubAssign for Felt {
    /// # Panics
    ///
    /// If the primes are different.
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Add for Felt {
    type Output = Felt;

    /// # Panics
    ///
    /// If the primes are different.
    fn add(self, rhs: Self) -> Self::Output {
        assert_eq!(self.prime, rhs.prime);
        self.replace(self.as_ref() + rhs.as_ref())
    }
}

impl AddAssign for Felt {
    /// # Panics
    ///
    /// If the primes are different.
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Mul for Felt {
    type Output = Felt;

    /// # Panics
    ///
    /// If the primes are different.
    fn mul(self, rhs: Self) -> Self::Output {
        assert_eq!(self.prime, rhs.prime);
        self.replace(self.as_ref() * rhs.as_ref())
    }
}

impl MulAssign for Felt {
    /// # Panics
    ///
    /// If the primes are different.
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl std::fmt::Display for Felt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_ref())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use ff::PrimeField;
    use halo2curves::bn256::Fq;
    use num_bigint::BigInt;
    use quickcheck_macros::quickcheck;

    /// Implementation of BabyBear used for testing the [`Felt`](super::Felt) type.
    #[derive(Hash, PrimeField)]
    #[PrimeFieldModulus = "2013265921"]
    #[PrimeFieldGenerator = "31"]
    #[PrimeFieldReprEndianness = "little"]
    pub struct BabyBear([u64; 1]);
    const BABYBEAR: u32 = 2013265921;

    #[quickcheck]
    fn partial_eq_for_other_types(x: u32) {
        let v: u32 = x % BABYBEAR;
        let v_f = Felt::new(BabyBear::from(x as u64));
        if x < BABYBEAR {
            assert_eq!(v, x);
        } else {
            assert_ne!(v, x);
        }
        assert_eq!(v_f, x);
    }

    #[quickcheck]
    fn mul(x: u32, y: u32) {
        let r = Felt::new(BabyBear::from(x as u64)) * Felt::new(BabyBear::from(y as u64));
        let e = (BigUint::from(x) * BigUint::from(y)) % BigUint::from(BABYBEAR);

        assert_eq!(r.as_ref(), &e);
    }

    #[quickcheck]
    fn sum(x: u32, y: u32) {
        let r = Felt::new(BabyBear::from(x as u64)) + Felt::new(BabyBear::from(y as u64));
        let e = (BigUint::from(x) + BigUint::from(y)) % BigUint::from(BABYBEAR);

        assert_eq!(r.as_ref(), &e);
    }

    #[quickcheck]
    fn sub(x: u32, y: u32) {
        let r = Felt::new(BabyBear::from(x as u64)) - Felt::new(BabyBear::from(y as u64));
        let e;
        if x >= y {
            e = (BigUint::from(x) - BigUint::from(y)) % BigUint::from(BABYBEAR);
        } else {
            let b = BigInt::from(BABYBEAR);
            let mut i = BigInt::from(x) - BigInt::from(y);
            while i.sign() == num_bigint::Sign::Minus {
                i += &b;
            }
            e = i.try_into().unwrap();
        }

        assert_eq!(r.as_ref(), &e);
    }

    #[quickcheck]
    fn same_prime_eq(i: u64) {
        let x = Felt::new(BabyBear::from(i));
        let y = Felt::new(BabyBear::from(i));
        assert_eq!(x, y);
    }

    #[quickcheck]
    fn different_primes_eq(i: u64) {
        let x = Felt::new(BabyBear::from(i));
        let y = Felt::new(Fq::from(i));
        assert_ne!(x, y);
    }

    #[quickcheck]
    #[should_panic]
    fn different_primes_sum(a: u64, b: u64) {
        let a = Felt::new(BabyBear::from(a));
        let b = Felt::new(Fq::from(b));
        let _ = a + b;
    }

    #[quickcheck]
    #[should_panic]
    fn different_primes_sum_assign(a: u64, b: u64) {
        let mut a = Felt::new(BabyBear::from(a));
        let b = Felt::new(Fq::from(b));
        a += b;
    }

    #[quickcheck]
    #[should_panic]
    fn different_primes_mul(a: u64, b: u64) {
        let a = Felt::new(BabyBear::from(a));
        let b = Felt::new(Fq::from(b));
        let _ = a * b;
    }

    #[quickcheck]
    #[should_panic]
    fn different_primes_mul_assign(a: u64, b: u64) {
        let mut a = Felt::new(BabyBear::from(a));
        let b = Felt::new(Fq::from(b));
        a *= b;
    }

    #[quickcheck]
    #[should_panic]
    fn different_primes_sub(a: u64, b: u64) {
        let a = Felt::new(BabyBear::from(a));
        let b = Felt::new(Fq::from(b));
        let _ = a - b;
    }

    #[quickcheck]
    #[should_panic]
    fn different_primes_sub_assign(a: u64, b: u64) {
        let mut a = Felt::new(BabyBear::from(a));
        let b = Felt::new(Fq::from(b));
        a -= b;
    }

    #[quickcheck]
    #[should_panic]
    fn different_primes_rem(a: u64, b: u64) {
        let a = Felt::new(BabyBear::from(a));
        let b = Felt::new(Fq::from(b));
        let _ = a % b;
    }

    #[quickcheck]
    #[should_panic]
    fn different_primes_rem_assign(a: u64, b: u64) {
        let mut a = Felt::new(BabyBear::from(a));
        let b = Felt::new(Fq::from(b));
        a %= b;
    }
}
