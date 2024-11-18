use ceno_goldilocks::{Goldilocks, GoldilocksExt2, SmallField};
use core::borrow::Borrow;
use core::iter::{Product, Sum};
use ff::{Field, FromUniformBytes};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use rand::{CryptoRng, RngCore};
use serde::{Deserialize, Serialize};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use zeroize::Zeroize;

/// Constant representing the modulus
/// q = 2^64 - 2^32 + 1
/// 0xFFFFFFFF00000001
const MODULUS: Scalar = Scalar(Goldilocks(0xFFFF_FFFF_0000_0001));
const P: u64 = 0xFFFF_FFFF_0000_0001;
const INV: u64 = 0xFFFF_FFFE_FFFF_FFFF;

#[derive(Clone, Copy, Eq, Serialize, Deserialize, Hash, Debug)]
pub struct Scalar(Goldilocks);

impl From<Goldilocks> for Scalar {
  fn from(g: Goldilocks) -> Self {
      Self(g)
  }
}

impl Scalar {
  /// Convert a field elements to a u64.
  fn to_canonical_u64(&self) -> u64 {
    self.0.to_canonical_u64()
  }

  /// Returns zero, the additive identity.
  #[inline]
  pub const fn zero() -> Self {
    Self(Goldilocks(0u64))
  }

  /// Returns one, the multiplicative identity.
  #[inline]
  pub const fn one() -> Self {
    Self(Goldilocks(1u64))
  }

  pub fn random<Rng: RngCore + CryptoRng>(rng: &mut Rng) -> Self {
    let mut res = rng.next_u64();
    while res >= P {
        res = rng.next_u64();
    }
    Goldilocks(res).into()
  }

  /// Attempts to convert a little-endian byte representation of
  /// a scalar into a `Scalar`, failing if the input is not canonical.
  pub fn from_bytes(bytes: &[u8; 32]) -> CtOption<Scalar> {
    CtOption::new(Goldilocks::from_uniform_bytes(bytes).into(), Choice::from(1u8))
  }

  /// Converts an element of `Scalar` into a byte representation in
  /// little-endian byte order.
  pub fn to_bytes(&self) -> [u8; 32] {
    let mut res = [0; 32];
    res[..8].copy_from_slice(&self.0.0.to_le_bytes());
    res
  }

  /// Converts a 512-bit little endian integer into
  /// a `Scalar` by reducing by the modulus.
  pub fn from_bytes_wide(bytes: &[u8; 64]) -> Scalar {
    Goldilocks::from_uniform_bytes(bytes).into()
  }

  /// Adds `rhs` to `self`, returning the result.
  #[inline]
  pub fn add(&self, rhs: &Self) -> Self {
    self.0.add(rhs.0).into()
  }

  /// Subtracts `rhs` from `self`, returning the result.
  #[inline]
  pub fn sub(&self, rhs: &Self) -> Self {
    self.0.sub(rhs.0).into()
  }

  /// Doubles this field element.
  #[inline]
  pub fn double(&self) -> Scalar {
    self.add(self)
  }

  /// Multiplies `rhs` by `self`, returning the result.
  #[inline]
  pub fn mul(&self, rhs: &Self) -> Self {
    self.0.mul(rhs.0).into()
  }

  /// Squares this element.
  #[inline]
  pub fn square(&self) -> Scalar {
    self.mul(self)
  }

  /// Negates `self`.
  #[inline]
  pub fn neg(&self) -> Self {
    self.0.neg().into()
  }

  /// Exponentiates `self` by `by`, where `by` is a
  /// little-endian order integer exponent.
  pub fn pow(&self, by: &[u64; 4]) -> Self {
    self.0.pow(by).into()
  }

  /// Exponentiates `self` by `by`, where `by` is a
  /// little-endian order integer exponent.
  ///
  /// **This operation is variable time with respect
  /// to the exponent.** If the exponent is fixed,
  /// this operation is effectively constant time.
  pub fn pow_vartime(&self, by: &[u64; 4]) -> Self {
    self.0.pow_vartime(by).into()
  }

  /// Computes the multiplicative inverse of this element,
  /// failing if the element is zero.
  pub fn invert(&self) -> CtOption<Self> {
    if self.0.is_zero().into() {
      CtOption::new(Self::zero(), Choice::from(0))
    } else {
      CtOption::new(self.0.invert().unwrap().into(), Choice::from(1))
    }
  }
  
  pub fn batch_invert(inputs: &mut [Scalar]) -> Scalar {
    // This code is essentially identical to the FieldElement
    // implementation, and is documented there.  Unfortunately,
    // it's not easy to write it generically, since here we want
    // to use `UnpackedScalar`s internally, and `Scalar`s
    // externally, but there's no corresponding distinction for
    // field elements.

    use zeroize::Zeroizing;

    let n = inputs.len();
    let one = Scalar::one();

    // Place scratch storage in a Zeroizing wrapper to wipe it when
    // we pass out of scope.
    let scratch_vec = vec![one; n];
    let mut scratch = Zeroizing::new(scratch_vec);

    // Keep an accumulator of all of the previous products
    let mut acc = Scalar::one();

    // Pass through the input vector, recording the previous
    // products in the scratch space
    for (input, scratch) in inputs.iter().zip(scratch.iter_mut()) {
      *scratch = acc;

      acc = acc * input;
    }

    // acc is nonzero iff all inputs are nonzero
    debug_assert!(acc != Scalar::zero());

    // Compute the inverse of all products
    acc = acc.invert().unwrap();

    // We need to return the product of all inverses later
    let ret = acc;

    // Pass through the vector backwards to compute the inverses
    // in place
    for (input, scratch) in inputs.iter_mut().rev().zip(scratch.iter().rev()) {
      let tmp = &acc * input.clone();
      *input = &acc * scratch;
      acc = tmp;
    }

    ret
  }
}

impl From<u64> for Scalar {
  fn from(val: u64) -> Scalar {
    Goldilocks(val).into()
  }
}

impl ConstantTimeEq for Scalar {
  fn ct_eq(&self, other: &Self) -> Choice {
      self.to_canonical_u64().ct_eq(&other.to_canonical_u64())
  }
}

impl PartialEq for Scalar {
  fn eq(&self, other: &Scalar) -> bool {
      self.to_canonical_u64() == other.to_canonical_u64()
  }
}

impl ConditionallySelectable for Scalar {
  fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
      Self(Goldilocks(u64::conditional_select(&a.0.0, &b.0.0, choice)))
  }
}

impl<'a, 'b> Add<&'b Scalar> for &'a Scalar {
  type Output = Scalar;

  #[inline]
  fn add(self, rhs: &'b Scalar) -> Scalar {
    self.add(rhs)
  }
}

impl<'a, 'b> Sub<&'b Scalar> for &'a Scalar {
  type Output = Scalar;

  #[inline]
  fn sub(self, rhs: &'b Scalar) -> Scalar {
    self.sub(rhs)
  }
}

impl<'a, 'b> Mul<&'b Scalar> for &'a Scalar {
  type Output = Scalar;

  #[inline]
  fn mul(self, rhs: &'b Scalar) -> Scalar {
    self.mul(rhs)
  }
}

impl Default for Scalar {
  #[inline]
  fn default() -> Self {
    Self::zero()
  }
}

impl<T> Product<T> for Scalar
where
  T: Borrow<Scalar>,
{
  fn product<I>(iter: I) -> Self
  where
    I: Iterator<Item = T>,
  {
    iter.fold(Scalar::one(), |acc, item| acc * item.borrow())
  }
}

impl<T> Sum<T> for Scalar
where
  T: Borrow<Scalar>,
{
  fn sum<I>(iter: I) -> Self
  where
    I: Iterator<Item = T>,
  {
    iter.fold(Scalar::zero(), |acc, item| acc + item.borrow())
  }
}

impl Zeroize for Scalar {
  fn zeroize(&mut self) {
    self.0 = Goldilocks(0u64);
  }
}

impl<'a> From<&'a Scalar> for [u8; 32] {
  fn from(value: &'a Scalar) -> [u8; 32] {
    value.to_bytes()
  }
}

impl Neg for Scalar {
  type Output = Self;

  #[inline]
  fn neg(self) -> Self {
      self.0.neg().into()
  }
}

crate::impl_binops_additive!(Scalar, Scalar);
crate::impl_binops_multiplicative!(Scalar, Scalar);

