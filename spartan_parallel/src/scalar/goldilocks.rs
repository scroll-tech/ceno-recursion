//! This module provides an implementation of the Goldilocks scalar field
//! where `q = 2^64 - 2^32 + 1 = 0xFFFFFFFF00000001`
use core::borrow::Borrow;
use core::convert::TryFrom;
use core::fmt;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use rand::{CryptoRng, RngCore};
use serde::{Deserialize, Serialize};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use zeroize::Zeroize;

macro_rules! impl_add_binop_specify_output {
  ($lhs:ident, $rhs:ident, $output:ident) => {
    impl<'b> Add<&'b $rhs> for $lhs {
      type Output = $output;

      #[inline]
      fn add(self, rhs: &'b $rhs) -> $output {
        &self + rhs
      }
    }

    impl<'a> Add<$rhs> for &'a $lhs {
      type Output = $output;

      #[inline]
      fn add(self, rhs: $rhs) -> $output {
        self + &rhs
      }
    }

    impl Add<$rhs> for $lhs {
      type Output = $output;

      #[inline]
      fn add(self, rhs: $rhs) -> $output {
        &self + &rhs
      }
    }
  };
}

macro_rules! impl_sub_binop_specify_output {
  ($lhs:ident, $rhs:ident, $output:ident) => {
    impl<'b> Sub<&'b $rhs> for $lhs {
      type Output = $output;

      #[inline]
      fn sub(self, rhs: &'b $rhs) -> $output {
        &self - rhs
      }
    }

    impl<'a> Sub<$rhs> for &'a $lhs {
      type Output = $output;

      #[inline]
      fn sub(self, rhs: $rhs) -> $output {
        self - &rhs
      }
    }

    impl Sub<$rhs> for $lhs {
      type Output = $output;

      #[inline]
      fn sub(self, rhs: $rhs) -> $output {
        &self - &rhs
      }
    }
  };
}

macro_rules! impl_binops_additive_specify_output {
  ($lhs:ident, $rhs:ident, $output:ident) => {
    impl_add_binop_specify_output!($lhs, $rhs, $output);
    impl_sub_binop_specify_output!($lhs, $rhs, $output);
  };
}

macro_rules! impl_binops_multiplicative_mixed {
  ($lhs:ident, $rhs:ident, $output:ident) => {
    impl<'b> Mul<&'b $rhs> for $lhs {
      type Output = $output;

      #[inline]
      fn mul(self, rhs: &'b $rhs) -> $output {
        &self * rhs
      }
    }

    impl<'a> Mul<$rhs> for &'a $lhs {
      type Output = $output;

      #[inline]
      fn mul(self, rhs: $rhs) -> $output {
        self * &rhs
      }
    }

    impl Mul<$rhs> for $lhs {
      type Output = $output;

      #[inline]
      fn mul(self, rhs: $rhs) -> $output {
        &self * &rhs
      }
    }
  };
}

macro_rules! impl_binops_additive {
  ($lhs:ident, $rhs:ident) => {
    impl_binops_additive_specify_output!($lhs, $rhs, $lhs);

    impl SubAssign<$rhs> for $lhs {
      #[inline]
      fn sub_assign(&mut self, rhs: $rhs) {
        *self = &*self - &rhs;
      }
    }

    impl AddAssign<$rhs> for $lhs {
      #[inline]
      fn add_assign(&mut self, rhs: $rhs) {
        *self = &*self + &rhs;
      }
    }

    impl<'b> SubAssign<&'b $rhs> for $lhs {
      #[inline]
      fn sub_assign(&mut self, rhs: &'b $rhs) {
        *self = &*self - rhs;
      }
    }

    impl<'b> AddAssign<&'b $rhs> for $lhs {
      #[inline]
      fn add_assign(&mut self, rhs: &'b $rhs) {
        *self = &*self + rhs;
      }
    }
  };
}

macro_rules! impl_binops_multiplicative {
  ($lhs:ident, $rhs:ident) => {
    impl_binops_multiplicative_mixed!($lhs, $rhs, $lhs);

    impl MulAssign<$rhs> for $lhs {
      #[inline]
      fn mul_assign(&mut self, rhs: $rhs) {
        *self = &*self * &rhs;
      }
    }

    impl<'b> MulAssign<&'b $rhs> for $lhs {
      #[inline]
      fn mul_assign(&mut self, rhs: &'b $rhs) {
        *self = &*self * rhs;
      }
    }
  };
}

/// Represents an element of the Goldilocks field
// The internal representation of this type is a singular u64.
#[derive(Clone, Copy, Eq, Serialize, Deserialize, Hash, Debug)]
pub struct Scalar(pub u64);

impl From<u64> for Scalar {
  fn from(val: u64) -> Scalar {
    Scalar(val)
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
      Self(u64::conditional_select(&a.0, &b.0, choice))
  }
}

/// Constant representing the modulus
/// q = 2^64 - 2^32 + 1
/// 0xFFFFFFFF00000001
const MODULUS: Scalar = Scalar(0xFFFF_FFFF_0000_0001);
const P: u64 = 0xFFFF_FFFF_0000_0001;
const INV: u64 = 0xFFFF_FFFE_FFFF_FFFF;

/// Compute the inverse of 2^exp in this field.
#[inline]
fn inverse_2exp(exp: usize) -> u64 {
    // Let p = char(F). Since 2^exp is in the prime subfield, i.e. an
    // element of GF_p, its inverse must be as well. Thus we may add
    // multiples of p without changing the result. In particular,
    // 2^-exp = 2^-exp - p 2^-exp
    //        = 2^-exp (1 - p)
    //        = p - (p - 1) / 2^exp

    // If this field's two adicity, t, is at least exp, then 2^exp divides
    // p - 1, so this division can be done with a simple bit shift. If
    // exp > t, we repeatedly multiply by 2^-t and reduce exp until it's in
    // the right range.

    // NB: The only reason this is split into two cases is to save
    // the multiplication (and possible calculation of
    // inverse_2_pow_adicity) in the usual case that exp <=
    // TWO_ADICITY. Can remove the branch and simplify if that
    // saving isn't worth it.
    let res = if exp > 32 {
        // NB: This should be a compile-time constant
        // MODULUS - ((MODULUS - 1) >> 32)
        let inverse_2_pow_adicity = Scalar(0xfffffffe00000002);

        let mut res = inverse_2_pow_adicity;
        let mut e = exp - 32;

        while e > 32 {
            res *= inverse_2_pow_adicity;
            e -= 32;
        }
        res * Scalar(P - ((P - 1) >> e))
    } else {
        Scalar(P - ((P - 1) >> exp))
    };
    res.0
}

/// This is a 'safe' iteration for the modular inversion algorithm. It
/// is safe in the sense that it will produce the right answer even
/// when f + g >= 2^64.
#[inline(always)]
fn safe_iteration(f: &mut u64, g: &mut u64, c: &mut i128, d: &mut i128, k: &mut u32) {
    if f < g {
        std::mem::swap(f, g);
        std::mem::swap(c, d);
    }
    if *f & 3 == *g & 3 {
        // f - g = 0 (mod 4)
        *f -= *g;
        *c -= *d;

        // kk >= 2 because f is now 0 (mod 4).
        let kk = f.trailing_zeros();
        *f >>= kk;
        *d <<= kk;
        *k += kk;
    } else {
        // f + g = 0 (mod 4)
        *f = (*f >> 2) + (*g >> 2) + 1u64;
        *c += *d;
        let kk = f.trailing_zeros();
        *f >>= kk;
        *d <<= kk + 2;
        *k += kk + 2;
    }
}

/// This is an 'unsafe' iteration for the modular inversion
/// algorithm. It is unsafe in the sense that it might produce the
/// wrong answer if f + g >= 2^64.
#[inline(always)]
unsafe fn unsafe_iteration(f: &mut u64, g: &mut u64, c: &mut i128, d: &mut i128, k: &mut u32) {
    if *f < *g {
        std::mem::swap(f, g);
        std::mem::swap(c, d);
    }
    if *f & 3 == *g & 3 {
        // f - g = 0 (mod 4)
        *f -= *g;
        *c -= *d;
    } else {
        // f + g = 0 (mod 4)
        *f += *g;
        *c += *d;
    }

    // kk >= 2 because f is now 0 (mod 4).
    let kk = f.trailing_zeros();
    *f >>= kk;
    *d <<= kk;
    *k += kk;
}

/// Try to invert an element in a prime field.
/// See Handbook of Elliptic and Hyperelliptic Cryptography, Algorithms 11.6 and 11.12.
#[allow(clippy::many_single_char_names)]
pub(crate) fn try_inverse_u64(x: &u64) -> Option<u64> {
    let mut f = *x;
    let mut g = P;
    // NB: These two are very rarely such that their absolute
    // value exceeds (p-1)/2; we are paying the price of i128 for
    // the whole calculation, just for the times they do
    // though. Measurements suggest a further 10% time saving if c
    // and d could be replaced with i64's.
    let mut c = 1i128;
    let mut d = 0i128;

    if f == 0 {
        return None;
    }

    // f and g must always be odd.
    let mut k = f.trailing_zeros();
    f >>= k;
    if f == 1 {
        return Some(inverse_2exp(k as usize));
    }

    // The first two iterations are unrolled. This is to handle
    // the case where f and g are both large and f+g can
    // overflow. log2(max{f,g}) goes down by at least one each
    // iteration though, so after two iterations we can be sure
    // that f+g won't overflow.

    // Iteration 1:
    safe_iteration(&mut f, &mut g, &mut c, &mut d, &mut k);

    if f == 1 {
        // c must be -1 or 1 here.
        if c == -1 {
            return Some(P - inverse_2exp(k as usize));
        }
        debug_assert!(c == 1, "bug in try_inverse_u64");
        return Some(inverse_2exp(k as usize));
    }

    // Iteration 2:
    safe_iteration(&mut f, &mut g, &mut c, &mut d, &mut k);

    // Remaining iterations:
    while f != 1 {
        unsafe {
            unsafe_iteration(&mut f, &mut g, &mut c, &mut d, &mut k);
        }
    }

    // The following two loops adjust c so it's in the canonical range
    // [0, F::ORDER).

    // The maximum number of iterations observed here is 2; should
    // prove this.
    while c < 0 {
        c += P as i128;
    }

    // The maximum number of iterations observed here is 1; should
    // prove this.
    while c >= P as i128 {
        c -= P as i128;
    }

    // Precomputing the binary inverses rather than using inverse_2exp
    // saves ~5ns on my machine.
    let res = Scalar(c as u64) * Scalar(inverse_2exp(k as usize));
    debug_assert!(
        Scalar(*x) * res == Scalar::one(),
        "bug in try_inverse_u64"
    );
    Some(res.0)
}

impl Neg for Scalar {
  type Output = Self;

  #[inline]
  fn neg(self) -> Self {
      if self.0 == 0 {
          self
      } else {
          Self(P - self.to_canonical_u64())
      }
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

impl_binops_additive!(Scalar, Scalar);
impl_binops_multiplicative!(Scalar, Scalar);

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
    self.0 = 0u64;
  }
}

impl Scalar {
  /// Convert a field elements to a u64.
  fn to_canonical_u64(&self) -> u64 {
    let mut c = self.0;
    if c >= P {
        c -= P;
    }
    c
  }

  /// Returns zero, the additive identity.
  #[inline]
  pub const fn zero() -> Scalar {
    Scalar(0u64)
  }

  /// Returns one, the multiplicative identity.
  #[inline]
  pub const fn one() -> Scalar {
    Scalar(1u64)
  }

  pub fn random<Rng: RngCore + CryptoRng>(rng: &mut Rng) -> Self {
    Scalar(rng.next_u64())
  }

  /// Attempts to convert a little-endian byte representation of
  /// a scalar into a `Scalar`, failing if the input is not canonical.
  pub fn from_bytes(bytes: &[u8; 32]) -> CtOption<Scalar> {
    let mut res: u128 = 0;

    for &byte in bytes.iter().rev() {
        res = (res << 8) | (byte as u128);
        res %= P as u128;
    }

    CtOption::new(Scalar(res as u64), Choice::from(1u8))
  }

  /// Converts an element of `Scalar` into a byte representation in
  /// little-endian byte order.
  pub fn to_bytes(&self) -> [u8; 32] {
    let mut res = [0; 32];
    res[..8].copy_from_slice(&self.0.to_le_bytes());
    res
  }

  /// Converts a 512-bit little endian integer into
  /// a `Scalar` by reducing by the modulus.
  pub fn from_bytes_wide(bytes: &[u8; 64]) -> Scalar {
    let mut res: u128 = 0;

    for &byte in bytes.iter().rev() {
        res = (res << 8) | (byte as u128);
        res %= P as u128;
    }

    Scalar(res as u64)
  }

  /// Adds `rhs` to `self`, returning the result.
  #[inline]
  pub const fn add(&self, rhs: &Self) -> Self {
    Scalar((((self.0 as u128) + (rhs.0 as u128)) % (P as u128)) as u64)
  }

  /// Subtracts `rhs` from `self`, returning the result.
  #[inline]
  pub const fn sub(&self, rhs: &Self) -> Self {
    Scalar((((self.0 as u128) + (u64::MAX as u128) - (rhs.0 as u128)) % (P as u128)) as u64)
  }

  /// Doubles this field element.
  #[inline]
  pub const fn double(&self) -> Scalar {
    self.add(self)
  }

  /// Multiplies `rhs` by `self`, returning the result.
  #[inline]
  pub const fn mul(&self, rhs: &Self) -> Self {
    Scalar((((self.0 as u128) * (rhs.0 as u128)) % (P as u128)) as u64)
  }

  /// Squares this element.
  #[inline]
  pub const fn square(&self) -> Scalar {
    self.mul(self)
  }

  /// Negates `self`.
  #[inline]
  pub const fn neg(&self) -> Self {
    Scalar((((P as u128) + (u64::MAX as u128) - (self.0 as u128)) % (P as u128)) as u64)
  }

  /// Exponentiates `self` by `by`, where `by` is a
  /// little-endian order integer exponent.
  pub fn pow(&self, by: &[u64; 4]) -> Self {
    let mut res = Self::one();
    for e in by.iter().rev() {
      for i in (0..64).rev() {
        res = res.square();
        let mut tmp = res;
        tmp *= self;
        res.conditional_assign(&tmp, (((*e >> i) & 0x1) as u8).into());
      }
    }
    res
  }

  /// Exponentiates `self` by `by`, where `by` is a
  /// little-endian order integer exponent.
  ///
  /// **This operation is variable time with respect
  /// to the exponent.** If the exponent is fixed,
  /// this operation is effectively constant time.
  pub fn pow_vartime(&self, by: &[u64; 4]) -> Self {
    let mut res = Self::one();
    for e in by.iter().rev() {
      for i in (0..64).rev() {
        res = res.square();

        if ((*e >> i) & 1) == 1 {
          res.mul_assign(self);
        }
      }
    }
    res
  }

  /// Computes the multiplicative inverse of this element,
  /// failing if the element is zero.
  pub fn invert(&self) -> CtOption<Self> {
    match try_inverse_u64(&self.0) {
        Some(p) => CtOption::new(Self(p), Choice::from(1)),
        None => CtOption::new(Self(0), Choice::from(0)),
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

impl<'a> From<&'a Scalar> for [u8; 32] {
  fn from(value: &'a Scalar) -> [u8; 32] {
    value.to_bytes()
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_inv() {
    // Compute -(q^{-1} mod 2^64) mod 2^64 by exponentiating
    // by totient(2**64) - 1

    let mut inv = 1u64;
    for _ in 0..63 {
      inv = inv.wrapping_mul(inv);
      inv = inv.wrapping_mul(P);
    }
    inv = inv.wrapping_neg();

    assert_eq!(inv, INV);
  }

  #[test]
  fn test_from_bytes() {
    assert_eq!(
      Scalar::from_bytes(&[
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0
      ])
      .unwrap(),
      Scalar::zero()
    );

    assert_eq!(
      Scalar::from_bytes(&[
        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0
      ])
      .unwrap(),
      Scalar::one()
    );

    assert_eq!(
      Scalar::from_bytes(&[
        0x01, 0x0f, 0x9c, 0x44, 0xe3, 0x11, 0x06, 0xa4, 
        0x47, 0x93, 0x85, 0x68, 0xa7, 0x1b, 0x0e, 0xd0, 
        0x65, 0xbe, 0xf5, 0x17, 0xd2, 0x73, 0xec, 0xce, 
        0x3d, 0x9a, 0x30, 0x7c, 0x1b, 0x41, 0x99, 0x03
      ])
      .unwrap(),
      Scalar(2973136677702561314)
    );

    assert_eq!(
      Scalar::from_bytes_wide(&[
        0x01, 0x0f, 0x9c, 0x44, 0xe3, 0x11, 0x06, 0xa4, 
        0x47, 0xa3, 0x0a, 0x56, 0x56, 0xe6, 0xc6, 0x6a, 
        0x05, 0xd7, 0xd3, 0x2d, 0x9a, 0x65, 0xa5, 0xbf, 
        0x00, 0xe3, 0x78, 0x38, 0x3d, 0xb7, 0x20, 0xb7, 
        0xea, 0xfd, 0x26, 0x1f, 0xf7, 0x8f, 0x45, 0x01, 
        0x8b, 0x30, 0xb9, 0x6f, 0xe2, 0x25, 0x23, 0x13, 
        0x0b, 0x14, 0x01, 0x1e, 0x33, 0x5c, 0x64, 0x2d, 
        0x7f, 0xfa, 0xac, 0xb3, 0xa2, 0x8f, 0x4f, 0x00,
      ]),
      Scalar(4689423654514323432)
    );
  }
}