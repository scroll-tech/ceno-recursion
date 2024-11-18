mod fp;
mod fp2;

use std::{iter::{Product, Sum}, ops::{Add, Mul, Neg, Sub}};

use ceno_goldilocks::ExtensionField;
pub use fp::Scalar;
pub use fp2::ScalarExt2;
use ff::Field;
use rand::{CryptoRng, RngCore};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use zeroize::Zeroize;

/// Trait describing the field element
/// Wraps around Goldilocks field towers from ceno-goldilocks
/// See: https://github.com/scroll-tech/ceno-Goldilocks
pub trait SpartanExtensionField: 
  Sized 
  + ConstantTimeEq 
  + PartialEq 
  + From<u64>
  + ConditionallySelectable
  + Zeroize
  + Neg
  + Default
  + Add<Output = Self>
  + Sub<Output = Self>
  + Mul<Output = Self>
  + Sum
  + Product
  + From<Self::InnerType>
{
  /// Inner Goldilocks extension field
  type InnerType: ExtensionField + Field;

  /// Return inner Goldilocks field element
  fn inner(&self) -> &Self::InnerType;

  /// Sample field element
  fn random<Rng: RngCore + CryptoRng>(rng: &mut Rng) -> Self;

  /// Convert to field element from 32 bytes
  fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self>;

  /// Convert to 32 bytes from field element
  fn to_bytes(&self) -> [u8; 32];

  /// Convert to field element from 64 bytes
  fn from_bytes_wide(bytes: &[u8; 64]) -> Self;

  /// Doubles this field element.
  #[inline]
  fn double(&self) -> Self {
    self.add(*self)
  }

  /// Squares this element.
  #[inline]
  fn square(&self) -> Self {
    self.mul(*self)
  }

  /// Negates `self`.
  #[inline]
  fn neg(&self) -> Self {
    self.inner().neg().into()
  }

  /// Exponentiates `self` by `by`, where `by` is a
  /// little-endian order integer exponent.
  fn pow(&self, by: &[u64; 4]) -> Self {
    self.inner().pow(by).into()
  }

  /// Exponentiates `self` by `by`, where `by` is a
  /// little-endian order integer exponent.
  ///
  /// **This operation is variable time with respect
  /// to the exponent.** If the exponent is fixed,
  /// this operation is effectively constant time.
  fn pow_vartime(&self, by: &[u64; 4]) -> Self {
    self.inner().pow_vartime(by).into()
  }

  /// Computes the multiplicative inverse of this element,
  /// failing if the element is zero.
  fn invert(&self) -> CtOption<Self> {
    if self.inner().is_zero().into() {
      CtOption::new(Self::InnerType::ZERO.into(), Choice::from(0))
    } else {
      CtOption::new(self.inner().invert().unwrap().into(), Choice::from(1))
    }
  }

  /// Batch invert field elements
  fn batch_invert(inputs: &mut [Self]) -> Self {
    use zeroize::Zeroizing;

    let n = inputs.len();
    let one: Self = Self::InnerType::ONE.into();

    // Place scratch storage in a Zeroizing wrapper to wipe it when
    // we pass out of scope.
    let scratch_vec = vec![one; n];
    let mut scratch = Zeroizing::new(scratch_vec);

    // Keep an accumulator of all of the previous products
    let mut acc = Self::InnerType::ONE.into();

    // Pass through the input vector, recording the previous
    // products in the scratch space
    for (input, scratch) in inputs.iter().zip(scratch.iter_mut()) {
      *scratch = acc;

      acc = acc * *input;
    }

    // acc is nonzero iff all inputs are nonzero
    debug_assert!(acc != Self::InnerType::ZERO.into());

    // Compute the inverse of all products
    acc = acc.invert().unwrap();

    // We need to return the product of all inverses later
    let ret = acc;

    // Pass through the vector backwards to compute the inverses
    // in place
    for (input, scratch) in inputs.iter_mut().rev().zip(scratch.iter().rev()) {
      let tmp: Self = acc * input.clone();
      *input = acc * *scratch;
      acc = tmp;
    }

    ret
  }
}

/// Trait describing relationship between primitives and field elements
pub trait ScalarFromPrimitives {
  /// Used for converting internal types to base Goldilocks
  fn to_scalar(self) -> Scalar;
}

impl ScalarFromPrimitives for usize {
  #[inline]
  fn to_scalar(self) -> Scalar {
    (0..self).map(|_i| Scalar::one()).sum()
  }
}

impl<'a> From<&'a Scalar> for [u8; 32] {
  fn from(value: &'a Scalar) -> [u8; 32] {
    value.to_bytes()
  }
}

/// macro_rules! impl_add_binop_specify_output
#[macro_export]
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

/// macro_rules! impl_sub_binop_specify_output
#[macro_export]
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

/// impl_binops_additive_specify_output
#[macro_export]
macro_rules! impl_binops_additive_specify_output {
  ($lhs:ident, $rhs:ident, $output:ident) => {
    crate::impl_add_binop_specify_output!($lhs, $rhs, $output);
    crate::impl_sub_binop_specify_output!($lhs, $rhs, $output);
  };
}

/// impl_binops_multiplicative_mixed
#[macro_export]
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

/// macro_rules! impl_binops_additive
#[macro_export]
macro_rules! impl_binops_additive {
  ($lhs:ident, $rhs:ident) => {
    crate::impl_binops_additive_specify_output!($lhs, $rhs, $lhs);

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

/// macro_rules! impl_binops_multiplicative
#[macro_export]
macro_rules! impl_binops_multiplicative {
  ($lhs:ident, $rhs:ident) => {
    crate::impl_binops_multiplicative_mixed!($lhs, $rhs, $lhs);

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