use super::SpartanExtensionField;
use crate::{ProofTranscript, Transcript};
use core::borrow::Borrow;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use ff::{Field, FromUniformBytes};
use goldilocks::Goldilocks;
use rand::{CryptoRng, RngCore};
use serde::{Deserialize, Serialize};
use std::ops::Neg;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use zeroize::Zeroize;

/// Field wrapper around base Goldilocks
#[derive(Clone, Copy, Eq, Serialize, Deserialize, Hash, Debug)]
pub struct Scalar(Goldilocks);

impl SpartanExtensionField for Scalar {
  type InnerType = Goldilocks;

  fn inner(&self) -> &Goldilocks {
    &self.0
  }

  fn field_zero() -> Self {
    Goldilocks::ZERO.into()
  }

  fn field_one() -> Self {
    Goldilocks::ONE.into()
  }

  fn random<Rng: RngCore + CryptoRng>(rng: &mut Rng) -> Self {
    Goldilocks::random(rng).into()
  }

  /// Attempts to convert a little-endian byte representation of
  /// a scalar into a `Scalar`, failing if the input is not canonical.
  fn from_bytes(bytes: &[u8; 32]) -> CtOption<Scalar> {
    CtOption::new(
      Goldilocks::from_uniform_bytes(bytes).into(),
      Choice::from(1u8),
    )
  }

  /// Converts an element of `Scalar` into a byte representation in
  /// little-endian byte order.
  fn to_bytes(&self) -> [u8; 32] {
    let mut res = [0; 32];
    res[..8].copy_from_slice(&self.0 .0.to_le_bytes());
    res
  }

  /// Converts a 512-bit little endian integer into
  /// a `Scalar` by reducing by the modulus.
  fn from_bytes_wide(bytes: &[u8; 64]) -> Scalar {
    Goldilocks::from_uniform_bytes(bytes).into()
  }

  /// Append Goldilocks scalar to transcript
  fn append_field_to_transcript(label: &'static [u8], transcript: &mut Transcript, input: Self) {
    transcript.append_scalar(label, &input);
  }

  /// Append a vector Goldilocks scalars to transcript
  fn append_field_vector_to_transcript(
    label: &'static [u8],
    transcript: &mut Transcript,
    input: &[Self],
  ) {
    transcript.append_message(label, b"begin_append_vector");
    for item in input {
      transcript.append_scalar(label, item);
    }
    transcript.append_message(label, b"end_append_vector");
  }
}

impl ConstantTimeEq for Scalar {
  fn ct_eq(&self, other: &Self) -> Choice {
    self.inner().ct_eq(other.inner())
  }
}
impl PartialEq for Scalar {
  fn eq(&self, other: &Self) -> bool {
    *self.inner() == *other.inner()
  }
}
impl From<u64> for Scalar {
  fn from(val: u64) -> Scalar {
    Goldilocks(val).into()
  }
}
impl From<usize> for Scalar {
  fn from(val: usize) -> Scalar {
    Goldilocks(val as u64).into()
  }
}
impl ConditionallySelectable for Scalar {
  fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
    Self(Goldilocks(u64::conditional_select(
      &a.0 .0, &b.0 .0, choice,
    )))
  }
}
impl Zeroize for Scalar {
  fn zeroize(&mut self) {
    self.0 = Goldilocks(0u64);
  }
}
impl Neg for Scalar {
  type Output = Scalar;

  fn neg(self) -> Scalar {
    self.0.neg().into()
  }
}
impl Default for Scalar {
  fn default() -> Self {
    Self::zero()
  }
}
impl From<Goldilocks> for Scalar {
  fn from(g: Goldilocks) -> Self {
    Self(g)
  }
}
impl Scalar {
  /// Returns zero, the additive identity.
  pub const fn zero() -> Self {
    Self(Goldilocks(0u64))
  }

  /// Returns one, the multiplicative identity.
  pub const fn one() -> Self {
    Self(Goldilocks(1u64))
  }
}

impl<'a, 'b> Add<&'b Scalar> for &'a Scalar {
  type Output = Scalar;

  fn add(self, rhs: &'b Scalar) -> Scalar {
    self.inner().add(rhs.inner()).into()
  }
}

impl<'a, 'b> Sub<&'b Scalar> for &'a Scalar {
  type Output = Scalar;

  fn sub(self, rhs: &'b Scalar) -> Scalar {
    self.inner().sub(rhs.inner()).into()
  }
}

impl<'a, 'b> Mul<&'b Scalar> for &'a Scalar {
  type Output = Scalar;

  fn mul(self, rhs: &'b Scalar) -> Scalar {
    self.inner().mul(rhs.inner()).into()
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

crate::impl_binops_additive!(Scalar, Scalar);
crate::impl_binops_multiplicative!(Scalar, Scalar);
