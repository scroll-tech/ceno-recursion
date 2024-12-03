use super::SpartanExtensionField;
use crate::{AppendToTranscript, ProofTranscript, Transcript};
use core::borrow::Borrow;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use ff::{Field, FromUniformBytes};
use goldilocks::{ExtensionField, Goldilocks, GoldilocksExt2};
use rand::{CryptoRng, RngCore};
use serde::{Deserialize, Serialize};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use zeroize::Zeroize;

/// Field wrapper around ext2 Goldilocks
#[derive(Clone, Copy, Eq, Serialize, Deserialize, Hash, Debug)]
pub struct ScalarExt2(GoldilocksExt2);

impl From<GoldilocksExt2> for ScalarExt2 {
  fn from(g: GoldilocksExt2) -> Self {
    Self(g)
  }
}

impl Mul<Goldilocks> for ScalarExt2 {
  type Output = ScalarExt2;

  #[inline]
  fn mul(self, rhs: Goldilocks) -> Self::Output {
    (self.inner() * &rhs).into()
  }
}
impl<'a> Mul<&'a Goldilocks> for ScalarExt2 {
  type Output = Self;

  #[inline]
  fn mul(mut self, rhs: &'a Goldilocks) -> Self::Output {
    self *= rhs;
    self
  }
}
impl MulAssign<&Goldilocks> for ScalarExt2 {
  #[inline]
  fn mul_assign(&mut self, rhs: &Goldilocks) {
    self.0 *= rhs;
  }
}
impl MulAssign<Goldilocks> for ScalarExt2 {
  #[inline]
  fn mul_assign(&mut self, rhs: Goldilocks) {
    self.mul_assign(&rhs)
  }
}
impl SpartanExtensionField for ScalarExt2 {
  type InnerType = GoldilocksExt2;
  type BaseField = Goldilocks;

  fn inner(&self) -> &GoldilocksExt2 {
    &self.0
  }

  fn field_zero() -> Self {
    GoldilocksExt2::ZERO.into()
  }

  fn field_one() -> Self {
    GoldilocksExt2::ONE.into()
  }

  /// Build a self from a base element; pad ext with 0s.
  fn from_base(b: &Self::BaseField) -> Self {
    GoldilocksExt2::from_base(b).into()
  }

  fn random<Rng: RngCore + CryptoRng>(rng: &mut Rng) -> Self {
    GoldilocksExt2::random(rng).into()
  }

  /// Attempts to convert a little-endian byte representation of
  /// a scalar into a `ScalarExt2`, failing if the input is not canonical.
  fn from_bytes(bytes: &[u8; 32]) -> CtOption<ScalarExt2> {
    CtOption::new(
      GoldilocksExt2::from_base(&Goldilocks::from_uniform_bytes(bytes)).into(),
      Choice::from(1u8),
    )
  }

  /// Converts an element of `ScalarExt2` into a byte representation in
  /// little-endian byte order.
  fn to_bytes(&self) -> [u8; 32] {
    let mut res = [0; 32];
    let els = &self.inner().to_canonical_u64_vec();
    res[..8].copy_from_slice(&els[0].to_le_bytes());
    res[8..16].copy_from_slice(&els[1].to_le_bytes());
    res
  }

  /// Converts a 512-bit little endian integer into
  /// a `ScalarExt2` by reducing by the modulus.
  fn from_bytes_wide(bytes: &[u8; 64]) -> ScalarExt2 {
    GoldilocksExt2::from_uniform_bytes(bytes).into()
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

impl ConstantTimeEq for ScalarExt2 {
  fn ct_eq(&self, other: &Self) -> Choice {
    self.inner().ct_eq(other.inner())
  }
}
impl PartialEq for ScalarExt2 {
  fn eq(&self, other: &Self) -> bool {
    *self.inner() == *other.inner()
  }
}
impl From<u64> for ScalarExt2 {
  fn from(val: u64) -> ScalarExt2 {
    GoldilocksExt2::from_base(&Goldilocks(val)).into()
  }
}
impl From<usize> for ScalarExt2 {
  fn from(val: usize) -> ScalarExt2 {
    GoldilocksExt2::from_base(&Goldilocks(val as u64)).into()
  }
}
impl ConditionallySelectable for ScalarExt2 {
  fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
    GoldilocksExt2::conditional_select(a.inner(), b.inner(), choice).into()
  }
}
impl Zeroize for ScalarExt2 {
  fn zeroize(&mut self) {
    self.0 = GoldilocksExt2::ZERO;
  }
}
impl Neg for ScalarExt2 {
  type Output = Self;

  fn neg(self) -> Self {
    self.0.neg().into()
  }
}
impl Default for ScalarExt2 {
  fn default() -> Self {
    Self::zero()
  }
}
impl ScalarExt2 {
  /// Returns zero, the additive identity.
  pub const fn zero() -> Self {
    Self(GoldilocksExt2::ZERO)
  }

  /// Returns one, the multiplicative identity.
  pub const fn one() -> Self {
    Self(GoldilocksExt2::ONE)
  }
}
impl<'a, 'b> Add<&'b ScalarExt2> for &'a ScalarExt2 {
  type Output = ScalarExt2;

  fn add(self, rhs: &'b ScalarExt2) -> ScalarExt2 {
    self.inner().add(rhs.inner()).into()
  }
}

impl<'a, 'b> Sub<&'b ScalarExt2> for &'a ScalarExt2 {
  type Output = ScalarExt2;

  fn sub(self, rhs: &'b ScalarExt2) -> ScalarExt2 {
    self.inner().sub(rhs.inner()).into()
  }
}

impl<'a, 'b> Mul<&'b ScalarExt2> for &'a ScalarExt2 {
  type Output = ScalarExt2;

  fn mul(self, rhs: &'b ScalarExt2) -> ScalarExt2 {
    let a = self.inner();
    let b = rhs.inner();

    let a1b1 = a.0[0] * b.0[0];
    let a1b2 = a.0[0] * b.0[1];
    let a2b1 = a.0[1] * b.0[0];
    let a2b2 = a.0[1] * b.0[1];

    let c1 = a1b1 + Goldilocks(7) * a2b2;
    let c2 = a2b1 + a1b2;
    GoldilocksExt2([c1, c2]).into()
  }
}

impl<T> Sum<T> for ScalarExt2
where
  T: Borrow<ScalarExt2>,
{
  fn sum<I>(iter: I) -> Self
  where
    I: Iterator<Item = T>,
  {
    iter.fold(ScalarExt2::zero(), |acc, item| acc + item.borrow())
  }
}
impl<T> Product<T> for ScalarExt2
where
  T: Borrow<ScalarExt2>,
{
  fn product<I>(iter: I) -> Self
  where
    I: Iterator<Item = T>,
  {
    iter.fold(ScalarExt2::one(), |acc, item| acc * item.borrow())
  }
}

impl AppendToTranscript for ScalarExt2 {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_scalar(label, self);
  }
}

impl AppendToTranscript for [ScalarExt2] {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(label, b"begin_append_vector");
    for item in self {
      transcript.append_scalar(label, item);
    }
    transcript.append_message(label, b"end_append_vector");
  }
}

crate::impl_add_binop_specify_output!(ScalarExt2, ScalarExt2, ScalarExt2);
crate::impl_sub_binop_specify_output!(ScalarExt2, ScalarExt2, ScalarExt2);
crate::impl_binops_multiplicative_mixed!(ScalarExt2, ScalarExt2, ScalarExt2);
