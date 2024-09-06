use serde::{Serialize, Deserialize};
use std::ops::{Neg, Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use ff::{derive::subtle::{Choice, ConditionallySelectable, ConstantTimeEq}, Field};
use rand::RngCore;

use crate::ff_field::FGoldilocks;
use ff::derive::subtle::CtOption;

/// Degree 2 FGoldilocks extension field mod x^2 - 7
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, Hash)]
pub struct FGoldilocksExt2(pub [FGoldilocks; 2]);

impl ConditionallySelectable for FGoldilocksExt2 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self([
            FGoldilocks::conditional_select(&a.0[0], &b.0[0], choice),
            FGoldilocks::conditional_select(&a.0[1], &b.0[1], choice),
        ])
    }
}

impl ConstantTimeEq for FGoldilocksExt2 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0
            .iter()
            .zip(other.0.iter())
            .map(|(a, b)| a.ct_eq(b))
            .fold(1.into(), |acc, x| acc & x)
    }
}

// AS EXTENSION FIELD
impl Mul<&FGoldilocks> for &FGoldilocksExt2 {
    type Output = FGoldilocksExt2;

    #[inline]
    fn mul(self, rhs: &FGoldilocks) -> Self::Output {
        let mut res = *self;
        res.mul_assign(rhs);
        res
    }
}
impl Mul<FGoldilocks> for FGoldilocksExt2 {
    type Output = FGoldilocksExt2;

    #[inline]
    fn mul(self, rhs: FGoldilocks) -> Self::Output {
        &self * &rhs
    }
}
impl<'a> Mul<&'a FGoldilocks> for FGoldilocksExt2 {
    type Output = Self;

    #[inline]
    fn mul(mut self, rhs: &'a FGoldilocks) -> Self::Output {
        self *= rhs;
        self
    }
}
impl MulAssign<&FGoldilocks> for FGoldilocksExt2 {
    #[inline]
    fn mul_assign(&mut self, rhs: &FGoldilocks) {
        self.0[0] *= rhs;
        self.0[1] *= rhs;
    }
}

impl MulAssign<FGoldilocks> for FGoldilocksExt2 {
    #[inline]
    fn mul_assign(&mut self, rhs: FGoldilocks) {
        self.mul_assign(&rhs)
    }
}

impl Add<FGoldilocks> for FGoldilocksExt2 {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: FGoldilocks) -> Self::Output {
        self += &rhs;
        self
    }
}

impl<'a> Add<&'a FGoldilocks> for FGoldilocksExt2 {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: &'a FGoldilocks) -> Self::Output {
        self += rhs;
        self
    }
}

impl AddAssign<FGoldilocks> for FGoldilocksExt2 {
    #[inline]
    fn add_assign(&mut self, rhs: FGoldilocks) {
        *self += &rhs;
    }
}

impl<'a> AddAssign<&'a FGoldilocks> for FGoldilocksExt2 {
    #[inline]
    fn add_assign(&mut self, rhs: &'a FGoldilocks) {
        self.0[0] += rhs;
    }
}

impl Sub<FGoldilocks> for FGoldilocksExt2 {
    type Output = Self;

    #[inline]
    fn sub(mut self, rhs: FGoldilocks) -> Self::Output {
        self -= &rhs;
        self
    }
}

impl<'a> Sub<&'a FGoldilocks> for FGoldilocksExt2 {
    type Output = Self;

    #[inline]
    fn sub(mut self, rhs: &'a FGoldilocks) -> Self::Output {
        self -= rhs;
        self
    }
}

impl SubAssign<FGoldilocks> for FGoldilocksExt2 {
    #[inline]
    fn sub_assign(&mut self, rhs: FGoldilocks) {
        *self -= &rhs;
    }
}

impl<'a> SubAssign<&'a FGoldilocks> for FGoldilocksExt2 {
    #[inline]
    fn sub_assign(&mut self, rhs: &'a FGoldilocks) {
        self.0[0] -= rhs;
    }
}

// AS PRIME FIELD
impl Neg for FGoldilocksExt2 {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self([-self.0[0], -self.0[1]])
    }
}

impl Add for FGoldilocksExt2 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self([self.0[0] + rhs.0[0], self.0[1] + rhs.0[1]])
    }
}
impl<'a> Add<&'a FGoldilocksExt2> for FGoldilocksExt2 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self([self.0[0] + rhs.0[0], self.0[1] + rhs.0[1]])
    }
}
impl AddAssign for FGoldilocksExt2 {
    #[inline]
    fn add_assign(&mut self, rhs: FGoldilocksExt2) {
        *self.0[0] += &rhs.0[0];
        *self.0[1] += &rhs.0[1];
    }
}
impl<'a> AddAssign<&'a FGoldilocksExt2> for FGoldilocksExt2 {
    #[inline]
    fn add_assign(&mut self, rhs: &'a FGoldilocksExt2) {
        *self.0[0] += rhs.0[0];
        *self.0[1] += rhs.0[1];
    }
}

impl Sub for FGoldilocksExt2 {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Self([self.0[0] - rhs.0[0], self.0[1] - rhs.0[1]])
    }
}
impl<'a> Sub<&'a FGoldilocksExt2> for FGoldilocksExt2 {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Self([self.0[0] - rhs.0[0], self.0[1] - rhs.0[1]])
    }
}
impl SubAssign for FGoldilocksExt2 {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self.0[0] -= rhs.0[0];
        *self.0[1] -= rhs.0[1];
    }
}
impl<'a> SubAssign<&'a FGoldilocksExt2> for FGoldilocksExt2 {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self.0[0] -= rhs.0[0];
        *self.0[1] -= rhs.0[1];
    }
}

fn mul_internal(a: &FGoldilocksExt2, b: &FGoldilocksExt2) -> FGoldilocksExt2 {
    // todo: optimizations?
    let a1b1 = a.0[0] * b.0[0];
    let a1b2 = a.0[0] * b.0[1];
    let a2b1 = a.0[1] * b.0[0];
    let a2b2 = a.0[1] * b.0[1];

    let c1 = a1b1 + FGoldilocks::from(7) * a2b2;
    let c2 = a2b1 + a1b2;
    FGoldilocksExt2::from([c1, c2])
}
impl Mul for FGoldilocksExt2 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        mul_internal(&self, &rhs)
    }
}
impl<'a> Mul<&'a FGoldilocksExt2> for FGoldilocksExt2 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        mul_internal(&self, &rhs)
    }
}
impl MulAssign for FGoldilocksExt2 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = mul_internal(&self, &rhs);
    }
}
impl<'a> MulAssign<&'a FGoldilocksExt2> for FGoldilocksExt2 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = mul_internal(&self, &rhs);
    }
}

impl Field for FGoldilocksExt2 {
    /// The zero element of the field, the additive identity.
    fn zero() -> Self {
        Self([FGoldilocks::from(0); 2])
    }

    /// The one element of the field, the multiplicative identity.
    fn one() -> Self {
        Self([FGoldilocks::from(1), FGoldilocks::from(0)])
    }

    /// Returns an element chosen uniformly at random using a user-provided RNG.
    /// Note: this sampler is not constant time!
    fn random(mut rng: impl RngCore) -> Self {
        let a1 = FGoldilocks::random(&mut rng);
        let a2 = FGoldilocks::random(&mut rng);

        Self([a1, a2])
    }

    /// Squares this element.
    #[must_use]
    fn square(&self) -> Self {
        *self * *self
    }

    /// Cubes this element.
    #[must_use]
    fn cube(&self) -> Self {
        self.square() * self
    }

    /// Doubles this element.
    #[must_use]
    fn double(&self) -> Self {
        *self + *self
    }

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    fn invert(&self) -> CtOption<Self> {
        if self.is_zero_vartime() {
            return CtOption::new(Self::default(), (false as u8).into());
        }

        let a_pow_r_minus_1 = self.frobenius();
        let a_pow_r = a_pow_r_minus_1 * *self;
        debug_assert!(a_pow_r.0[1] == FGoldilocks::ZERO);
        let a_pow_r_inv = a_pow_r.0[0].invert().expect("inverse does not exist");

        let res = [
            a_pow_r_minus_1.0[0] * a_pow_r_inv,
            a_pow_r_minus_1.0[1] * a_pow_r_inv,
        ];

        CtOption::new(Self(res), Choice::from(1))
    }

    /// Returns the square root of the field element, if it is
    /// quadratic residue.
    fn sqrt(&self) -> Option<Self> {
        unimplemented!()
    }
}