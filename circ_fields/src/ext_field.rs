use serde::{Serialize, Deserialize};
use std::ops::{Neg, Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use ff::{derive::subtle::{Choice, ConditionallySelectable, ConstantTimeEq}, Field};
use rand::RngCore;

use crate::ff_field::FGoldilocks;
use ff::derive::subtle::CtOption;
use rug::Integer;

/// Degree 2 FGoldilocks extension field mod x^2 - 7
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, Hash)]
pub struct FGoldilocksExt2(pub [FGoldilocks; 2]);

impl FGoldilocksExt2 {
    /// FrobeniusField automorphisms: x -> x^p, where p is the order of BaseField.
    fn frobenius(&self) -> Self {
        self.repeated_frobenius(1)
    }

    /// Repeated Frobenius automorphisms: x -> x^(p^count).
    ///
    /// Follows precomputation suggestion in Section 11.3.3 of the
    /// Handbook of Elliptic and Hyperelliptic Curve Cryptography.
    fn repeated_frobenius(&self, count: usize) -> Self {
        if count == 0 {
            return *self;
        } else if count >= 2 {
            // x |-> x^(p^D) is the identity, so x^(p^count) ==
            // x^(p^(count % D))
            return self.repeated_frobenius(count % 2);
        }
        let arr = self.0;

        // z0 = DTH_ROOT^count = W^(k * count) where k = floor((p^D-1)/D)
        let mut z0 = FGoldilocks::from(18446744069414584320u64);
        for _ in 1..count {
            z0 *= FGoldilocks::from(18446744069414584320u64);
        }
        let z0square = z0 * z0;

        let mut res = [FGoldilocks::from(0u64); 2];

        res[0] = arr[0] * z0;
        res[1] = arr[1] * z0square;

        Self(res)
    }
}

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
impl Mul<i64> for FGoldilocksExt2 {
    type Output = FGoldilocksExt2;

    #[inline]
    fn mul(self, rhs: i64) -> Self::Output {
        &self * &FGoldilocks::from(rhs)
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
impl MulAssign<i64> for FGoldilocksExt2 {
    #[inline]
    fn mul_assign(&mut self, rhs: i64) {
        self.mul_assign(&FGoldilocks::from(rhs))
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
impl Add<i64> for FGoldilocksExt2 {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: i64) -> Self::Output {
        self += &FGoldilocks::from(rhs);
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
impl AddAssign<i64> for FGoldilocksExt2 {
    #[inline]
    fn add_assign(&mut self, rhs: i64) {
        *self += &FGoldilocks::from(rhs);
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
impl Sub<i64> for FGoldilocksExt2 {
    type Output = Self;

    #[inline]
    fn sub(mut self, rhs: i64) -> Self::Output {
        self -= &FGoldilocks::from(rhs);
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
impl SubAssign<i64> for FGoldilocksExt2 {
    #[inline]
    fn sub_assign(&mut self, rhs: i64) {
        *self -= &FGoldilocks::from(rhs);
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
    fn add(self, rhs: &'a FGoldilocksExt2) -> Self::Output {
        Self([self.0[0] + rhs.0[0], self.0[1] + rhs.0[1]])
    }
}
impl AddAssign for FGoldilocksExt2 {
    #[inline]
    fn add_assign(&mut self, rhs: FGoldilocksExt2) {
        self.0[0] += &rhs.0[0];
        self.0[1] += &rhs.0[1];
    }
}
impl<'a> AddAssign<&'a FGoldilocksExt2> for FGoldilocksExt2 {
    #[inline]
    fn add_assign(&mut self, rhs: &'a FGoldilocksExt2) {
        self.0[0] += rhs.0[0];
        self.0[1] += rhs.0[1];
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
    fn sub(self, rhs: &'a FGoldilocksExt2) -> Self::Output {
        Self([self.0[0] - rhs.0[0], self.0[1] - rhs.0[1]])
    }
}
impl SubAssign for FGoldilocksExt2 {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.0[0] -= rhs.0[0];
        self.0[1] -= rhs.0[1];
    }
}
impl<'a> SubAssign<&'a FGoldilocksExt2> for FGoldilocksExt2 {
    #[inline]
    fn sub_assign(&mut self, rhs: &'a FGoldilocksExt2) {
        self.0[0] -= rhs.0[0];
        self.0[1] -= rhs.0[1];
    }
}

fn mul_internal(a: &FGoldilocksExt2, b: &FGoldilocksExt2) -> FGoldilocksExt2 {
    // todo: optimizations?
    let a1b1 = a.0[0] * b.0[0];
    let a1b2 = a.0[0] * b.0[1];
    let a2b1 = a.0[1] * b.0[0];
    let a2b2 = a.0[1] * b.0[1];

    let c1 = a1b1 + FGoldilocks::from(7u64) * a2b2;
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
    fn mul(self, rhs: &'a FGoldilocksExt2) -> Self::Output {
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
    fn mul_assign(&mut self, rhs: &'a FGoldilocksExt2) {
        *self = mul_internal(&self, &rhs);
    }
}

impl Field for FGoldilocksExt2 {
    /// The zero element of the field, the additive identity.
    fn zero() -> Self {
        Self([FGoldilocks::from(0u64); 2])
    }

    /// The one element of the field, the multiplicative identity.
    fn one() -> Self {
        Self([FGoldilocks::from(1u64), FGoldilocks::from(0u64)])
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
        debug_assert!(a_pow_r.0[1] == FGoldilocks::from(0u64));
        let a_pow_r_inv = a_pow_r.0[0].invert().expect("inverse does not exist");

        let res = [
            a_pow_r_minus_1.0[0] * a_pow_r_inv,
            a_pow_r_minus_1.0[1] * a_pow_r_inv,
        ];

        CtOption::new(Self(res), Choice::from(1))
    }

    /// Returns the square root of the field element, if it is
    /// quadratic residue.
    fn sqrt(&self) -> CtOption<Self> {
        unimplemented!()
    }
}

impl std::convert::From<[FGoldilocks; 2]> for FGoldilocksExt2 {
    #[track_caller]
    fn from(limbs: [FGoldilocks; 2]) -> Self {
        FGoldilocksExt2(limbs)
    }
}

impl std::convert::From<Integer> for FGoldilocksExt2 {
    #[track_caller]
    fn from(i: Integer) -> Self {
        let ui: u64 = i.try_into().unwrap();
        FGoldilocksExt2::from(ui)
    }
}

impl std::convert::From<i64> for FGoldilocksExt2 {
    #[track_caller]
    fn from(i: i64) -> Self {
        let u = i.abs_diff(0);
        let neg = i < 0;
        if neg {
            -FGoldilocksExt2::from(u)
        } else {
            FGoldilocksExt2::from(u)
        }
    }
}

impl std::convert::From<u64> for FGoldilocksExt2 {
    #[track_caller]
    fn from(i: u64) -> Self {
        FGoldilocksExt2::from([FGoldilocks::from(i), FGoldilocks::from(0u64)])
    }
}

impl std::convert::From<&FGoldilocksExt2> for Integer {
    #[track_caller]
    fn from(f: &FGoldilocksExt2) -> Self {
        assert_eq!(f.0[1], FGoldilocks::from(0u64));
        Integer::from(&f.0[0])
    }
}