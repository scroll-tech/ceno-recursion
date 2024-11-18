use ceno_goldilocks::GoldilocksExt2;
// use ceno_goldilocks::{Goldilocks, GoldilocksExt2, SmallField};
// use core::borrow::Borrow;
// use core::iter::{Product, Sum};
// use ff::{Field, FromUniformBytes};
// use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
// use rand::{CryptoRng, RngCore};
// use serde::{Deserialize, Serialize};
// use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
// use zeroize::Zeroize;

// #[derive(Clone, Copy, Eq, Serialize, Deserialize, Hash, Debug)]
pub struct ScalarExt2(GoldilocksExt2);

impl From<GoldilocksExt2> for ScalarExt2 {
    fn from(g: GoldilocksExt2) -> Self {
        Self(g)
    }
}