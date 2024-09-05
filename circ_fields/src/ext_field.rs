use goldilocks::SmallField;
use serde::Serialize;
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

pub trait ExtensionField:
    Serialize
    + From<Self::BaseField>
    + Add<Self::BaseField, Output = Self>
    + Sub<Self::BaseField, Output = Self>
    + Mul<Self::BaseField, Output = Self>
    + for<'a> Add<&'a Self::BaseField, Output = Self>
    + for<'a> Sub<&'a Self::BaseField, Output = Self>
    + for<'a> Mul<&'a Self::BaseField, Output = Self>
    + AddAssign<Self::BaseField>
    + SubAssign<Self::BaseField>
    + MulAssign<Self::BaseField>
    + for<'a> AddAssign<&'a Self::BaseField>
    + for<'a> SubAssign<&'a Self::BaseField>
    + for<'a> MulAssign<&'a Self::BaseField>
{
    const DEGREE: usize;

    type BaseField: SmallField;

    fn from_bases(bases: &[Self::BaseField]) -> Self;

    fn as_bases(&self) -> &[Self::BaseField];

    /// Convert limbs into self
    fn from_limbs(limbs: &[Self::BaseField]) -> Self;
}

pub mod impl_goldilocks {
    use crate::ext_field::ExtensionField;
    use goldilocks::{Goldilocks, GoldilocksExt2, SmallField};
    use crate::{Integer, Arc};

    /// Field modulus
    pub const F_GOLDILOCK_FMOD: Integer = Integer::from(SmallField::MODULUS_U64);
    pub const F_GOLDILOCK_FMOD_ARC: Arc<Integer> = Arc::new(F_GOLDILOCK_FMOD.clone());

    impl ExtensionField for GoldilocksExt2 {
        const DEGREE: usize = 2;

        type BaseField = Goldilocks;

        fn from_bases(bases: &[Goldilocks]) -> Self {
            debug_assert_eq!(bases.len(), 2);
            Self([bases[0], bases[1]])
        }

        fn as_bases(&self) -> &[Goldilocks] {
            self.0.as_slice()
        }

        /// Convert limbs into self
        fn from_limbs(limbs: &[Self::BaseField]) -> Self {
            Self([limbs[0], limbs[1]])
        }
    }
}
