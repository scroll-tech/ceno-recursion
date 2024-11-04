mod goldilocks;
pub type Scalar = goldilocks::Scalar;

pub trait ScalarFromPrimitives {
  fn to_scalar(self) -> Scalar;
}

impl ScalarFromPrimitives for usize {
  #[inline]
  fn to_scalar(self) -> Scalar {
    (0..self).map(|_i| Scalar::one()).sum()
  }
}
