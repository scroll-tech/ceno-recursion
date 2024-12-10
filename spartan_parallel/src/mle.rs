use crate::scalar::SpartanExtensionField;
use std::cmp::max;
use std::ops::{Index, IndexMut, Range, RangeFrom, RangeTo};

pub trait MLEType {}

#[derive(Debug, Clone)]
pub struct Base;
impl MLEType for Base {}

#[derive(Debug, Clone)]
pub struct Ext;
impl MLEType for Ext {}

#[derive(Debug, Clone)]
pub struct MLE<S: SpartanExtensionField, T: MLEType> {
  t: T,

  // Depending on T, one of the following fields will be empty.
  // For MLE, field elements can potentially be stored as elements
  // in the base field (resource saving) or in the extended field.
  ext_vec: Vec<S>,
  base_vec: Vec<S::BaseField>,
}

// Define universal behavior of MLE
impl<S: SpartanExtensionField, T: MLEType> MLE<S, T> {
  pub fn len(&self) -> usize {
    max(self.ext_vec.len(), self.base_vec.len())
  }
}

// Define behavior of MLE when elements are in the base field
impl<S: SpartanExtensionField> MLE<S, Base> {
  pub fn new(vals: Vec<S::BaseField>) -> Self {
    Self {
      t: Base,
      ext_vec: vec![],
      base_vec: vals,
    }
  }

  pub fn inner_ref(&self) -> &Vec<S::BaseField> {
    &self.base_vec
  }
}

impl<S: SpartanExtensionField> Index<usize> for MLE<S, Base> {
  type Output = S::BaseField;

  fn index(&self, index: usize) -> &Self::Output {
    &self.base_vec[index]
  }
}

impl<S: SpartanExtensionField> Index<Range<usize>> for MLE<S, Base> {
  type Output = [S::BaseField];

  fn index(&self, index: Range<usize>) -> &Self::Output {
    &self.base_vec[index]
  }
}

impl<S: SpartanExtensionField> Index<RangeTo<usize>> for MLE<S, Base> {
  type Output = [S::BaseField];

  fn index(&self, range: RangeTo<usize>) -> &Self::Output {
    &self.base_vec[range]
  }
}

impl<S: SpartanExtensionField> Index<RangeFrom<usize>> for MLE<S, Base> {
  type Output = [S::BaseField];

  fn index(&self, range: RangeFrom<usize>) -> &Self::Output {
    &self.base_vec[range]
  }
}

impl<S: SpartanExtensionField> IndexMut<usize> for MLE<S, Base> {
  fn index_mut(&mut self, index: usize) -> &mut Self::Output {
    &mut self.base_vec[index]
  }
}

// Define behavior of MLE when elements are in the extended field
impl<S: SpartanExtensionField> MLE<S, Ext> {
  pub fn new(vals: Vec<S>) -> Self {
    Self {
      t: Ext,
      ext_vec: vals,
      base_vec: vec![],
    }
  }

  pub fn inner_ref(&self) -> &Vec<S> {
    &self.ext_vec
  }

  pub fn extend(&mut self, other_vec: &Vec<S>) -> &Vec<S> {
    self.ext_vec.extend(other_vec);
    &self.ext_vec
  }
}

impl<S: SpartanExtensionField> Index<usize> for MLE<S, Ext> {
  type Output = S;

  fn index(&self, index: usize) -> &Self::Output {
    &self.ext_vec[index]
  }
}

impl<S: SpartanExtensionField> Index<Range<usize>> for MLE<S, Ext> {
  type Output = [S];

  fn index(&self, index: Range<usize>) -> &Self::Output {
    &self.ext_vec[index]
  }
}

impl<S: SpartanExtensionField> Index<RangeTo<usize>> for MLE<S, Ext> {
  type Output = [S];

  fn index(&self, range: RangeTo<usize>) -> &Self::Output {
    &self.ext_vec[range]
  }
}

impl<S: SpartanExtensionField> Index<RangeFrom<usize>> for MLE<S, Ext> {
  type Output = [S];

  fn index(&self, range: RangeFrom<usize>) -> &Self::Output {
    &self.ext_vec[range]
  }
}

impl<S: SpartanExtensionField> IndexMut<usize> for MLE<S, Ext> {
  fn index_mut(&mut self, index: usize) -> &mut Self::Output {
    &mut self.ext_vec[index]
  }
}
