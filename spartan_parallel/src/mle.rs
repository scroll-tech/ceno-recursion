use crate::scalar::SpartanExtensionField;
use std::cmp::max;

pub trait MLEType {}

pub struct Base;
impl MLEType for Base {}

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

// Define general behavior of MLE
impl<S: SpartanExtensionField, T: MLEType> MLE<S, T>
{
    pub fn len(&self) -> usize {
        max(self.ext_vec.len(), self.base_vec.len())
    }
}

// Define behavior of MLE when elements are in the base field
impl<S: SpartanExtensionField> MLE<S, Base>
{
    pub fn new(vals: Vec<S::BaseField>) -> Self {
        Self {
            t: Base,
            ext_vec: vec![],
            base_vec: vals,
        }
    }
}

// Define behavior of MLE when elements are in the extended field
impl<S: SpartanExtensionField> MLE<S, Ext>
{
    pub fn new(vals: Vec<S>) -> Self {
        Self {
            t: Ext,
            ext_vec: vals,
            base_vec: vec![],
        }
    }
}