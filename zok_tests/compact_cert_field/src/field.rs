use ff::PrimeField;
use serde::{Serialize, Deserialize};

// --
// FIELD OPERATIONS
// --
#[derive(PrimeField, Serialize, Deserialize)]
#[PrimeFieldModulus = "7237005577332262213973186563042994240857116359379907606001950938285454250989"]
#[PrimeFieldGenerator = "9"]
#[PrimeFieldReprEndianness = "little"]
pub struct Fp([u64; 4]);

impl Fp {
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.map(|i| i.to_ne_bytes()).concat().try_into().unwrap()
    }
}