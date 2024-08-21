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

#[derive(Clone)]
struct Point {
    x: Fp,
    y: Fp
}

const A: Fp = Fp::from(526);
const B: Fp = Fp::from(265);

pub fn curve_add(a: &Point, b: &Point) -> Point {
    let m = if a.x != b.x {
        (b.y - a.y) / (b.x - a.x)
    } else {
        (3 * a.x * a.x + A) / (2 * a.y)
    };
    let x3 = m * m - a.x - b.x
    let y3 = m * (a.x - x3) - b.y
    Point {
        x: x3,
        y: y3
    }
}

pub fn curve_double(a: &Point) -> Point {
    curve_add(a, a)
}

pub fn curve_mul(a: &Point, k: Fp) -> Point {
    let mut a_k = a.clone()
    let mut k_bits = Vec::new()
    while k > 0 {
        let k_mod_2 = k % 2
        k_bits.insert(0, k_mod_2)
        k = (k - k_mod_2) / Fp::from(2)
    }
    for i in 1..k_bits.len() {
        a_k = curve_add(&a_k, &a_k)
        if k_bits[i] == 1 {
            a_k = curve_add(&a_k, a)
        }
    }
    a_k
}