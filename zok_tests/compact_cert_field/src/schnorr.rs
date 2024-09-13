use crate::curve::*;
use rand::Rng;
use ff::PrimeField;
use crate::field::Fp;
use crate::poseidon;
use crate::Integer;

#[derive(Clone, Debug)]
pub struct PublicKey {
    pub p: Point,
    pub q: Point,
}

#[derive(Clone, Debug)]
pub struct SecretKey {
    pub a: Integer,
    pub pk: PublicKey,
}

#[derive(Clone, Debug)]
pub struct Signature {
    pub r: Point,
    pub s: Integer,
}

pub fn gen_r(num_bits: usize) -> (Integer, Vec<bool>) {
    let mut a_bits = Vec::new();
    let mut rng = rand::thread_rng();
    for _ in 0..num_bits {
        let bit: bool = rng.gen();
        a_bits.insert(0, bit);
    }
    let mut a = Integer::from(1);
    let mut i = 0;
    while !a_bits[i] {
        i += 1;
    }
    while i < a_bits.len() {
        a *= 2;
        if a_bits[i] {
            a += Integer::from(1);
        }
        i += 1;
    }
    (a, a_bits)
}

pub fn gen() -> (PublicKey, SecretKey) {
    let x = Fp::from_str_vartime("2023776050662786605020065854616777351003832247628992350849206310281785027488").unwrap();
    let y = Fp::from_str_vartime("1079270832837170318396516616249394502719834190979906495690419930531357954746").unwrap();
    assert_eq!(y * y, x * x * x + Fp::from(A) * x + Fp::from(B));
    let p = Point {
        x,
        y 
    };
    // Randomize 252 bits to form a
    let (a, _) = gen_r(252);

    let q = curve_mul(&p, a.clone());
    let pk = PublicKey {
        p,
        q,
    };
    let sk = SecretKey {
        a,
        pk: pk.clone(),
    };
    (pk, sk)
}

// Record down e to be used by the circuit
pub fn sign(sk: &SecretKey, m: &Fp) -> (Signature, Integer) {
    let order = Integer::from_str_radix("7237005577332262213973186563042994240955753618821290553176770668684506720427", 10).unwrap();
    let (k, _) = gen_r(252);
    let r = curve_mul(&sk.pk.p, k.clone());
    // Produce hash
    let e = Integer::from(&poseidon(&[m.clone(), r.x.clone(), r.y.clone(), Fp::from(0), Fp::from(0)]));
    let s = (k + sk.a.clone() * e.clone()) % order;
    (
        Signature { r, s },
        e
    )
}

pub fn verify_sig(pk: &PublicKey, sig: &Signature, m: &Fp) {
    // Produce hash
    let e = Integer::from(&poseidon(&[m.clone(), sig.r.x.clone(), sig.r.y.clone(), Fp::from(0), Fp::from(0)]));

    let eq = curve_mul(&pk.q, e);
    let sp = curve_mul(&pk.p, sig.s.clone());
    assert_eq!(curve_add(&sig.r, &eq), sp);
}