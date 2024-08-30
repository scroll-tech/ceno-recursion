use crate::curve::*;
use crate::Sha256;
use rs_merkle::Hasher;
use rand::Rng;
use ff::PrimeField;
use primitive_types::U512;
use crate::field::Fp;

#[derive(Clone, Debug)]
pub struct PublicKey {
    pub p: Point,
    pub q: Point,
}

#[derive(Clone, Debug)]
pub struct SecretKey {
    pub a: U512,
    pub pk: PublicKey,
}

#[derive(Clone, Debug)]
pub struct Signature {
    pub r: Point,
    pub s: U512,
}

pub fn gen_r(num_bits: usize) -> (U512, Vec<bool>) {
    let mut a_bits = Vec::new();
    let mut rng = rand::thread_rng();
    for _ in 0..num_bits {
        let bit: bool = rng.gen();
        a_bits.insert(0, bit);
    }
    let mut a: U512 = U512::from(1);
    let mut i = 0;
    while !a_bits[i] {
        i += 1;
    }
    while i < a_bits.len() {
        a *= 2;
        if a_bits[i] {
            a += U512::from(1);
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

    let q = curve_mul(&p, a);
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

pub fn sign(sk: &SecretKey, m: &[u8]) -> Signature {
    let order: U512 = U512::from_dec_str("7237005577332262213973186563042994240955753618821290553176770668684506720427").unwrap();
    let (k, _) = gen_r(252);
    let r = curve_mul(&sk.pk.p, k);
    // Produce hash
    let mut hin: Vec<u8> = Vec::new();
    hin.extend(m);
    let x_bytes: Vec<u8> = bincode::serialize(&r.x).unwrap();
    let y_bytes: Vec<u8> = bincode::serialize(&r.y).unwrap();
    hin.extend(x_bytes);
    hin.extend(y_bytes);
    let e_bytes = Sha256::hash(&hin);
    let mut e: U512 = U512::from(0);
    for e_byte in e_bytes {
        e *= 256;
        e += e_byte.into();
        e %= order;
    }
    let s = (k + sk.a * e) % order;
    Signature {
        r,
        s
    }
}

pub fn verify_sig(pk: &PublicKey, sig: &Signature, m: &[u8]) -> bool {
    let order: U512 = U512::from_dec_str("7237005577332262213973186563042994240955753618821290553176770668684506720427").unwrap();
    // Produce hash
    let mut hin: Vec<u8> = Vec::new();
    hin.extend(m);
    let x_bytes: Vec<u8> = bincode::serialize(&sig.r.x).unwrap();
    let y_bytes: Vec<u8> = bincode::serialize(&sig.r.y).unwrap();
    hin.extend(x_bytes);
    hin.extend(y_bytes);
    let e_bytes = Sha256::hash(&hin);
    let mut e: U512 = U512::from(0);
    for e_byte in e_bytes {
        e *= 256;
        e += e_byte.into();
        e %= order;
    }

    let eq = curve_mul(&pk.q, e);
    let sp = curve_mul(&pk.p, sig.s);
    return curve_add(&sig.r, &eq) == sp
}