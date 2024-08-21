struct PublicKey {
    p: Point,
    q: Point,
}

struct SecretKey {
    a: usize,
    pk: PublicKey,
}

struct Signature {
    R: Point,
    s: usize,
}

pub fn gen() -> (PublicKey, SecretKey) {
    let p0 = Point {
        x: Fp::from(265),
        
    }
}