mod curve;
mod schnorr;

use rs_merkle::algorithms::Sha256;
use rs_merkle::{MerkleTree, Hasher, MerkleProof};
use rand::*;
use crate::schnorr::*;

// Attestor info
#[derive(Clone)]
struct Attestor {
    sig: Signature,
    pk: PublicKey,
    weight: usize
}
impl Attestor {
    fn new(sig: Signature, pk: PublicKey, weight: usize) -> Attestor {
        Attestor {
            sig,
            pk,
            weight
        }
    }

    // bit:        8       8       4       4      8
    // entry: pk.p.x, pk.p.y, pk.q.x, pk.q.y, weight
    fn hash(&self) -> [u8; 32] {
        let pk_p_x_hash: [u8; 8] = Sha256::hash(&self.pk.p.x.to_bytes())[24..].try_into().unwrap();
        let pk_p_y_hash: [u8; 8] = Sha256::hash(&self.pk.p.y.to_bytes())[24..].try_into().unwrap();
        let pk_q_x_hash: [u8; 4] = Sha256::hash(&self.pk.q.x.to_bytes())[28..].try_into().unwrap();
        let pk_q_y_hash: [u8; 4] = Sha256::hash(&self.pk.q.y.to_bytes())[28..].try_into().unwrap();
        let pk_q_hash: [u8; 8] = [pk_q_x_hash, pk_q_y_hash].concat().try_into().unwrap();
        let weight_hash: [u8; 8] = Sha256::hash(&self.weight.to_ne_bytes())[24..].try_into().unwrap();
        [pk_p_x_hash, pk_p_y_hash, pk_q_hash, weight_hash].concat().try_into().unwrap()
    }
}

// Signature Info
#[derive(Clone)]
struct Sig {
    l: usize,
    r: usize,
    sig: Option<Signature>
}
impl Sig {
    fn new(l: usize, r: usize, sig: Option<Signature>) -> Sig {
        Sig {
            l,
            r,
            sig
        }
    }

    // bit:   8   8        4        4      8
    // entry: l,  r, sig.r.x, sig.r.y, sig.s
    fn hash(&self) -> [u8; 32] {
        let l_hash: [u8; 8] = Sha256::hash(&self.l.to_ne_bytes())[24..].try_into().unwrap();
        let r_hash: [u8; 8] = Sha256::hash(&self.r.to_ne_bytes())[24..].try_into().unwrap();
        if let Some(sig) = &self.sig {
            let sig_r_x_hash: [u8; 4] = Sha256::hash(&sig.r.x.to_bytes())[28..].try_into().unwrap();
            let sig_r_y_hash: [u8; 4] = Sha256::hash(&sig.r.y.to_bytes())[28..].try_into().unwrap();
            let sig_r_hash: [u8; 8] = [sig_r_x_hash, sig_r_y_hash].concat().try_into().unwrap();
            let mut sig_s_buffer: [u8; 64] = [0; 64];
            sig.s.to_big_endian(&mut sig_s_buffer);
            let sig_s_hash: [u8; 8] = Sha256::hash(&sig_s_buffer[32..])[24..].try_into().unwrap();
            [l_hash, r_hash, sig_r_hash, sig_s_hash].concat().try_into().unwrap()
        } else {
            [l_hash, r_hash, [0; 8], [0; 8]].concat().try_into().unwrap()
        }
    }
}

// Reveal Proof Entry
struct T {
    i: usize,
    s: [u8; 32],
    pi_s: MerkleProof<Sha256>,
    p: [u8; 32],
    pi_p: MerkleProof<Sha256>,
}
impl T {
    fn new(i: usize, s: [u8; 32], pi_s: MerkleProof<Sha256>, p: [u8; 32], pi_p: MerkleProof<Sha256>) -> T {
        T {
            i,
            s,
            pi_s,
            p,
            pi_p
        }
    }
}

// Proof
struct CompactCertProof {
    sig_root: [u8; 32],
    signed_weight: usize,
    t_list: Vec<T>
}

const MSG_LEN: usize = 15;
const NUM_ATTESTORS: usize = 10;
const PROVEN_WEIGHT: usize = 8;
const KNOWLEDGE_SOUNDNESS: usize = 10; // knowledge soundness of 2^{-k}
const MAX_NUM_REVEALS: usize = 2; // num reveals 2^q

// Commit all attestors as a merkle tree
fn trusted_setup(
    attestors: &Vec<Attestor>
) -> Result<([u8; 32], MerkleTree<Sha256>), String> {
    let leaves: Vec<[u8; 32]> = attestors.iter().map(|att| att.hash()).collect();
    let merkle_tree = MerkleTree::<Sha256>::from_leaves(&leaves);
    let root = merkle_tree.root().ok_or("couldn't get the merkle root")?;

    Ok((root, merkle_tree))
}

fn prover(
    attestors: &Vec<Attestor>, 
    proven_weight: usize,
    k: usize, // knowledge error ~2^{-k} 
    q: usize, // <=2^q random oracle queries
    message: &[u8], // the message being signed
    att_root: &[u8; 32], // commitment to the attestors (root of merkle tree)
    att_tree: &MerkleTree<Sha256>,
) -> Result<(CompactCertProof, Vec<Attestor>, Vec<Sig>), String> {
    let mut signed_weight = 0;
    let mut collected_list = vec![false; attestors.len()];
    
    // Check uniqueness and signature of each attestor
    let mut i = 0;
    for a in attestors {
        // Check signature
        assert!(verify_sig(&a.pk, &a.sig, &message));
        signed_weight += a.weight;
        
        collected_list[i] = true;
        i += 1;
    }
    assert!(signed_weight > proven_weight);

    // Convert attestors into sigs structure
    let mut sigs: Vec<Sig> = Vec::new();
    for i in 0..attestors.len() {
        if collected_list[i] {
            sigs.push(Sig::new(
                if i == 0 { 0 } else { sigs[i - 1].r },
                if i == 0 { 0 } else { sigs[i - 1].r } + attestors[i].weight,
                Some(attestors[i].sig.clone())
            ));
        } else {
            sigs.push(Sig::new(
                if i == 0 { 0 } else { sigs[i - 1].r },
                if i == 0 { 0 } else { sigs[i - 1].r },
                None
            ));
        }
    }
    assert!(sigs[sigs.len() - 1].r == signed_weight);

    // Construct merkle tree for sigs
    let (sig_root, sig_tree) = {
        let leaves: Vec<[u8; 32]> = sigs.iter().map(|i| i.hash()).collect();
        let merkle_tree = MerkleTree::<Sha256>::from_leaves(&leaves);
        let root = merkle_tree.root().ok_or("couldn't get the merkle root")?;
        (root, merkle_tree)
    };

    // Map cumulated weight back to index
    // Binary search, lo inclusive, hi exclusive
    // Need to skip signatures with 0 weight (those not selected)
    let int_to_ind = |coin: usize, mut lo: usize, mut hi: usize| -> usize {
        assert!(coin < signed_weight);
        while lo + 1 < hi {
            let mid = (lo + hi - 1) / 2;
            if sigs[mid].l > coin {
                hi = mid;
            } else if sigs[mid].r <= coin {
                lo = mid + 1;
            } else {
                lo = mid;
                hi = mid + 1;
            }
        }
        assert_eq!(lo + 1, hi);
        lo
    };

    // Fiat-Shamir of oracle queries
    let num_reveals: usize = (k + q).div_ceil((signed_weight / proven_weight).ilog2() as usize);
    let mut t_list = Vec::new();
    let mut att_list = Vec::new();
    let mut sig_list = Vec::new();
    for j in 0..num_reveals {
        let mut hin: Vec<u8> = Vec::new();
        // hin <- (j, root, proven_weight, message, commit)
        hin.extend((j as u32).to_ne_bytes());
        hin.extend(sig_root);
        hin.extend(proven_weight.to_ne_bytes());
        hin.extend(message);
        hin.extend(att_root);

        // Compute coin_hash modulo signed_weight
        let coin_hash = Sha256::hash(&hin);
        let mut coin: usize = 0;
        for j in coin_hash {
            coin = (2 * coin + j as usize) % signed_weight;
        }
        let i = int_to_ind(coin, 0, attestors.len());
        att_list.push(attestors[i].clone());
        sig_list.push(sigs[i].clone());

        // Construct Merkle Proof for Sig
        let (sig_leaf, sig_proof) = {
            let leaf = sig_tree.leaves().ok_or("sig tree contains no leaf")?[i];
            let merkle_proof = sig_tree.proof(&vec![i]);
            (leaf, merkle_proof)
        };

        // Construct Merkle Proof for Att
        let (att_leaf, att_proof) = {
            let leaf = att_tree.leaves().ok_or("att tree contains no leaf")?[i];
            let merkle_proof = att_tree.proof(&vec![i]);
            (leaf, merkle_proof)
        };

        t_list.push(T::new(i, sig_leaf, sig_proof, att_leaf, att_proof));
    }
    
    Ok((
        CompactCertProof {
            sig_root,
            signed_weight,
            t_list
        },
        att_list,
        sig_list,
    ))
}

fn verifier(
    compact_cert_proof: &CompactCertProof,
    proven_weight: usize,
    k: usize,
    q: usize,
    message: &[u8], // the message being signed
    att_len: usize,
    att_root: [u8; 32],
    // List of attestors / sigs provided by the prover
    att_list: &Vec<Attestor>,
    sig_list: &Vec<Sig>,
) {
    let signed_weight = compact_cert_proof.signed_weight;
    assert!(signed_weight > proven_weight);
    let num_reveals: usize = (k + q).div_ceil((signed_weight / proven_weight).ilog2() as usize);
    assert_eq!(num_reveals, att_list.len());
    assert_eq!(num_reveals, sig_list.len());

    for j in 0..num_reveals {
        // Reproduce coin
        let mut hin: Vec<u8> = Vec::new();
        // hin <- (j, root, proven_weight, message, commit)
        hin.extend((j as u32).to_ne_bytes());
        hin.extend(compact_cert_proof.sig_root);
        hin.extend(proven_weight.to_ne_bytes());
        hin.extend(message);
        hin.extend(att_root);
        // Compute coin_hash modulo signed_weight
        let coin_hash = Sha256::hash(&hin);
        let mut coin: usize = 0;
        for j in coin_hash {
            coin = (2 * coin + j as usize) % signed_weight;
        }

        let t = &compact_cert_proof.t_list[j];
        // Sig Opening
        assert!(t.pi_s.verify(compact_cert_proof.sig_root, &vec![t.i], &vec![t.s], att_len));
        // Att Opening
        assert!(t.pi_p.verify(att_root, &vec![t.i], &vec![t.p], att_len));
        // Validity of signature
        assert_eq!(att_list[j].hash(), t.p);
        assert!(verify_sig(&att_list[j].pk, &sig_list[j].sig.clone().unwrap(), &message));
        // L < coin <= L + Weight
        assert_eq!(sig_list[j].hash(), t.s);
        assert!(sig_list[j].l <= coin && coin < sig_list[j].l + att_list[j].weight);
    }
}

fn main() {
    // Generate message
    let mut rng = rand::thread_rng();
    let mut message: [u8; MSG_LEN] = [0; MSG_LEN];
    rng.try_fill(&mut message).unwrap();

    // Generate attestors
    let mut attestors = Vec::new();
    for i in 0..NUM_ATTESTORS {
        let (pk, sk) = gen();
        let attestor_sig = sign(&sk, &message);
        attestors.push(Attestor::new(attestor_sig, pk, i));
    }
    let k = KNOWLEDGE_SOUNDNESS;
    let q = MAX_NUM_REVEALS;

    // TRUSTED SETUP
    let (att_root, att_tree) = trusted_setup(&attestors).unwrap();
    
    // PROVER
    let (compact_cert_proof, att_list, sig_list) = prover(&attestors, PROVEN_WEIGHT, k, q, &message, &att_root, &att_tree).unwrap();

    // VERIFIER
    verifier(&compact_cert_proof, PROVEN_WEIGHT, k, q, &message, attestors.len(), att_root, &att_list, &sig_list);

    println!("Verification Successful!")
}
