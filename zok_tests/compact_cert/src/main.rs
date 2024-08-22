mod curve;
mod schnorr;

use std::collections::HashSet;
use rs_merkle::algorithms::Sha256;
use rs_merkle::{MerkleTree, Hasher, MerkleProof};
use rand::*;
use serde::{Serialize, Deserialize};
use crate::schnorr::*;

// Attestor info
#[derive(Serialize, Deserialize)]
struct Attestor {
    signature: Signature,
    weight: usize
}
impl Attestor {
    fn new(signature: Signature, weight: usize) -> Attestor {
        Attestor {
            signature,
            weight
        }
    }
}

// Signature Info
#[derive(Serialize, Deserialize)]
struct Sig {
    l: usize,
    r: usize,
    sig: Option<Signature>
}
impl Sig {
    fn new(l: usize, r: usize, sig: Option<[u8; 24]>) -> Sig {
        Sig {
            l,
            r,
            sig
        }
    }
}

// Reveal Proof Entry
struct T {
    i: usize,
    s: &[u8],
    pi_s: MerkleProof<Sha256>,
    p: &[u8],
    pi_p: MerkleProof<Sha256>,
}
impl T {
    fn new(i: usize, s: &[u8], pi_s: MerkleProof<Sha256>, p: &[u8], pi_p: MerkleProof<Sha256>) -> T {
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
    let leaves: Vec<Vec<u8>> = attestors.iter().map(|att| bincode::serialize(&att).unwrap()).collect();
    let merkle_tree = MerkleTree::<Sha256>::from_leaves(&leaves);
    let root = merkle_tree.root().ok_or("couldn't get the merkle root")?;

    Ok((root, merkle_tree))
}

/*
fn prover(
    attestors: &Vec<Attestor>, 
    proven_weight: usize,
    k: usize, // knowledge error ~2^{-k} 
    q: usize, // <=2^q random oracle queries
    message: &[u8], // the message being signed
    att_root: &[u8], // commitment to the attestors (root of merkle tree)
    att_tree: &MerkleTree<Sha256>,
) -> Result<CompactCertProof, String> {
    let mut signers_list = HashSet::new();
    let mut signed_weight = 0;
    let mut collected_list = vec![false; attestors.len()];
    
    // Check uniqueness and signature of each attestor
    let mut i = 0;
    for a in attestors {
        if !signers_list.contains(&a.label) {
            signers_list.insert(a.label);
            // Check signature
            assert!(att_tree.leaves().unwrap()[i][..24] == a.signature);
            signed_weight += a.weight;
            
            collected_list[i] = true;
        }
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
                Some(attestors[i].signature)
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
        let leaves: Vec<[u8; 32]> = sigs.iter().map(|i| i.to_byte_array()).collect();
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
    
    Ok(CompactCertProof {
        sig_root,
        signed_weight,
        t_list
    })
}

fn verifier(
    compact_cert_proof: &CompactCertProof,
    proven_weight: usize,
    k: usize,
    q: usize,
    message: &[u8], // the message being signed
    att_len: usize,
    att_root: [u8; 32],
) {
    let signed_weight = compact_cert_proof.signed_weight;
    assert!(signed_weight > proven_weight);
    let num_reveals: usize = (k + q).div_ceil((signed_weight / proven_weight).ilog2() as usize);

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
        assert_eq!(t.s[..24], t.p[..24]);
        // L < coin <= L + Weight
        let l = u32::from_ne_bytes(t.s[24..28].try_into().unwrap()) as usize;
        let weight = u32::from_ne_bytes(t.p[28..32].try_into().unwrap()) as usize;
        assert!(l <= coin && coin < l + weight);
    }
}
*/

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
        attestors.push(Attestor::new(attestor_sig, i));
    }
    let k = KNOWLEDGE_SOUNDNESS;
    let q = MAX_NUM_REVEALS;

    // TRUSTED SETUP
    let (att_root, att_tree) = trusted_setup(&attestors).unwrap();
    
    /*
    // PROVER
    let compact_cert_proof = prover(&attestors, PROVEN_WEIGHT, k, q, &message, &att_root, &att_tree).unwrap();

    // VERIFIER
    verifier(&compact_cert_proof, PROVEN_WEIGHT, k, q, &message, attestors.len(), att_root);
    */
    println!("Verification Successful!")
}
