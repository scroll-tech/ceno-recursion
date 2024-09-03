use crate::field::Fp;
use crate::poseidon::*;

pub struct MerkleTree {
    pub depth: usize,
    pub root: Fp,
    // Layers ordered from bottom to top, excluding root
    // Within each layer, from left to right
    pub internal_nodes: Vec<Vec<Fp>>,
    pub leaves: Vec<Vec<Fp>>,
    pub leaf_hashes: Vec<Fp>,
}

pub struct MerkleProof {
    // All internal nodes on the path
    pub path: Vec<Fp>,
}

pub fn build_merkle_tree(leaves: &Vec<Vec<Fp>>) -> MerkleTree {
    // Compute hashes of leaves
    let leaf_hashes: Vec<Fp> = leaves.iter().map(|i| poseidon(&i)).collect();
    // Pad leaves with 0s
    let mut internal_nodes: Vec<Vec<Fp>> = vec![
        [
            leaf_hashes.clone(),
            vec![Fp::from(0); leaves.len().next_power_of_two() - leaves.len()]
        ].concat()
    ];
    let mut round = 0;
    while internal_nodes[round].len() > 2 {
        internal_nodes.push(Vec::new());
        for i in 0..internal_nodes[round].len() / 2 {
            let child_0 = internal_nodes[round][2 * i].clone();
            let child_1 = internal_nodes[round][2 * i + 1].clone();
            internal_nodes[round + 1].push(poseidon(&[child_0, child_1]));
        }
        round += 1;
    }
    let root = poseidon(&[internal_nodes[round][0], internal_nodes[round][1]]);
    let depth = round + 1;
    MerkleTree {
        depth,
        root,
        internal_nodes,
        leaves: leaves.clone(),
        leaf_hashes,
    }
}

pub fn prove_merkle(tree: &MerkleTree, mut index: usize) -> MerkleProof {
    assert!(index < tree.leaves.len());
    let mut path = Vec::new();
    for round in 0..tree.depth {
        path.push(tree.internal_nodes[round][index ^ 1]);
        index /= 2;
    }
    MerkleProof {
        path,
    }
}

pub fn verify_merkle(num_leaves: usize, proof: &MerkleProof, root: Fp, mut index: usize, hashed_leaf: &Fp) {
    // hash of leaf
    let mut cur_node = hashed_leaf.clone();
    // hash of internal nodes
    assert_eq!(proof.path.len().pow(2), num_leaves.next_power_of_two());
    for other_node in &proof.path {
        if index % 2 == 0 {
            cur_node = poseidon(&[cur_node, other_node.clone()]);
        } else {
            cur_node = poseidon(&[other_node.clone(), cur_node]);
        }
        index /= 2;
    }
    assert_eq!(cur_node, root);
}