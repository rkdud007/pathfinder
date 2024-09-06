use std::collections::HashMap;

use anyhow::Context;
use bitvec::{order::Msb0, slice::BitSlice, view::BitView};
use pathfinder_common::{
    hash::{FeltHash, PedersenHash},
    trie::TrieNode,
};
use pathfinder_crypto::Felt;
use pathfinder_storage::{Node, NodeRef, StoredNode};

use crate::{merkle_node::Direction, storage::Storage, tree::MerkleTree};

/// A [Patricia Merkle tree](MerkleTree) which can be used to calculate
/// transaction or event commitments.
///
/// The tree has a height of 64 bits and is ephemeral -- it has no persistent
/// storage. This is sensible as each event or transaction tree is confined to a
/// single starknet block i.e. each block a new event / transaction
/// tree is formed from an empty one.
///
/// More information about these commitments can be found in the Starknet [documentation](https://docs.starknet.io/documentation/architecture_and_concepts/Blocks/header/).
pub struct TransactionOrEventTree<H: FeltHash> {
    pub tree: MerkleTree<H, 64>,
}

impl<H: FeltHash> Default for TransactionOrEventTree<H> {
    fn default() -> Self {
        Self {
            tree: MerkleTree::empty(),
        }
    }
}

#[derive(Debug)]
pub enum Membership {
    Member,
    NonMember,
}

/// [Storage](crate::storage::Storage) type which always returns [None].'
#[derive(Default, Debug)]
struct StatelessStorage {
    nodes: HashMap<u64, (Felt, StoredNode)>,
    leaves: HashMap<Felt, Felt>,
    next_index: u64,
}

impl crate::storage::Storage for StatelessStorage {
    fn get(&self, index: u64) -> anyhow::Result<Option<StoredNode>> {
        Ok(self.nodes.get(&index).map(|x| x.1.clone()))
    }

    fn hash(&self, index: u64) -> anyhow::Result<Option<Felt>> {
        Ok(self.nodes.get(&index).map(|x| x.0))
    }

    fn leaf(&self, path: &BitSlice<u8, Msb0>) -> anyhow::Result<Option<Felt>> {
        let key = Felt::from_bits(path).context("Mapping path to felt")?;

        Ok(self.leaves.get(&key).cloned())
    }
}

impl<H: FeltHash> TransactionOrEventTree<H> {
    pub fn set(&mut self, storage: &impl Storage, index: u64, value: Felt) -> anyhow::Result<()> {
        let key = index.to_be_bytes().view_bits().to_owned();
        self.tree.set(storage, key, value)
    }

    // pub fn commit(&self, storage: &impl Storage) -> anyhow::Result<Felt> {
    //     for (key, value) in &self.tree.leaves {
    //         let key = Felt::from_bits(key).unwrap();
    //         storage.leaves.insert(key, *value);
    //     }

    //     let update = tree.commit(storage).unwrap();
    // }

    pub fn get_proof(
        storage: &impl Storage,
        root_idx: u64,
        key: Felt,
    ) -> anyhow::Result<Option<Vec<TrieNode>>> {
        let key = key.to_be_bytes().view_bits().to_owned();
        MerkleTree::<H, 64>::get_proof(root_idx, storage, &key)
    }

    pub fn verify_proof(
        root: Felt,
        key: Felt,
        value: Felt,
        proofs: &[TrieNode],
    ) -> Option<Membership> {
        let mut expected_hash = root;
        let mut remaining_path: &BitSlice<u8, Msb0> = key.as_be_bytes().view_bits();

        for proof_node in proofs.iter() {
            if proof_node.hash::<PedersenHash>() != expected_hash {
                return None;
            }
            match proof_node {
                TrieNode::Binary { left, right } => {
                    let direction = Direction::from(remaining_path[0]);
                    expected_hash = match direction {
                        Direction::Left => *left,
                        Direction::Right => *right,
                    };
                    remaining_path = &remaining_path[1..];
                }
                TrieNode::Edge { child, path } => {
                    if path != &remaining_path[..path.len()] {
                        return Some(Membership::NonMember);
                    }

                    expected_hash = *child;

                    remaining_path = &remaining_path[path.len()..];
                }
            }
        }

        // assert!(remaining_path.is_empty(), "Proof path should be empty");

        if expected_hash == value {
            Some(Membership::Member)
        } else {
            None
        }
    }
}

/// Commits the tree changes and persists them to storage.
fn commit_and_persist<H: FeltHash, const HEIGHT: usize>(
    tree: MerkleTree<H, HEIGHT>,
    storage: &mut StatelessStorage,
) -> (Felt, u64) {
    for (key, value) in &tree.leaves {
        let key = Felt::from_bits(key).unwrap();
        storage.leaves.insert(key, *value);
    }

    let update = tree.commit(storage).unwrap();

    let number_of_nodes_added = update.nodes_added.len() as u64;

    for (rel_index, (hash, node)) in update.nodes_added.into_iter().enumerate() {
        let node = match node {
            Node::Binary { left, right } => {
                let left = match left {
                    NodeRef::StorageIndex(idx) => idx,
                    NodeRef::Index(idx) => storage.next_index + (idx as u64),
                };

                let right = match right {
                    NodeRef::StorageIndex(idx) => idx,
                    NodeRef::Index(idx) => storage.next_index + (idx as u64),
                };

                StoredNode::Binary { left, right }
            }
            Node::Edge { child, path } => {
                let child = match child {
                    NodeRef::StorageIndex(idx) => idx,
                    NodeRef::Index(idx) => storage.next_index + (idx as u64),
                };

                StoredNode::Edge { child, path }
            }
            Node::LeafBinary => StoredNode::LeafBinary,
            Node::LeafEdge { path } => StoredNode::LeafEdge { path },
        };

        let index = storage.next_index + (rel_index as u64);

        storage.nodes.insert(index, (hash, node));
    }

    let storage_root_index = storage.next_index + number_of_nodes_added - 1;
    storage.next_index += number_of_nodes_added;

    (update.root_commitment, storage_root_index)
}

#[cfg(test)]
mod tests {
    use pathfinder_common::felt;
    use pathfinder_common::hash::PedersenHash;

    use super::*;

    #[test]
    fn test_commitment_merkle_tree() {
        let mut tree: TransactionOrEventTree<PedersenHash> = Default::default();
        let mut storage = StatelessStorage::default();

        for (idx, hash) in [1u64, 2, 3, 4].into_iter().enumerate() {
            let hash = Felt::from(hash);
            let idx: u64 = idx.try_into().unwrap();
            tree.set(&storage, idx, hash).unwrap();
        }

        // produced by the cairo-lang Python implementation:
        // `hex(asyncio.run(calculate_patricia_root([1, 2, 3, 4], height=64,
        // ffc=ffc))))`
        let expected_root_hash =
            felt!("0x1a0e579b6b444769e4626331230b5ae39bd880f47e703b73fa56bf77e52e461");
        let (root, root_idx) = commit_and_persist(tree.tree, &mut storage);

        assert_eq!(expected_root_hash, root);
        let key = Felt::from_u64(1);
        let proof = TransactionOrEventTree::<PedersenHash>::get_proof(&storage, root_idx, key)
            .unwrap()
            .unwrap();
        println!("{:?}", proof);
        let mem = TransactionOrEventTree::<PedersenHash>::verify_proof(root, key, key, &proof);
        println!("{:?}", mem);
    }
}
