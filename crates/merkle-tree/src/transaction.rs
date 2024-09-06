use std::collections::HashMap;

use anyhow::Context;
use bitvec::{order::Msb0, slice::BitSlice, vec::BitVec, view::BitView};
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
pub struct StatelessStorage {
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
    pub fn set(
        &mut self,
        storage: &impl Storage,
        key: BitVec<u8, Msb0>,
        value: Felt,
    ) -> anyhow::Result<()> {
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
        key: BitVec<u8, Msb0>,
    ) -> anyhow::Result<Option<Vec<TrieNode>>> {
        MerkleTree::<H, 64>::get_proof(root_idx, storage, &key)
    }

    pub fn verify_proof(
        root: Felt,
        key: &BitSlice<u8, Msb0>,
        value: Felt,
        proofs: &[TrieNode],
    ) -> Option<Membership> {
        // Protect from ill-formed keys
        if key.len() != 251 {
            return None;
        }

        let mut expected_hash = root;
        let mut remaining_path: &BitSlice<u8, Msb0> = key;

        for proof_node in proofs.iter() {
            // Hash mismatch? Return None.
            if proof_node.hash::<PedersenHash>() != expected_hash {
                return None;
            }
            match proof_node {
                TrieNode::Binary { left, right } => {
                    // Direction will always correspond to the 0th index
                    // because we're removing bits on every iteration.
                    let direction = Direction::from(remaining_path[0]);

                    // Set the next hash to be the left or right hash,
                    // depending on the direction
                    expected_hash = match direction {
                        Direction::Left => *left,
                        Direction::Right => *right,
                    };

                    // Advance by a single bit
                    remaining_path = &remaining_path[1..];
                }
                TrieNode::Edge { child, path } => {
                    if path != &remaining_path[..path.len()] {
                        // If paths don't match, we've found a proof of non membership because
                        // we:
                        // 1. Correctly moved towards the target insofar as is possible, and
                        // 2. hashing all the nodes along the path does result in the root hash,
                        //    which means
                        // 3. the target definitely does not exist in this tree
                        return Some(Membership::NonMember);
                    }

                    // Set the next hash to the child's hash
                    expected_hash = *child;

                    // Advance by the whole edge path
                    remaining_path = &remaining_path[path.len()..];
                }
            }
        }

        // At this point, we should reach `value` !
        if expected_hash == value {
            Some(Membership::Member)
        } else {
            // Hash mismatch. Return `None`.
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

        let key1 = felt!("0x0").view_bits().to_owned(); // 0b01
        let key2 = felt!("0x1").view_bits().to_owned(); // 0b01
        let key3 = felt!("0x2").view_bits().to_owned(); // 0b01
        let key4 = felt!("0x3").view_bits().to_owned(); // 0b01
        let key5 = felt!("0x4").view_bits().to_owned(); // 0b01
        let key6 = felt!("0x5").view_bits().to_owned(); // 0b01

        // let keys = vec![key1.as_bitslice(), key2.as_bitslice()];

        let value_1 = felt!("0x2");
        let value_2 = felt!("0x3");
        let value_3 = felt!("0x4");
        let value_4 = felt!("0x5");
        let value_5 = felt!("0x6");
        let value_6 = felt!("0x7");

        tree.set(&storage, key1.clone(), value_1).unwrap();
        tree.set(&storage, key2.clone(), value_2).unwrap();
        tree.set(&storage, key3.clone(), value_3).unwrap();
        tree.set(&storage, key4.clone(), value_4).unwrap();
        tree.set(&storage, key5.clone(), value_5).unwrap();
        tree.set(&storage, key6.clone(), value_6).unwrap();

        // produced by the cairo-lang Python implementation:
        // `hex(asyncio.run(calculate_patricia_root([1, 2, 3, 4], height=64,
        // ffc=ffc))))`
        // let expected_root_hash =
        //     felt!("0x1a0e579b6b444769e4626331230b5ae39bd880f47e703b73fa56bf77e52e461");
        let (root, root_idx) = commit_and_persist(tree.tree, &mut storage);

        // assert_eq!(expected_root_hash, root);
        // let key = Felt::from_u64(1);
        // let value = Felt::from_u64(2);
        let proof =
            TransactionOrEventTree::<PedersenHash>::get_proof(&storage, root_idx, key1.clone())
                .unwrap()
                .unwrap();
        println!("{:?}", proof);
        let mem =
            TransactionOrEventTree::<PedersenHash>::verify_proof(root, &key1, value_1, &proof);
        println!("{:?}", mem);

        let mem =
            TransactionOrEventTree::<PedersenHash>::verify_proof(root, &key1, value_2, &proof);
        println!("{:?}", mem);

        let key7 = felt!("0xabc").view_bits().to_owned(); // 0b01

        let mem =
            TransactionOrEventTree::<PedersenHash>::verify_proof(root, &key7, value_2, &proof);
        println!("{:?}", mem);
    }
}
