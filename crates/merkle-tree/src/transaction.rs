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
    pub storage: StatelessStorage,
}

impl<H: FeltHash> Default for TransactionOrEventTree<H> {
    fn default() -> Self {
        Self {
            tree: MerkleTree::empty(),
            storage: Default::default(),
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
    pub fn set(&mut self, key: BitVec<u8, Msb0>, value: Felt) -> anyhow::Result<()> {
        self.tree.set(&self.storage, key, value)
    }

    pub fn commit(&mut self) -> anyhow::Result<(Felt, u64)> {
        let update = commit_and_persist(&self.tree, &mut self.storage);
        Ok(update)
    }

    pub fn get_proof(
        &self,
        root_idx: u64,
        key: BitVec<u8, Msb0>,
    ) -> anyhow::Result<Option<Vec<TrieNode>>> {
        MerkleTree::<H, 64>::get_proof(root_idx, &self.storage, &key)
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
    tree: &MerkleTree<H, HEIGHT>,
    storage: &mut StatelessStorage,
) -> (Felt, u64) {
    for (key, value) in &tree.leaves {
        println!("key :{:?}, value:{:?}", key, value);
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

        let key1 = felt!("0x0").view_bits().to_owned(); // 0b01
        let key2 = felt!("0x1").view_bits().to_owned(); // 0b01
        let key3 = felt!("0x2").view_bits().to_owned(); // 0b01
        let key4 = felt!("0x3").view_bits().to_owned(); // 0b01
        let key5 = felt!("0x4").view_bits().to_owned(); // 0b01
        let key6 = felt!("0x5").view_bits().to_owned(); // 0b01
        let key7 = felt!("0x6").view_bits().to_owned(); // 0b01
        let key8 = felt!("0x7").view_bits().to_owned(); // 0b01
        let key9 = felt!("0x8").view_bits().to_owned(); // 0b01
        let key10 = felt!("0x9").view_bits().to_owned(); // 0b01
        let key11 = felt!("0xa").view_bits().to_owned(); // 0b01
        let key12 = felt!("0xb").view_bits().to_owned(); // 0b01
        let key13 = felt!("0xc").view_bits().to_owned(); // 0b01
        let key14 = felt!("0xd").view_bits().to_owned(); // 0b01
        let key15 = felt!("0xe").view_bits().to_owned(); // 0b01
        let key16 = felt!("0xf").view_bits().to_owned(); // 0b01
        let key17 = felt!("0x10").view_bits().to_owned(); // 0b01

        // let keys = vec![key1.as_bitslice(), key2.as_bitslice()];

        let value_1 = felt!("0x7ddafca73b3f2c36ca920b34f3536fdbe876511b9d582a1127fa0780977c257");
        let value_2 = felt!("0x4ecbdbef65a58c90abf2d03ae9dc6c66ad4331bccd098a16f8dd6a0976152f4");
        let value_3 = felt!("0x53222976c5360d0b9f0380f4a8b2a0f135540eb64eb021113282b4d519df2cf");
        let value_4 = felt!("0x39c8f931e51038872c7a2650a68c388e9b6abd268ea710a950f845119e2f0bb");
        let value_5 = felt!("0x696713c5328e75e97f2fa60fc6296c84def311b1bace7e19571efc58801efc0");
        let value_6 = felt!("0x7553ae1155d78c96ca1bf14ff36e283ae56e1d23c4c64c61c250b5c67a3c564");
        let value_7 = felt!("0x5f26a24b17932cc85462d1e6272d9e7bce6db27640884e64582253580a57a1a");
        let value_8 = felt!("0xfb1f8879a89f5fed0cfa2848cf77ad940d1c9e2a5a8dd3b41075c96dee3141");
        let value_9 = felt!("0x4ba17bc1bde8b5412ad0c3bad9ee89d9a00e373568b9097a289f045cad83b41");
        let value_10 = felt!("0x506cd52babd14d4386c50053324777fb6245f43da25162bb99decef0e9a2ec7");
        let value_11 = felt!("0x6f8f0dfb7dfc1f9a4ff37680cfc41d0fdc3f57bfcd0d1a88310cf44b6675ed3");
        let value_12 = felt!("0x3d7e6dbb27dad9327640e4ae7e373186e3c01e05a24d621eb106845a68a1e");
        let value_13 = felt!("0x62d36d3c9cc8e499276632bb9d3d428d28665243f722f3d5071c48b2c1ff3a1");
        let value_14 = felt!("0x6c7b8f6526d8d345a39bae9d78f73168491eedb2d9c46430c831d0705e1b777");
        let value_15 = felt!("0x79a1896bd14b45593d6d788e9c43f8fb5a8e66c07dccf85cbbb21b4b03b44da");
        let value_16 = felt!("0x187d9280d359b6babad05ae9ae1549231c0eb8ef084ea7500b04c74aa7bf945");
        let value_17 = felt!("0x4c9792370f39c29ca3643c80a8903b31db675cfcc86970c868652e7dd6f139b");

        tree.set(key1.clone(), value_1).unwrap();
        tree.set(key2.clone(), value_2).unwrap();
        tree.set(key3.clone(), value_3).unwrap();
        tree.set(key4.clone(), value_4).unwrap();
        tree.set(key5.clone(), value_5).unwrap();
        tree.set(key6.clone(), value_6).unwrap();
        tree.set(key7.clone(), value_7).unwrap();
        tree.set(key8.clone(), value_8).unwrap();
        tree.set(key9.clone(), value_9).unwrap();
        tree.set(key10.clone(), value_10).unwrap();
        tree.set(key11.clone(), value_11).unwrap();
        tree.set(key12.clone(), value_12).unwrap();
        tree.set(key13.clone(), value_13).unwrap();
        tree.set(key14.clone(), value_14).unwrap();
        tree.set(key15.clone(), value_15).unwrap();
        tree.set(key16.clone(), value_16).unwrap();
        tree.set(key17.clone(), value_17).unwrap();

        // produced by the cairo-lang Python implementation:
        // `hex(asyncio.run(calculate_patricia_root([1, 2, 3, 4], height=64,
        // ffc=ffc))))`
        // let expected_root_hash =
        //     felt!("0x1a0e579b6b444769e4626331230b5ae39bd880f47e703b73fa56bf77e52e461");
        let (root, root_idx) = tree.commit().unwrap();
        println!("{:?}", root);
        println!("{:?}", root_idx);
        println!("stoage {:?}", tree.storage);

        // assert_eq!(expected_root_hash, root);
        // let key = Felt::from_u64(1);
        // let value = Felt::from_u64(2);
        let proof = tree.get_proof(root_idx, key1.clone()).unwrap().unwrap();
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
