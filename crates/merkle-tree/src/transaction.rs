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
            if proof_node.hash::<H>() != expected_hash {
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
    use pathfinder_common::hash::{PedersenHash, PoseidonHash};

    use super::*;

    #[test]
    fn test_commitment_merkle_tree_1() {
        // tests/test_block_rpc.py Testing block 99709...
        // protocol_version='0.13.2'
        // tx_hash_hex='0x3ad5b36aebddd41f7a940f661524b8b1a7f9122ecc32c3787fe1d3d505832b0'
        // tx_hash_hex='0x60ce1ec3185e1e518f1927d912391c854d0691e8fcc8c7e869f28d4e1bde18f'
        // tx_hash_hex='0x143ca81e68f9396b25b2fb5b1c6d12f8b21bae293cd6884bc4d0cae2c17d7ad'
        // tx_hash_hex='0x4b7ea705cf636d247ab13eb690dd31358cf69e75c06f39ba177ac55d18a9661'
        // tx_hash_hex='0x4ff941e616e9bee6bc6e6aaed4858808c025b33a8b4aa1c6cf532573e6e7bb9'
        // tx_commit_hex='0x2b03aaba363cb9ae391fd4cfc5f7041f057fc912560f7d84915fa52e8bbe33'

        let mut tree: TransactionOrEventTree<PoseidonHash> = Default::default();

        let key1 = 0_u64.to_be_bytes().view_bits().to_owned(); // 0b01
        let key2 = 1_u64.to_be_bytes().view_bits().to_owned(); // 0b01
        let key3 = 2_u64.to_be_bytes().view_bits().to_owned(); // 0b01
        let key4 = 3_u64.to_be_bytes().view_bits().to_owned(); // 0b01
        let key5 = 4_u64.to_be_bytes().view_bits().to_owned(); // 0b01
                                                               // let keys = vec![key1.as_bitslice(), key2.as_bitslice()];

        let value_1 = felt!("0x3ad5b36aebddd41f7a940f661524b8b1a7f9122ecc32c3787fe1d3d505832b0");
        let value_2 = felt!("0x60ce1ec3185e1e518f1927d912391c854d0691e8fcc8c7e869f28d4e1bde18f");
        let value_3 = felt!("0x143ca81e68f9396b25b2fb5b1c6d12f8b21bae293cd6884bc4d0cae2c17d7ad");
        let value_4 = felt!("0x4b7ea705cf636d247ab13eb690dd31358cf69e75c06f39ba177ac55d18a9661");
        let value_5 = felt!("0x4ff941e616e9bee6bc6e6aaed4858808c025b33a8b4aa1c6cf532573e6e7bb9");

        tree.set(key1.clone(), value_1).unwrap();
        tree.set(key2.clone(), value_2).unwrap();
        tree.set(key3.clone(), value_3).unwrap();
        tree.set(key4.clone(), value_4).unwrap();
        tree.set(key5.clone(), value_5).unwrap();

        let (root, root_idx) = tree.commit().unwrap();
        // 0x002B03AABA363CB9AE391FD4CFC5F7041F057FC912560F7D84915FA52E8BBE33
        println!("{:?}", root);
        // 5
        println!("{:?}", root_idx);
        println!("stoage {:?}", tree.storage);

        // assert_eq!(expected_root_hash, root);
        // let key = Felt::from_u64(1);
        // let value = Felt::from_u64(2);
        let proof = tree.get_proof(root_idx, key1.clone()).unwrap().unwrap();
        println!("{:?}", proof);
        let mem =
            TransactionOrEventTree::<PoseidonHash>::verify_proof(root, &key1, value_1, &proof);
        println!("{:?}", mem);

        let mem =
            TransactionOrEventTree::<PoseidonHash>::verify_proof(root, &key1, value_2, &proof);
        println!("{:?}", mem);

        let key7 = felt!("0xabc").view_bits().to_owned(); // 0b01

        let mem =
            TransactionOrEventTree::<PoseidonHash>::verify_proof(root, &key7, value_2, &proof);
        println!("{:?}", mem);
    }

    #[test]
    fn test_commitment_merkle_tree() {
        // tests/test_block_rpc.py Testing block 99708...
        // protocol_version='0.13.2'
        // tx_hash_hex='0x3b0a986bb600b0321f793ae02ba6b5e67b60f929858692ce6090ef3478171b4'
        // tx_hash_hex='0x5d6dad4d216a82d9ba1e36a253acf42c7d59fcad28c1fd88b33631e5f727eb6'
        // tx_hash_hex='0x3e5d4de97db501efa25ed734cacfef078f98f765c689708a4cb72d85693610'
        // tx_hash_hex='0x503e5883a44cb2a2df8751b2943d05b95b50e1ba41beec4013b23889476e2ae'

        // tx_commit_hex='0x6b58f9c5d621e72bfce120f8bb5b2cf0d7cd2ec0b6539c93bee7bf0281420e9'

        let mut tree: TransactionOrEventTree<PoseidonHash> = Default::default();

        let key1 = 0_u64.to_be_bytes().view_bits().to_owned(); // 0b01
        let key2 = 1_u64.to_be_bytes().view_bits().to_owned(); // 0b01
        let key3 = 2_u64.to_be_bytes().view_bits().to_owned(); // 0b01
        let key4 = 3_u64.to_be_bytes().view_bits().to_owned(); // 0b01

        // let keys = vec![key1.as_bitslice(), key2.as_bitslice()];

        let value_1 = felt!("0x3b0a986bb600b0321f793ae02ba6b5e67b60f929858692ce6090ef3478171b4");
        let value_2 = felt!("0x5d6dad4d216a82d9ba1e36a253acf42c7d59fcad28c1fd88b33631e5f727eb6");
        let value_3 = felt!("0x3e5d4de97db501efa25ed734cacfef078f98f765c689708a4cb72d85693610");
        let value_4 = felt!("0x503e5883a44cb2a2df8751b2943d05b95b50e1ba41beec4013b23889476e2ae");

        tree.set(key1.clone(), value_1).unwrap();
        tree.set(key2.clone(), value_2).unwrap();
        tree.set(key3.clone(), value_3).unwrap();
        tree.set(key4.clone(), value_4).unwrap();

        let (root, root_idx) = tree.commit().unwrap();
        // 0x06B58F9C5D621E72BFCE120F8BB5B2CF0D7CD2EC0B6539C93BEE7BF0281420E9
        println!("{:?}", root);
        // 3
        println!("{:?}", root_idx);
        println!("stoage {:?}", tree.storage);

        // assert_eq!(expected_root_hash, root);
        // let key = Felt::from_u64(1);
        // let value = Felt::from_u64(2);
        let proof = tree.get_proof(root_idx, key1.clone()).unwrap().unwrap();
        println!("{:?}", proof);
        let mem =
            TransactionOrEventTree::<PoseidonHash>::verify_proof(root, &key1, value_1, &proof);
        println!("{:?}", mem);

        let mem =
            TransactionOrEventTree::<PoseidonHash>::verify_proof(root, &key1, value_2, &proof);
        println!("{:?}", mem);

        let key7 = felt!("0xabc").view_bits().to_owned(); // 0b01

        let mem =
            TransactionOrEventTree::<PoseidonHash>::verify_proof(root, &key7, value_2, &proof);
        println!("{:?}", mem);
    }

    #[test]
    fn test_tx_commitment_merkle_tree() {
        let mut tree: TransactionOrEventTree<PedersenHash> = Default::default();

        for (idx, hash) in [1u64, 2, 3, 4].into_iter().enumerate() {
            let hash = Felt::from(hash);
            let idx: u64 = idx.try_into().unwrap();
            let key = idx.to_be_bytes().view_bits().to_owned();
            tree.set(key, hash).unwrap();
        }

        // produced by the cairo-lang Python implementation:
        // `hex(asyncio.run(calculate_patricia_root([1, 2, 3, 4], height=64,
        // ffc=ffc))))`
        let expected_root_hash =
            felt!("0x1a0e579b6b444769e4626331230b5ae39bd880f47e703b73fa56bf77e52e461");
        let computed_root_hash = tree.commit().unwrap().0;

        assert_eq!(expected_root_hash, computed_root_hash);
    }
}
