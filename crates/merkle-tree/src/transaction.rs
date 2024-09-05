use bitvec::{order::Msb0, slice::BitSlice, view::BitView};
use pathfinder_common::{
    hash::{FeltHash, PedersenHash},
    trie::TrieNode,
};
use pathfinder_crypto::Felt;
use pathfinder_storage::StoredNode;

use crate::{
    merkle_node::{Direction, InternalNode},
    storage::Storage,
    tree::MerkleTree,
};

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
    tree: MerkleTree<H, 64>,
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

/// [Storage](crate::storage::Storage) type which always returns [None].
struct NullStorage;

impl crate::storage::Storage for NullStorage {
    fn get(&self, _: u64) -> anyhow::Result<Option<StoredNode>> {
        Ok(None)
    }

    fn hash(&self, _: u64) -> anyhow::Result<Option<Felt>> {
        Ok(None)
    }

    fn leaf(
        &self,
        _: &bitvec::slice::BitSlice<u8, bitvec::prelude::Msb0>,
    ) -> anyhow::Result<Option<Felt>> {
        Ok(None)
    }
}

impl<H: FeltHash> TransactionOrEventTree<H> {
    pub fn set(&mut self, index: u64, value: Felt) -> anyhow::Result<()> {
        let key = index.to_be_bytes().view_bits().to_owned();
        self.tree.set(&NullStorage {}, key, value)
    }

    pub fn commit(self) -> anyhow::Result<Felt> {
        self.tree
            .commit(&NullStorage {})
            .map(|update| update.root_commitment)
    }

    pub fn get_proof(&self, root: Felt, key: Felt) -> anyhow::Result<Option<Vec<TrieNode>>> {
        let key = key.to_be_bytes().view_bits().to_owned();
        let root = u64::from_str_radix(&root.to_hex_str(), 16).unwrap();
        MerkleTree::<H, 64>::get_proof(root, &NullStorage {}, &key)
    }

    pub fn verify_proof(
        &self,
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

        assert!(remaining_path.is_empty(), "Proof path should be empty");

        if expected_hash == value {
            Some(Membership::Member)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use pathfinder_common::felt;
    use pathfinder_common::hash::PedersenHash;

    use super::*;

    #[test]
    fn test_commitment_merkle_tree() {
        let mut tree: TransactionOrEventTree<PedersenHash> = Default::default();

        for (idx, hash) in [1u64, 2, 3, 4].into_iter().enumerate() {
            let hash = Felt::from(hash);
            let idx: u64 = idx.try_into().unwrap();
            tree.set(idx, hash).unwrap();
        }

        // produced by the cairo-lang Python implementation:
        // `hex(asyncio.run(calculate_patricia_root([1, 2, 3, 4], height=64,
        // ffc=ffc))))`
        let expected_root_hash =
            felt!("0x1a0e579b6b444769e4626331230b5ae39bd880f47e703b73fa56bf77e52e461");

        let key = Felt::from_u64(1);
        let proof = tree.get_proof(expected_root_hash, key).unwrap().unwrap();
        let mem = tree.verify_proof(expected_root_hash, key, key, &proof);
        println!("{:?}", mem);
        let computed_root_hash = tree.commit().unwrap();

        assert_eq!(expected_root_hash, computed_root_hash);
    }
}
