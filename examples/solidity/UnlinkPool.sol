// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/**
 * @title UnlinkPool (Simplified Reference)
 * @notice Solidity implementation matching the Lean EDSL semantics exactly.
 *         Uses the same flat storage layout and simplified scaffolds (additive hash,
 *         dummy merkle root, verifyProof = true) so that behavior is bit-identical
 *         to the Lean implementation for differential testing.
 *
 * Storage layout (matches Lean EDSL):
 *   Slot 0: nextLeafIndex
 *   Slot 1: merkleRoot
 *   Slot 2 + hash: nullifierHashes mapping (1 = spent)
 *   Slot 3 + root: rootSeen mapping (1 = seen)
 *   Slot 4: verifierRouter
 */
contract UnlinkPool {
    // --- Storage (flat slots, matching Lean EDSL) ---
    // Slot 0
    uint256 public nextLeafIndex;
    // Slot 1
    uint256 public merkleRoot;

    // We use mappings that hash to slots 2+h and 3+r respectively.
    // For the Lean EDSL comparison, we use assembly to match flat slot arithmetic.

    // --- Structs ---
    struct Note {
        uint256 npk;
        uint256 token;
        uint256 amount;
    }

    struct Transaction {
        uint256 merkleRoot;
        uint256[] nullifierHashes;
        uint256[] newCommitments;
        Note withdrawal;
    }

    // --- Internal helpers (matching Lean EDSL) ---

    function _nullifierSlot(uint256 hash) internal pure returns (uint256) {
        return 2 + hash;
    }

    function _rootSeenSlot(uint256 root) internal pure returns (uint256) {
        return 3 + root;
    }

    function _sloadSlot(uint256 slot) internal view returns (uint256 val) {
        assembly { val := sload(slot) }
    }

    function _sstoreSlot(uint256 slot, uint256 val) internal {
        assembly { sstore(slot, val) }
    }

    function isNullifierSpent(uint256 nullifier) public view returns (bool) {
        return _sloadSlot(_nullifierSlot(nullifier)) == 1;
    }

    function isRootSeen(uint256 root) public view returns (bool) {
        return _sloadSlot(_rootSeenSlot(root)) == 1;
    }

    // hashNote: matches Lean EDSL placeholder (npk + token + amount)
    function hashNote(Note memory note) public pure returns (uint256) {
        return note.npk + note.token + note.amount;
    }

    // verifyProof: matches Lean EDSL placeholder (always true)
    function verifyProof(Transaction memory) public pure returns (bool) {
        return true;
    }

    // insertLeaves: matches Lean EDSL (root = oldRoot + length, mark seen, update index)
    function _insertLeaves(uint256[] memory commitments) internal {
        uint256 currentRoot = merkleRoot;
        uint256 newRoot = currentRoot + commitments.length;
        merkleRoot = newRoot;
        _sstoreSlot(_rootSeenSlot(newRoot), 1);
        nextLeafIndex = nextLeafIndex + commitments.length;
    }

    // --- Main functions (matching Lean EDSL) ---

    function deposit(Note[] calldata notes) external {
        require(notes.length > 0, "Cannot deposit empty list of notes");

        // Validate notes
        for (uint256 i = 0; i < notes.length; i++) {
            require(notes[i].amount > 0, "Note amount must be positive");
        }

        // Compute commitments
        uint256[] memory commitments = new uint256[](notes.length);
        for (uint256 i = 0; i < notes.length; i++) {
            commitments[i] = hashNote(notes[i]);
        }

        // Insert into merkle tree
        _insertLeaves(commitments);
    }

    function transact(Transaction calldata txn) external {
        // Validate inputs
        require(txn.nullifierHashes.length > 0, "Must spend at least one note");
        require(txn.newCommitments.length > 0, "Must have at least one commitment");
        require(txn.nullifierHashes.length <= 16, "Too many input notes (max 16)");
        require(txn.newCommitments.length <= 16, "Too many output notes (max 16)");

        // Verify merkle root
        require(isRootSeen(txn.merkleRoot), "Invalid merkle root");

        // Withdrawal coherence check
        if (txn.withdrawal.amount > 0) {
            uint256 withdrawalCommitment = hashNote(txn.withdrawal);
            require(
                txn.newCommitments.length > 0 &&
                txn.newCommitments[txn.newCommitments.length - 1] == withdrawalCommitment,
                "Withdrawal commitment mismatch"
            );
        }

        // Check nullifiers are unspent
        for (uint256 i = 0; i < txn.nullifierHashes.length; i++) {
            require(!isNullifierSpent(txn.nullifierHashes[i]), "Nullifier already spent");
        }

        // Verify proof (placeholder: always true)
        require(verifyProof(txn), "Invalid proof");

        // Mark nullifiers as spent
        for (uint256 i = 0; i < txn.nullifierHashes.length; i++) {
            _sstoreSlot(_nullifierSlot(txn.nullifierHashes[i]), 1);
        }

        // Insert new commitments
        _insertLeaves(txn.newCommitments);
    }

    // --- View functions ---
    function getMerkleRoot() external view returns (uint256) {
        return merkleRoot;
    }

    function getNextLeafIndex() external view returns (uint256) {
        return nextLeafIndex;
    }
}
