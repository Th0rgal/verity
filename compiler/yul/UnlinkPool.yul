/// @title UnlinkPool (Hand-written Yul)
/// @notice Yul implementation matching the Lean EDSL UnlinkPool semantics.
///         Same flat storage layout, same scaffolded hash/proof/merkle logic.
///
/// Storage layout:
///   Slot 0: nextLeafIndex
///   Slot 1: merkleRoot
///   Slot 2 + h: nullifierHashes[h] (1 = spent)
///   Slot 3 + r: rootSeen[r] (1 = seen)
///   Slot 4: verifierRouter
///
/// Function selectors (from `cast sig`):
///   deposit((uint256,uint256,uint256)[])                                     = 0x8695ddbb
///   transact((uint256,uint256[],uint256[],(uint256,uint256,uint256)))         = 0xe4c6c89d
///   getMerkleRoot()                                                          = 0x49590657
///   getNextLeafIndex()                                                       = 0x50e9b925
///   isNullifierSpent(uint256)                                                = 0x557b0a4c
///   isRootSeen(uint256)                                                      = 0x7885b60a

object "UnlinkPool" {
    code {
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        return(0, datasize("runtime"))
    }
    object "runtime" {
        code {
            // --- Helper: revert with Error(string) ---
            function revertMsg(offset, len) {
                // Error(string) selector = 0x08c379a0
                mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(4, 32)
                mstore(36, len)
                // Copy message from code (we use memory scratch for short messages)
                // For simplicity, store inline
                revert(0, add(68, len))
            }

            // --- Helper: insertLeaves ---
            // commitmentCount: number of commitments
            // Does NOT read commitment values (scaffolded: root = oldRoot + count)
            function insertLeaves(commitmentCount) {
                let currentRoot := sload(1)
                let newRoot := add(currentRoot, commitmentCount)
                sstore(1, newRoot)
                // mark rootSeen: slot 3 + newRoot
                sstore(add(3, newRoot), 1)
                // update nextLeafIndex
                sstore(0, add(sload(0), commitmentCount))
            }

            // --- Selector dispatch ---
            switch shr(224, calldataload(0))

            // getMerkleRoot() -> uint256
            case 0x49590657 {
                mstore(0, sload(1))
                return(0, 32)
            }

            // getNextLeafIndex() -> uint256
            case 0x50e9b925 {
                mstore(0, sload(0))
                return(0, 32)
            }

            // isNullifierSpent(uint256) -> bool
            case 0x557b0a4c {
                let nullifier := calldataload(4)
                mstore(0, eq(sload(add(2, nullifier)), 1))
                return(0, 32)
            }

            // isRootSeen(uint256) -> bool
            case 0x7885b60a {
                let root := calldataload(4)
                mstore(0, eq(sload(add(3, root)), 1))
                return(0, 32)
            }

            // deposit((uint256,uint256,uint256)[])
            // ABI: offset to array (4+0), then length, then packed Note structs (3 words each)
            case 0x8695ddbb {
                // Decode dynamic array of Note structs
                let notesOffset := add(4, calldataload(4))
                let notesLen := calldataload(notesOffset)

                // require(notes.length > 0)
                if iszero(notesLen) {
                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 34)
                    mstore(68, "Cannot deposit empty list of not")
                    mstore(100, "es")
                    revert(0, 132)
                }

                // Validate each note has amount > 0
                for { let i := 0 } lt(i, notesLen) { i := add(i, 1) } {
                    let noteBase := add(add(notesOffset, 32), mul(i, 96))
                    // Note layout: npk (32), token (32), amount (32)
                    let amount := calldataload(add(noteBase, 64))
                    if iszero(gt(amount, 0)) {
                        mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                        mstore(4, 32)
                        mstore(36, 30)
                        mstore(68, "Note amount must be positive\x00\x00")
                        revert(0, 100)
                    }
                }

                // Insert leaves (scaffolded: just update root by count)
                insertLeaves(notesLen)
                stop()
            }

            // transact((uint256,uint256[],uint256[],(uint256,uint256,uint256)))
            // ABI encoding for this struct with dynamic arrays is complex.
            // Layout:
            //   calldataload(4): offset to Transaction tuple
            //   Transaction tuple:
            //     +0:   merkleRoot (uint256)
            //     +32:  offset to nullifierHashes array (relative to tuple start)
            //     +64:  offset to newCommitments array (relative to tuple start)
            //     +96:  withdrawal.npk
            //     +128: withdrawal.token
            //     +160: withdrawal.amount
            //   nullifierHashes array: length, then elements
            //   newCommitments array: length, then elements
            case 0xe4c6c89d {
                let txnOffset := add(4, calldataload(4))

                let txnMerkleRoot := calldataload(txnOffset)

                // Decode nullifierHashes
                let nullsRelOffset := calldataload(add(txnOffset, 32))
                let nullsAbsOffset := add(txnOffset, nullsRelOffset)
                let nullsLen := calldataload(nullsAbsOffset)

                // Decode newCommitments
                let commsRelOffset := calldataload(add(txnOffset, 64))
                let commsAbsOffset := add(txnOffset, commsRelOffset)
                let commsLen := calldataload(commsAbsOffset)

                // Decode withdrawal Note (inline, 3 words)
                let wNpk := calldataload(add(txnOffset, 96))
                let wToken := calldataload(add(txnOffset, 128))
                let wAmount := calldataload(add(txnOffset, 160))

                // require(nullifierHashes.length > 0)
                if iszero(nullsLen) {
                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 30)
                    mstore(68, "Must spend at least one note\x00\x00")
                    revert(0, 100)
                }

                // require(newCommitments.length > 0)
                if iszero(commsLen) {
                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 35)
                    mstore(68, "Must have at least one commitmen")
                    mstore(100, "t\x00\x00")
                    revert(0, 132)
                }

                // require(nullifierHashes.length <= 16)
                if gt(nullsLen, 16) {
                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 30)
                    mstore(68, "Too many input notes (max 16)\x00\x00")
                    revert(0, 100)
                }

                // require(newCommitments.length <= 16)
                if gt(commsLen, 16) {
                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 31)
                    mstore(68, "Too many output notes (max 16)\x00")
                    revert(0, 100)
                }

                // require(isRootSeen(merkleRoot))
                if iszero(eq(sload(add(3, txnMerkleRoot)), 1)) {
                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 20)
                    mstore(68, "Invalid merkle root\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00")
                    revert(0, 100)
                }

                // Withdrawal coherence check
                if gt(wAmount, 0) {
                    // hashNote = npk + token + amount
                    let withdrawalCommitment := add(add(wNpk, wToken), wAmount)
                    // last commitment
                    let lastCommIdx := sub(commsLen, 1)
                    let lastComm := calldataload(add(add(commsAbsOffset, 32), mul(lastCommIdx, 32)))
                    if iszero(eq(lastComm, withdrawalCommitment)) {
                        mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                        mstore(4, 32)
                        mstore(36, 32)
                        mstore(68, "Withdrawal commitment mismatch\x00\x00")
                        revert(0, 100)
                    }
                }

                // Check nullifiers are unspent
                for { let i := 0 } lt(i, nullsLen) { i := add(i, 1) } {
                    let nullifier := calldataload(add(add(nullsAbsOffset, 32), mul(i, 32)))
                    if eq(sload(add(2, nullifier)), 1) {
                        mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                        mstore(4, 32)
                        mstore(36, 23)
                        mstore(68, "Nullifier already spent\x00\x00\x00\x00\x00\x00\x00\x00\x00")
                        revert(0, 100)
                    }
                }

                // verifyProof: always true (scaffolded)

                // Mark nullifiers as spent
                for { let i := 0 } lt(i, nullsLen) { i := add(i, 1) } {
                    let nullifier := calldataload(add(add(nullsAbsOffset, 32), mul(i, 32)))
                    sstore(add(2, nullifier), 1)
                }

                // Insert new commitments
                insertLeaves(commsLen)
                stop()
            }

            default {
                revert(0, 0)
            }
        }
    }
}
