object "Ledger" {
    code {
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        return(0, datasize("runtime"))
    }
    object "runtime" {
        code {
            function mappingSlot(baseSlot, key) -> slot {
                mstore(0, key)
                mstore(32, baseSlot)
                slot := keccak256(0, 64)
            }
            switch shr(224, calldataload(0))
            case 0xb6b55f25 {
                /* deposit() */
                if callvalue() {
                    revert(0, 0)
                }
                if lt(calldatasize(), 36) {
                    revert(0, 0)
                }
                let amount := calldataload(4)
                let senderBal := sload(mappingSlot(0, caller()))
                sstore(mappingSlot(0, caller()), add(senderBal, amount))
                stop()
            }
            case 0x2e1a7d4d {
                /* withdraw() */
                if callvalue() {
                    revert(0, 0)
                }
                if lt(calldatasize(), 36) {
                    revert(0, 0)
                }
                let amount := calldataload(4)
                let senderBal := sload(mappingSlot(0, caller()))
                if lt(senderBal, amount) {
                    mstore(0, 0x8c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 20)
                    mstore(68, 0x496e73756666696369656e742062616c616e6365000000000000000000000000)
                    revert(0, 100)
                }
                sstore(mappingSlot(0, caller()), sub(senderBal, amount))
                stop()
            }
            case 0xa9059cbb {
                /* transfer() */
                if callvalue() {
                    revert(0, 0)
                }
                if lt(calldatasize(), 68) {
                    revert(0, 0)
                }
                let to := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                let amount := calldataload(36)
                let senderBal := sload(mappingSlot(0, caller()))
                let recipientBal := sload(mappingSlot(0, to))
                if lt(senderBal, amount) {
                    mstore(0, 0x8c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 20)
                    mstore(68, 0x496e73756666696369656e742062616c616e6365000000000000000000000000)
                    revert(0, 100)
                }
                let sameAddr := eq(caller(), to)
                let delta := sub(1, sameAddr)
                let amountDelta := mul(amount, delta)
                let newRecipientBal := add(recipientBal, amountDelta)
                if lt(newRecipientBal, recipientBal) {
                    mstore(0, 0x8c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 26)
                    mstore(68, 0x526563697069656e742062616c616e6365206f766572666c6f77000000000000)
                    revert(0, 100)
                }
                sstore(mappingSlot(0, caller()), sub(senderBal, amountDelta))
                sstore(mappingSlot(0, to), newRecipientBal)
                stop()
            }
            case 0xf8b2cb4f {
                /* getBalance() */
                if callvalue() {
                    revert(0, 0)
                }
                if lt(calldatasize(), 36) {
                    revert(0, 0)
                }
                let addr := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                mstore(0, sload(mappingSlot(0, addr)))
                return(0, 32)
            }
            default {
                revert(0, 0)
            }
        }
    }
}