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
                let sender := caller()
                let amount := calldataload(4)
                let current := sload(mappingSlot(0, sender))
                sstore(mappingSlot(0, sender), add(current, amount))
                stop()
            }
            case 0x2e1a7d4d {
                /* withdraw() */
                let sender := caller()
                let amount := calldataload(4)
                let current := sload(mappingSlot(0, sender))
                if lt(current, amount) {
                    revert(0, 0)
                }
                sstore(mappingSlot(0, sender), sub(current, amount))
                stop()
            }
            case 0xa9059cbb {
                /* transfer() */
                let sender := caller()
                let to := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                let amount := calldataload(36)
                let senderBal := sload(mappingSlot(0, sender))
                if lt(senderBal, amount) {
                    revert(0, 0)
                }
                let recipientBal := sload(mappingSlot(0, to))
                sstore(mappingSlot(0, sender), sub(senderBal, amount))
                sstore(mappingSlot(0, to), add(recipientBal, amount))
                stop()
            }
            case 0xf8b2cb4f {
                /* getBalance() */
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