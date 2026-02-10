object "SimpleToken" {
    code {
        let argsOffset := sub(codesize(), 32)
        codecopy(0, argsOffset, 32)
        let arg0 := and(mload(0), 0xffffffffffffffffffffffffffffffffffffffff)
        sstore(0, arg0)
        sstore(2, 0)
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
            case 0x40c10f19 {
                /* mint() */
                let to := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                let amount := calldataload(36)
                if iszero(eq(caller(), sload(0))) {
                    revert(0, 0)
                }
                let recipientBal := sload(mappingSlot(1, to))
                let supply := sload(2)
                sstore(mappingSlot(1, to), add(recipientBal, amount))
                sstore(2, add(supply, amount))
                stop()
            }
            case 0xa9059cbb {
                /* transfer() */
                let to := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                let amount := calldataload(36)
                let senderBal := sload(mappingSlot(1, caller()))
                let recipientBal := sload(mappingSlot(1, to))
                if lt(senderBal, amount) {
                    revert(0, 0)
                }
                sstore(mappingSlot(1, caller()), sub(senderBal, amount))
                sstore(mappingSlot(1, to), add(recipientBal, amount))
                stop()
            }
            case 0x70a08231 {
                /* balanceOf() */
                let addr := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                mstore(0, sload(mappingSlot(1, addr)))
                return(0, 32)
            }
            case 0x18160ddd {
                /* totalSupply() */
                mstore(0, sload(2))
                return(0, 32)
            }
            case 0x8da5cb5b {
                /* owner() */
                mstore(0, sload(0))
                return(0, 32)
            }
            default {
                revert(0, 0)
            }
        }
    }
}