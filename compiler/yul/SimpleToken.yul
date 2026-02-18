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
                if callvalue() {
                    revert(0, 0)
                }
                if lt(calldatasize(), 68) {
                    revert(0, 0)
                }
                let to := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                let amount := calldataload(36)
                if iszero(eq(caller(), sload(0))) {
                    mstore(0, 0x8c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 9)
                    mstore(68, 0x4e6f74206f776e65720000000000000000000000000000000000000000000000)
                    revert(0, 100)
                }
                let recipientBal := sload(mappingSlot(1, to))
                let newBalance := add(recipientBal, amount)
                if lt(newBalance, recipientBal) {
                    mstore(0, 0x8c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 16)
                    mstore(68, 0x42616c616e6365206f766572666c6f7700000000000000000000000000000000)
                    revert(0, 100)
                }
                let supply := sload(2)
                let newSupply := add(supply, amount)
                if lt(newSupply, supply) {
                    mstore(0, 0x8c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 15)
                    mstore(68, 0x537570706c79206f766572666c6f770000000000000000000000000000000000)
                    revert(0, 100)
                }
                sstore(mappingSlot(1, to), newBalance)
                sstore(2, newSupply)
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
                let senderBal := sload(mappingSlot(1, caller()))
                let recipientBal := sload(mappingSlot(1, to))
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
                sstore(mappingSlot(1, caller()), sub(senderBal, amountDelta))
                sstore(mappingSlot(1, to), newRecipientBal)
                stop()
            }
            case 0x70a08231 {
                /* balanceOf() */
                if callvalue() {
                    revert(0, 0)
                }
                if lt(calldatasize(), 36) {
                    revert(0, 0)
                }
                let addr := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                mstore(0, sload(mappingSlot(1, addr)))
                return(0, 32)
            }
            case 0x18160ddd {
                /* totalSupply() */
                if callvalue() {
                    revert(0, 0)
                }
                if lt(calldatasize(), 4) {
                    revert(0, 0)
                }
                mstore(0, sload(2))
                return(0, 32)
            }
            case 0x8da5cb5b {
                /* owner() */
                if callvalue() {
                    revert(0, 0)
                }
                if lt(calldatasize(), 4) {
                    revert(0, 0)
                }
                mstore(0, sload(0))
                return(0, 32)
            }
            default {
                revert(0, 0)
            }
        }
    }
}