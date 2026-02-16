object "Owned" {
    code {
        let argsOffset := sub(codesize(), 32)
        codecopy(0, argsOffset, 32)
        let arg0 := and(mload(0), 0xffffffffffffffffffffffffffffffffffffffff)
        sstore(0, arg0)
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        return(0, datasize("runtime"))
    }
    object "runtime" {
        code {
            switch shr(224, calldataload(0))
            case 0xf2fde38b {
                /* transferOwnership() */
                if callvalue() {
                    revert(0, 0)
                }
                if lt(calldatasize(), 36) {
                    revert(0, 0)
                }
                let newOwner := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                if iszero(eq(caller(), sload(0))) {
                    mstore(0, 0x8c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 9)
                    mstore(68, 0x4e6f74206f776e65720000000000000000000000000000000000000000000000)
                    revert(0, 100)
                }
                sstore(0, newOwner)
                stop()
            }
            case 0x893d20e8 {
                /* getOwner() */
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