object "Owned" {
    code {
        let argsOffset := sub(codesize(), 32)
        codecopy(0, argsOffset, 32)
        let initialOwner := and(mload(0), 0xffffffffffffffffffffffffffffffffffffffff)
        sstore(0, initialOwner)
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        return(0, datasize("runtime"))
    }
    object "runtime" {
        code {
            switch shr(224, calldataload(0))
            case 0xf2fde38b {
                /* transferOwnership() */
                if iszero(eq(caller(), sload(0))) {
                    revert(0, 0)
                }
                let newOwner := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                sstore(0, newOwner)
                stop()
            }
            case 0x893d20e8 {
                /* getOwner() */
                mstore(0, sload(0))
                return(0, 32)
            }
            default {
                revert(0, 0)
            }
        }
    }
}