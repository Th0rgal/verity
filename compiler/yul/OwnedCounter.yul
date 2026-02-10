object "OwnedCounter" {
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
            case 0xd09de08a {
                /* increment() */
                if iszero(eq(caller(), sload(0))) {
                    revert(0, 0)
                }
                let current := sload(1)
                sstore(1, add(current, 1))
                stop()
            }
            case 0x2baeceb7 {
                /* decrement() */
                if iszero(eq(caller(), sload(0))) {
                    revert(0, 0)
                }
                let current := sload(1)
                sstore(1, sub(current, 1))
                stop()
            }
            case 0xa87d942c {
                /* getCount() */
                mstore(0, sload(1))
                return(0, 32)
            }
            case 0x893d20e8 {
                /* getOwner() */
                mstore(0, sload(0))
                return(0, 32)
            }
            case 0xf2fde38b {
                /* transferOwnership() */
                if iszero(eq(caller(), sload(0))) {
                    revert(0, 0)
                }
                let newOwner := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                sstore(0, newOwner)
                stop()
            }
            default {
                revert(0, 0)
            }
        }
    }
}