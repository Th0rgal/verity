object "SafeCounter" {
    code {
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        return(0, datasize("runtime"))
    }
    object "runtime" {
        code {
            switch shr(224, calldataload(0))
            case 0xd09de08a {
                /* increment() */
                let count := sload(0)
                if iszero(gt(add(count, 1), count)) {
                    revert(0, 0)
                }
                sstore(0, add(count, 1))
                stop()
            }
            case 0x2baeceb7 {
                /* decrement() */
                let count := sload(0)
                if lt(count, 1) {
                    revert(0, 0)
                }
                sstore(0, sub(count, 1))
                stop()
            }
            case 0xa87d942c {
                /* getCount() */
                mstore(0, sload(0))
                return(0, 32)
            }
            default {
                revert(0, 0)
            }
        }
    }
}