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
                let current := sload(0)
                let result := add(current, 1)
                if lt(result, current) {
                    revert(0, 0)
                }
                sstore(0, result)
                stop()
            }
            case 0x2baeceb7 {
                /* decrement() */
                let current := sload(0)
                if gt(1, current) {
                    revert(0, 0)
                }
                let result := sub(current, 1)
                sstore(0, result)
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