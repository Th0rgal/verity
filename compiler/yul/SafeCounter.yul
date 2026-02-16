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
                if callvalue() {
                    revert(0, 0)
                }
                if lt(calldatasize(), 4) {
                    revert(0, 0)
                }
                let count := sload(0)
                let newCount := add(count, 1)
                if iszero(gt(newCount, count)) {
                    mstore(0, 0x8c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 21)
                    mstore(68, 0x4f766572666c6f7720696e20696e6372656d656e740000000000000000000000)
                    revert(0, 100)
                }
                sstore(0, newCount)
                stop()
            }
            case 0x2baeceb7 {
                /* decrement() */
                if callvalue() {
                    revert(0, 0)
                }
                if lt(calldatasize(), 4) {
                    revert(0, 0)
                }
                let count := sload(0)
                if lt(count, 1) {
                    mstore(0, 0x8c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 22)
                    mstore(68, 0x556e646572666c6f7720696e2064656372656d656e7400000000000000000000)
                    revert(0, 100)
                }
                sstore(0, sub(count, 1))
                stop()
            }
            case 0xa87d942c {
                /* getCount() */
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