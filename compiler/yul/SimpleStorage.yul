object "SimpleStorage" {
    code {
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        return(0, datasize("runtime"))
    }
    object "runtime" {
        code {
            switch shr(224, calldataload(0))
            case 0x6057361d {
                /* store() */
                if callvalue() {
                    revert(0, 0)
                }
                if lt(calldatasize(), 36) {
                    revert(0, 0)
                }
                let value := calldataload(4)
                sstore(0, value)
                stop()
            }
            case 0x2e64cec1 {
                /* retrieve() */
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