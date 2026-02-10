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
                let value := calldataload(4)
                sstore(0, value)
                stop()
            }
            case 0x2e64cec1 {
                /* retrieve() */
                mstore(0, sload(0))
                return(0, 32)
            }
            default {
                revert(0, 0)
            }
        }
    }
}