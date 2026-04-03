object "LocalObligationMacroSmoke" {
    code {
        if callvalue() {
            revert(0, 0)
        }
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        return(0, datasize("runtime"))
    }
    object "runtime" {
        code {
            {
                let __has_selector := iszero(lt(calldatasize(), 4))
                if iszero(__has_selector) {
                    revert(0, 0)
                }
                if __has_selector {
                    switch shr(224, calldataload(0))
                    case 0xbb93e288 {
                        /* unsafeEdge() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 4) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 4) {
                            revert(0, 0)
                        }
                        stop()
                    }
                    case 0xb67b3c55 {
                        /* dischargedEdge() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let value := calldataload(4)
                        sstore(1, value)
                        mstore(0, value)
                        return(0, 32)
                    }
                    default {
                        revert(0, 0)
                    }
                }
            }
        }
    }
}