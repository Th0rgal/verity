/-
  SafeCounter: Demonstrating safe arithmetic operations

  This contract shows:
  - Using stdlib Math.safeAdd and Math.safeSub
  - Checked arithmetic that prevents overflow/underflow
  - Handling Option results from safe operations
  - requireSome helper for clean error handling

  Pattern: Safe arithmetic with overflow/underflow protection
-/

import Verity.Core
import Verity.Stdlib.Math

namespace Verity.Examples.SafeCounter

open Verity
open Verity.Stdlib.Math

-- Storage layout
def count : StorageSlot Uint256 := ⟨0⟩

-- Increment the counter by 1 (with overflow check)
def increment : Contract Unit := do
  let current ← getStorage count
  let newCount ← requireSomeUint (safeAdd current 1) "Overflow in increment"
  setStorage count newCount

-- Decrement the counter by 1 (with underflow check)
def decrement : Contract Unit := do
  let current ← getStorage count
  let newCount ← requireSomeUint (safeSub current 1) "Underflow in decrement"
  setStorage count newCount

-- Get the current count
def getCount : Contract Uint256 := do
  getStorage count

-- Example: Increment twice, decrement once
def exampleUsage : Contract Uint256 := do
  increment
  increment
  decrement
  getCount

#eval (exampleUsage.run { defaultState with
  sender := 0xA11CE,
  thisAddress := 0x5AFE
}).getValue?
-- Expected output: some 1

end Verity.Examples.SafeCounter
