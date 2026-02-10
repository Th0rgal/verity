/-
  SafeCounter: Demonstrating safe arithmetic operations

  This contract shows:
  - Using stdlib Math.safeAdd and Math.safeSub
  - Checked arithmetic that prevents overflow/underflow
  - Handling Option results from safe operations
  - requireSome helper for clean error handling

  Pattern: Safe arithmetic with overflow/underflow protection
-/

import DumbContracts.Core
import DumbContracts.Stdlib.Math

namespace DumbContracts.Examples.SafeCounter

open DumbContracts
open DumbContracts.Stdlib.Math

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

#eval (exampleUsage.run {
  storage := fun _ => 0,
  storageAddr := fun _ => "",
  storageMap := fun _ _ => 0,
  sender := "0xAlice",
  thisAddress := "0xSafeCounter"
}).getValue?
-- Expected output: some 1

end DumbContracts.Examples.SafeCounter
