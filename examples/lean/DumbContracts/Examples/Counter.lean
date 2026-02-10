/-
  Counter: Demonstrating arithmetic operations

  This contract shows:
  - Stateful counter variable
  - Increment operation (addition)
  - Decrement operation (subtraction)
  - Getter for current count

  Pattern: Basic arithmetic and state updates
-/

import DumbContracts.Core

namespace DumbContracts.Examples.Counter

open DumbContracts

-- Storage layout
def count : StorageSlot Uint256 := ⟨0⟩

-- Increment the counter by 1
def increment : Contract Unit := do
  let current ← getStorage count
  setStorage count (current + 1)

-- Decrement the counter by 1
def decrement : Contract Unit := do
  let current ← getStorage count
  setStorage count (current - 1)

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
  thisAddress := "0xCounter"
}).getValue?
-- Expected output: some 1

end DumbContracts.Examples.Counter
