/-
  Counter: Demonstrating arithmetic operations

  This contract shows:
  - Stateful counter variable
  - Increment operation (addition with EVM modular semantics)
  - Decrement operation (subtraction with EVM modular semantics)
  - Getter for current count

  Pattern: Basic arithmetic and state updates with EVM-compatible operations
-/

import DumbContracts.Core
import DumbContracts.EVM.Uint256

namespace DumbContracts.Examples.Counter

open DumbContracts
open DumbContracts.EVM.Uint256

-- Storage layout
def count : StorageSlot Uint256 := ⟨0⟩

-- Increment the counter by 1 (with EVM modular arithmetic)
def increment : Contract Unit := do
  let current ← getStorage count
  setStorage count (add current 1)

-- Decrement the counter by 1 (with EVM modular arithmetic)
def decrement : Contract Unit := do
  let current ← getStorage count
  setStorage count (sub current 1)

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
  thisAddress := "0xCounter",
  msgValue := 0,
  blockTimestamp := 0,
  knownAddresses := fun _ => Core.FiniteAddressSet.empty
}).getValue?
-- Expected output: some 1

end DumbContracts.Examples.Counter
