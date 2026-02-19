/-
  Counter: Demonstrating arithmetic operations

  This contract shows:
  - Stateful counter variable
  - Increment operation (addition with EVM modular semantics)
  - Decrement operation (subtraction with EVM modular semantics)
  - Getter for current count

  Pattern: Basic arithmetic and state updates with EVM-compatible operations
-/

import Verity.Core
import Verity.EVM.Uint256

namespace Verity.Examples.Counter

open Verity
open Verity.EVM.Uint256

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

#eval (exampleUsage.run { defaultState with
  sender := 0xA11CE,
  thisAddress := 0xC04273
}).getValue?
-- Expected output: some 1

end Verity.Examples.Counter
