/-
  SimpleStorage: The "Hello World" of smart contracts

  This contract demonstrates:
  - Basic storage (one uint256 value)
  - A setter function
  - A getter function

  Pattern: Simplest possible stateful contract
-/

import Verity.Core

namespace Verity.Examples

open Verity

-- Storage layout
def storedData : StorageSlot Uint256 := ⟨0⟩

-- Set the stored value
def store (value : Uint256) : Contract Unit := do
  setStorage storedData value

-- Get the stored value
def retrieve : Contract Uint256 := do
  getStorage storedData

-- Example: Store and retrieve
def exampleUsage : Contract Uint256 := do
  store 42
  retrieve

#eval (exampleUsage.run { defaultState with
  sender := 0xA11CE,
  thisAddress := 0xC0437AC7
}).getValue?
-- Expected output: some 42

end Verity.Examples
