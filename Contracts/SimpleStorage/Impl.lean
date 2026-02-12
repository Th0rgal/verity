/-
  SimpleStorage: The "Hello World" of smart contracts

  This contract demonstrates:
  - Basic storage (one uint256 value)
  - A setter function
  - A getter function

  Pattern: Simplest possible stateful contract
-/

import DumbContracts.Core

namespace Contracts.SimpleStorage

open DumbContracts

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

#eval (exampleUsage.run {
  storage := fun _ => 0,
  storageAddr := fun _ => "",
  storageMap := fun _ _ => 0,
  storageMapAddr := fun _ _ => "",
  sender := "0xAlice",
  thisAddress := "0xContract",
  msgValue := 0,
  blockTimestamp := 0
}).getValue?
-- Expected output: some 42

end Contracts.SimpleStorage
