/-
  Owned: Demonstrating the ownership pattern

  This contract shows:
  - Owner address storage
  - Access control with onlyOwner pattern
  - Using msgSender for authentication
  - Using require for authorization checks
  - Transfer ownership functionality

  Pattern: Access control and ownership
-/

import DumbContracts.Core

namespace DumbContracts.Examples.Owned

open DumbContracts

-- Storage layout
def owner : StorageSlot Address := ⟨0⟩

-- Helper: Check if caller is owner
def isOwner : Contract Bool := do
  let sender ← msgSender
  let currentOwner ← getStorageAddr owner
  return sender == currentOwner

-- Modifier pattern: Only owner can proceed
def onlyOwner : Contract Unit := do
  let ownerCheck ← isOwner
  require ownerCheck "Caller is not the owner"

-- Initialize contract with owner
def constructor (initialOwner : Address) : Contract Unit := do
  setStorageAddr owner initialOwner

-- Transfer ownership to new address
def transferOwnership (newOwner : Address) : Contract Unit := do
  onlyOwner
  setStorageAddr owner newOwner

-- Get current owner
def getOwner : Contract Address := do
  getStorageAddr owner

-- Example: Initialize, check owner, transfer ownership
def exampleUsage : Contract Address := do
  constructor "0xAlice"
  transferOwnership "0xBob"
  getOwner

-- Note: This will evaluate in a context where msgSender is set
#eval (exampleUsage.run {
  storage := fun _ => 0,
  storageAddr := fun _ => "",
  storageMap := fun _ _ => 0,
  sender := "0xAlice",  -- Alice is the caller
  thisAddress := "0xContract"
}).getValue?
-- Expected output: some "0xBob" (after transfer)

end DumbContracts.Examples.Owned
