/-
  OwnedCounter: Demonstrating pattern composition

  This contract shows:
  - Combining Owned and Counter patterns
  - Owner-controlled counter operations
  - Multiple storage slots (owner Address + count Uint256)
  - Access control on state updates
  - Pattern composition without interference

  Pattern: Composition of ownership and arithmetic
-/

import Verity.Core
import Verity.EVM.Uint256

namespace Verity.Examples.OwnedCounter

open Verity
open Verity.EVM.Uint256

-- Storage layout
def owner : StorageSlot Address := ⟨0⟩
def count : StorageSlot Uint256 := ⟨1⟩

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

-- Increment the counter (owner-only, with EVM modular arithmetic)
def increment : Contract Unit := do
  onlyOwner
  let current ← getStorage count
  setStorage count (add current 1)

-- Decrement the counter (owner-only, with EVM modular arithmetic)
def decrement : Contract Unit := do
  onlyOwner
  let current ← getStorage count
  setStorage count (sub current 1)

-- Get the current count (public read)
def getCount : Contract Uint256 := do
  getStorage count

-- Get current owner (public read)
def getOwner : Contract Address := do
  getStorageAddr owner

-- Transfer ownership (owner-only)
def transferOwnership (newOwner : Address) : Contract Unit := do
  onlyOwner
  setStorageAddr owner newOwner

-- Example: Initialize with Alice, increment twice, transfer to Bob, try to increment
def exampleUsage : Contract (Uint256 × Address) := do
  constructor 0xA11CE
  increment
  increment
  transferOwnership 0xB0B
  -- Note: Next increment would fail if caller is still Alice
  -- But in this example context, we just read the final state
  let finalCount ← getCount
  let finalOwner ← getOwner
  return (finalCount, finalOwner)

#eval (exampleUsage.run { defaultState with
  sender := 0xA11CE,  -- Alice is the caller
  thisAddress := 0xC0437AC7
}).getValue?
-- Expected output: some (2, 0xB0B)

end Verity.Examples.OwnedCounter
