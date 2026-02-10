/-
  SimpleToken: Demonstrates pattern composition with mappings

  This contract shows:
  - Combining Owned (access control) + Ledger (balances mapping) patterns
  - Owner-controlled minting
  - Public transfer operations
  - Total supply tracking
  - Pattern composition with mappings works seamlessly

  Pattern: Token contract (ERC20-like, minimal)
-/

import DumbContracts.Core

namespace DumbContracts.Examples.SimpleToken

open DumbContracts

-- Storage layout
def owner : StorageSlot Address := ⟨0⟩
def balances : StorageSlot (Address → Uint256) := ⟨1⟩
def totalSupply : StorageSlot Uint256 := ⟨2⟩

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
  setStorage totalSupply 0

-- Mint tokens to an address (owner-only)
def mint (to : Address) (amount : Uint256) : Contract Unit := do
  onlyOwner
  let currentBalance ← getMapping balances to
  setMapping balances to (currentBalance + amount)
  let currentSupply ← getStorage totalSupply
  setStorage totalSupply (currentSupply + amount)

-- Transfer tokens from caller to another address
def transfer (to : Address) (amount : Uint256) : Contract Unit := do
  let sender ← msgSender
  let senderBalance ← getMapping balances sender
  require (senderBalance >= amount) "Insufficient balance"

  let recipientBalance ← getMapping balances to
  setMapping balances sender (senderBalance - amount)
  setMapping balances to (recipientBalance + amount)

-- Get balance of an address
def balanceOf (addr : Address) : Contract Uint256 := do
  getMapping balances addr

-- Get total supply
def getTotalSupply : Contract Uint256 := do
  getStorage totalSupply

-- Get current owner
def getOwner : Contract Address := do
  getStorageAddr owner

-- Example usage: Alice creates token, mints 1000 to herself, transfers 300 to Bob
def exampleUsage : Contract (Uint256 × Uint256 × Uint256) := do
  constructor "0xAlice"

  -- Alice mints 1000 tokens to herself
  mint "0xAlice" 1000

  -- Alice transfers 300 to Bob
  transfer "0xBob" 300

  -- Return: (Alice balance, Bob balance, total supply)
  let aliceBalance ← balanceOf "0xAlice"
  let bobBalance ← balanceOf "0xBob"
  let supply ← getTotalSupply
  return (aliceBalance, bobBalance, supply)

-- Evaluate the example
#eval (exampleUsage.run {
  storage := fun _ => 0,
  storageAddr := fun _ => "",
  storageMap := fun _ _ => 0,
  sender := "0xAlice",
  thisAddress := "0xSimpleToken"
}).getValue?
-- Expected output: some (700, 300, 1000) - Alice: 700, Bob: 300, supply: 1000

end DumbContracts.Examples.SimpleToken
