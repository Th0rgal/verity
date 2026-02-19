/-
  SimpleToken: Demonstrates pattern composition with mappings

  This contract shows:
  - Combining Owned (access control) + Ledger (balances mapping) patterns
  - Owner-controlled minting with overflow protection (safeAdd)
  - Public transfer operations with EVM modular arithmetic
  - Total supply tracking
  - Pattern composition with mappings works seamlessly

  Pattern: Token contract (ERC20-like, minimal) with EVM-compatible operations
-/

import Verity.Core
import Verity.EVM.Uint256
import Verity.Stdlib.Math

namespace Verity.Examples.SimpleToken

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

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

-- Mint tokens to an address (owner-only, with overflow protection)
-- Follows checks-before-effects: all require guards execute before state mutations,
-- so revert always carries the original (unmodified) state.
def mint (to : Address) (amount : Uint256) : Contract Unit := do
  onlyOwner
  let currentBalance ← getMapping balances to
  let newBalance ← requireSomeUint (safeAdd currentBalance amount) "Balance overflow"
  let currentSupply ← getStorage totalSupply
  let newSupply ← requireSomeUint (safeAdd currentSupply amount) "Supply overflow"
  setMapping balances to newBalance
  setStorage totalSupply newSupply

-- Transfer tokens from caller to another address (with overflow protection)
def transfer (to : Address) (amount : Uint256) : Contract Unit := do
  let sender ← msgSender
  let senderBalance ← getMapping balances sender
  require (senderBalance >= amount) "Insufficient balance"

  if sender == to then
    pure ()
  else
    let recipientBalance ← getMapping balances to
    let newRecipientBalance ← requireSomeUint (safeAdd recipientBalance amount) "Recipient balance overflow"
    setMapping balances sender (sub senderBalance amount)
    setMapping balances to newRecipientBalance

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
  constructor 0xA11CE

  -- Alice mints 1000 tokens to herself
  mint 0xA11CE 1000

  -- Alice transfers 300 to Bob
  transfer 0xB0B 300

  -- Return: (Alice balance, Bob balance, total supply)
  let aliceBalance ← balanceOf 0xA11CE
  let bobBalance ← balanceOf 0xB0B
  let supply ← getTotalSupply
  return (aliceBalance, bobBalance, supply)

-- Evaluate the example
#eval! (exampleUsage.run { defaultState with
  sender := 0xA11CE,
  thisAddress := 0x5143
}).getValue?
-- Expected output: some (700, 300, 1000) - Alice: 700, Bob: 300, supply: 1000

end Verity.Examples.SimpleToken
