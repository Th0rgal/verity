/-
  Ledger: Demonstrates mapping storage pattern

  This contract shows how to use mappings (Address → Uint256) for
  tracking balances per address. It implements basic deposit,
  withdraw, and transfer operations.
-/

import DumbContracts.Core

namespace DumbContracts.Examples.Ledger

open DumbContracts

-- Storage: balances mapping (Address → Uint256)
def balances : StorageSlot (Address → Uint256) := ⟨0⟩

-- Deposit: add to caller's balance
def deposit (amount : Uint256) : Contract Unit := do
  let sender ← msgSender
  let currentBalance ← getMapping balances sender
  setMapping balances sender (currentBalance + amount)

-- Withdraw: subtract from caller's balance (with safety check)
def withdraw (amount : Uint256) : Contract Unit := do
  let sender ← msgSender
  let currentBalance ← getMapping balances sender
  require (currentBalance >= amount) "Insufficient balance"
  setMapping balances sender (currentBalance - amount)

-- Transfer: move balance from caller to another address
def transfer (to : Address) (amount : Uint256) : Contract Unit := do
  let sender ← msgSender
  let senderBalance ← getMapping balances sender
  require (senderBalance >= amount) "Insufficient balance"

  let recipientBalance ← getMapping balances to
  setMapping balances sender (senderBalance - amount)
  setMapping balances to (recipientBalance + amount)

-- Get balance of any address
def getBalance (addr : Address) : Contract Uint256 := do
  getMapping balances addr

-- Example usage: Alice deposits 100, withdraws 30, transfers 50 to Bob
def exampleUsage : Contract (Uint256 × Uint256) := do
  -- Alice deposits 100
  deposit 100

  -- Alice withdraws 30 (balance: 70)
  withdraw 30

  -- Alice transfers 50 to Bob (Alice: 20, Bob: 50)
  transfer "0xBob" 50

  -- Return both balances
  let aliceBalance ← getBalance "0xAlice"
  let bobBalance ← getBalance "0xBob"
  return (aliceBalance, bobBalance)

-- Evaluate the example
#eval (exampleUsage.run {
  storage := fun _ => 0,
  storageAddr := fun _ => "",
  storageMap := fun _ _ => 0,
  sender := "0xAlice",
  thisAddress := "0xLedger"
}).getValue?
-- Expected output: some (20, 50) - Alice has 20, Bob has 50

end DumbContracts.Examples.Ledger
