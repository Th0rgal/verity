/-
  Ledger: Demonstrates mapping storage pattern

  This contract shows how to use mappings (Address → Uint256) for
  tracking balances per address. It implements basic deposit,
  withdraw, and transfer operations with EVM modular arithmetic.
-/

import Verity.Core
import Verity.EVM.Uint256
import Verity.Stdlib.Math

namespace Verity.Examples.Ledger

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math (safeAdd requireSomeUint)

-- Storage: balances mapping (Address → Uint256)
def balances : StorageSlot (Address → Uint256) := ⟨0⟩

-- Deposit: add to caller's balance (with EVM modular arithmetic)
def deposit (amount : Uint256) : Contract Unit := do
  let sender ← msgSender
  let currentBalance ← getMapping balances sender
  setMapping balances sender (add currentBalance amount)

-- Withdraw: subtract from caller's balance (with safety check and EVM modular arithmetic)
def withdraw (amount : Uint256) : Contract Unit := do
  let sender ← msgSender
  let currentBalance ← getMapping balances sender
  require (currentBalance >= amount) "Insufficient balance"
  setMapping balances sender (sub currentBalance amount)

-- Transfer: move balance from caller to another address (with overflow protection)
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
  transfer 0xB0B 50

  -- Return both balances
  let aliceBalance ← getBalance 0xA11CE
  let bobBalance ← getBalance 0xB0B
  return (aliceBalance, bobBalance)

-- Evaluate the example
#eval! (exampleUsage.run { defaultState with
  sender := 0xA11CE,
  thisAddress := 0x1ED6E2
}).getValue?
-- Expected output: some (20, 50) - Alice has 20, Bob has 50

end Verity.Examples.Ledger
