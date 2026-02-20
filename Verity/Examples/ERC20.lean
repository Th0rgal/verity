/-
  ERC20 (foundation scaffold):
  - balances mapping
  - allowances double mapping
  - owner-controlled minting
  - transfer / approve / transferFrom

  This module is intentionally proof-light and serves as the executable
  contract baseline for issue #69.
-/

import Verity.Core
import Verity.EVM.Uint256
import Verity.Stdlib.Math

namespace Verity.Examples.ERC20

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

-- Storage layout
def owner : StorageSlot Address := ⟨0⟩
def totalSupply : StorageSlot Uint256 := ⟨1⟩
def balances : StorageSlot (Address → Uint256) := ⟨2⟩
def allowances : StorageSlot (Address → Address → Uint256) := ⟨3⟩

-- Access-control helpers
def isOwner : Contract Bool := do
  let sender ← msgSender
  let currentOwner ← getStorageAddr owner
  return sender == currentOwner

def onlyOwner : Contract Unit := do
  let ownerCheck ← isOwner
  require ownerCheck "Caller is not the owner"

-- Constructor initializes owner and starts with zero supply.
def constructor (initialOwner : Address) : Contract Unit := do
  setStorageAddr owner initialOwner
  setStorage totalSupply 0

-- Owner-only mint with overflow checks on balance and supply.
def mint (to : Address) (amount : Uint256) : Contract Unit := do
  onlyOwner
  let currentBalance ← getMapping balances to
  let newBalance ← requireSomeUint (safeAdd currentBalance amount) "Balance overflow"
  let currentSupply ← getStorage totalSupply
  let newSupply ← requireSomeUint (safeAdd currentSupply amount) "Supply overflow"
  setMapping balances to newBalance
  setStorage totalSupply newSupply

-- EIP-20 transfer: sender -> recipient.
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

-- EIP-20 approve: owner(sender) -> spender allowance.
def approve (spender : Address) (amount : Uint256) : Contract Unit := do
  let sender ← msgSender
  setMapping2 allowances sender spender amount

-- EIP-20 transferFrom: move from `fromAddr` to `to` using sender's allowance.
def transferFrom (fromAddr to : Address) (amount : Uint256) : Contract Unit := do
  let spender ← msgSender
  let currentAllowance ← getMapping2 allowances fromAddr spender
  require (currentAllowance >= amount) "Insufficient allowance"

  let fromBalance ← getMapping balances fromAddr
  require (fromBalance >= amount) "Insufficient balance"

  if fromAddr == to then
    pure ()
  else
    let toBalance ← getMapping balances to
    let newToBalance ← requireSomeUint (safeAdd toBalance amount) "Recipient balance overflow"
    setMapping balances fromAddr (sub fromBalance amount)
    setMapping balances to newToBalance

  -- Keep MAX_UINT256 as "infinite allowance" (common ERC20 behavior).
  if currentAllowance == MAX_UINT256 then
    pure ()
  else
    setMapping2 allowances fromAddr spender (sub currentAllowance amount)

-- View helpers
def balanceOf (addr : Address) : Contract Uint256 := do
  getMapping balances addr

def allowanceOf (ownerAddr spender : Address) : Contract Uint256 := do
  getMapping2 allowances ownerAddr spender

def getTotalSupply : Contract Uint256 := do
  getStorage totalSupply

def getOwner : Contract Address := do
  getStorageAddr owner

-- Example flow: constructor + mint + approve + transferFrom.
def exampleUsage : Contract (Uint256 × Uint256 × Uint256 × Uint256) := do
  constructor 0xA11CE
  mint 0xA11CE 1000
  approve 0xA11CE 300
  transferFrom 0xA11CE 0xB0B 250

  let aliceBalance ← balanceOf 0xA11CE
  let bobBalance ← balanceOf 0xB0B
  let bobAllowance ← allowanceOf 0xA11CE 0xA11CE
  let supply ← getTotalSupply
  return (aliceBalance, bobBalance, bobAllowance, supply)

#eval! (exampleUsage.run { defaultState with
  sender := 0xA11CE,
  thisAddress := 0xE20
}).getValue?
-- Expected: some (750, 250, 50, 1000)

end Verity.Examples.ERC20
