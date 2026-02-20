/-
  ERC721 (foundation scaffold):
  - balances mapping
  - token ownership by tokenId
  - token approvals and operator approvals

  This module provides a compile-safe executable baseline for issue #73.
-/

import Verity.Core
import Verity.EVM.Uint256
import Verity.Stdlib.Math

namespace Verity.Examples.ERC721

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

-- Storage layout
def owner : StorageSlot Address := ⟨0⟩
def totalSupply : StorageSlot Uint256 := ⟨1⟩
def nextTokenId : StorageSlot Uint256 := ⟨2⟩
def balances : StorageSlot (Address → Uint256) := ⟨3⟩
def owners : StorageSlot (Uint256 → Uint256) := ⟨4⟩
def tokenApprovals : StorageSlot (Uint256 → Uint256) := ⟨5⟩
def operatorApprovals : StorageSlot (Address → Address → Uint256) := ⟨6⟩

def addressToWord (a : Address) : Uint256 :=
  (a.toNat : Uint256)

def wordToAddress (w : Uint256) : Address :=
  Verity.Core.Address.ofNat (w : Nat)

def boolToWord (b : Bool) : Uint256 :=
  if b then 1 else 0

def isOwner : Contract Bool := do
  let sender ← msgSender
  let currentOwner ← getStorageAddr owner
  return sender == currentOwner

def onlyOwner : Contract Unit := do
  let ownerCheck ← isOwner
  require ownerCheck "Caller is not the owner"

-- Constructor initializes owner and zeroes core counters.
def constructor (initialOwner : Address) : Contract Unit := do
  setStorageAddr owner initialOwner
  setStorage totalSupply 0
  setStorage nextTokenId 0

-- Core ERC721 view helpers.
def balanceOf (addr : Address) : Contract Uint256 := do
  getMapping balances addr

def ownerOf (tokenId : Uint256) : Contract Address := do
  let ownerWord ← getMappingUint owners tokenId
  return wordToAddress ownerWord

def getApproved (tokenId : Uint256) : Contract Address := do
  let approvedWord ← getMappingUint tokenApprovals tokenId
  return wordToAddress approvedWord

def isApprovedForAll (ownerAddr operator : Address) : Contract Bool := do
  let flag ← getMapping2 operatorApprovals ownerAddr operator
  return flag != 0

-- Approve a specific address for a single tokenId.
def approve (approved : Address) (tokenId : Uint256) : Contract Unit := do
  let sender ← msgSender
  let tokenOwner ← ownerOf tokenId
  require (sender == tokenOwner) "Not token owner"
  setMappingUint tokenApprovals tokenId (addressToWord approved)

-- Set or clear global operator approval for sender.
def setApprovalForAll (operator : Address) (approved : Bool) : Contract Unit := do
  let sender ← msgSender
  setMapping2 operatorApprovals sender operator (boolToWord approved)

-- Owner-only mint with sequential token IDs.
def mint (to : Address) : Contract Uint256 := do
  onlyOwner
  require (to != 0) "Invalid recipient"

  let tokenId ← getStorage nextTokenId
  let currentOwnerWord ← getMappingUint owners tokenId
  require (currentOwnerWord == 0) "Token already minted"

  let recipientBalance ← getMapping balances to
  let newRecipientBalance ← requireSomeUint (safeAdd recipientBalance 1) "Balance overflow"

  let currentSupply ← getStorage totalSupply
  let newSupply ← requireSomeUint (safeAdd currentSupply 1) "Supply overflow"

  setMappingUint owners tokenId (addressToWord to)
  setMapping balances to newRecipientBalance
  setStorage totalSupply newSupply
  setStorage nextTokenId (add tokenId 1)
  return tokenId

-- Transfer token from owner to recipient with approval checks.
def transferFrom (fromAddr to : Address) (tokenId : Uint256) : Contract Unit := do
  let sender ← msgSender
  require (to != 0) "Invalid recipient"

  let ownerWord ← getMappingUint owners tokenId
  require (ownerWord != 0) "Token does not exist"

  let tokenOwner := wordToAddress ownerWord
  require (tokenOwner == fromAddr) "From is not owner"

  let approvedWord ← getMappingUint tokenApprovals tokenId
  let operatorWord ← getMapping2 operatorApprovals fromAddr sender
  let senderWord := addressToWord sender
  let authorized := sender == fromAddr || approvedWord == senderWord || operatorWord != 0
  require authorized "Not authorized"

  if fromAddr == to then
    pure ()
  else
    let fromBalance ← getMapping balances fromAddr
    require (fromBalance >= 1) "Insufficient balance"
    let toBalance ← getMapping balances to
    let newToBalance ← requireSomeUint (safeAdd toBalance 1) "Balance overflow"
    setMapping balances fromAddr (sub fromBalance 1)
    setMapping balances to newToBalance

  setMappingUint owners tokenId (addressToWord to)
  setMappingUint tokenApprovals tokenId 0

end Verity.Examples.ERC721
