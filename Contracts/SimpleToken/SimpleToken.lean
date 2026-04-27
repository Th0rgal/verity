import Contracts.Common

namespace Contracts

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract SimpleToken where
  storage
    ownerSlot : Address := slot 0
    balancesSlot : Address → Uint256 := slot 1
    totalSupplySlot : Uint256 := slot 2

  constructor (initialOwner : Address) := do
    setStorageAddr ownerSlot initialOwner
    setStorage totalSupplySlot 0

  function mint (toAddr : Address, amount : Uint256) : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr ownerSlot
    require (sender == currentOwner) "Caller is not the owner"
    let currentBalance ← getMapping balancesSlot toAddr
    let newBalance ← requireSomeUint (safeAdd currentBalance amount) "Balance overflow"
    let currentSupply ← getStorage totalSupplySlot
    let newSupply ← requireSomeUint (safeAdd currentSupply amount) "Supply overflow"
    setMapping balancesSlot toAddr newBalance
    setStorage totalSupplySlot newSupply

  function transfer (toAddr : Address, amount : Uint256) : Unit := do
    let sender ← msgSender
    let senderBalance ← getMapping balancesSlot sender
    require (senderBalance >= amount) "Insufficient balance"

    if sender == toAddr then
      pure ()
    else
      let recipientBalance ← getMapping balancesSlot toAddr
      let newRecipientBalance ← requireSomeUint (safeAdd recipientBalance amount) "Recipient balance overflow"
      setMapping balancesSlot sender (sub senderBalance amount)
      setMapping balancesSlot toAddr newRecipientBalance

  function balanceOf (addr : Address) : Uint256 := do
    let currentBalance ← getMapping balancesSlot addr
    return currentBalance

  function totalSupply () : Uint256 := do
    let currentSupply ← getStorage totalSupplySlot
    return currentSupply

  function owner () : Address := do
    let currentOwner ← getStorageAddr ownerSlot
    return currentOwner

namespace SimpleToken

abbrev getTotalSupply : Contract Uint256 := totalSupply
abbrev getOwner : Contract Address := owner

def isOwner : Contract Bool := do
  let sender ← msgSender
  let currentOwner ← getStorageAddr ownerSlot
  return sender == currentOwner

def onlyOwner : Contract Unit := do
  let ownerCheck ← isOwner
  require ownerCheck "Caller is not the owner"

end SimpleToken

end Contracts
