import Contracts.Common

namespace Contracts

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract ERC20 where
  storage
    ownerSlot : Address := slot 0
    totalSupplySlot : Uint256 := slot 1
    balancesSlot : Address → Uint256 := slot 2
    allowancesSlot : Address → Address → Uint256 := slot 3

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

  function approve (spender : Address, amount : Uint256) : Unit := do
    let sender ← msgSender
    setMapping2 allowancesSlot sender spender amount

  function transferFrom (fromAddr : Address, toAddr : Address, amount : Uint256) : Unit := do
    let spender ← msgSender
    let currentAllowance ← getMapping2 allowancesSlot fromAddr spender
    require (currentAllowance >= amount) "Insufficient allowance"

    let fromBalance ← getMapping balancesSlot fromAddr
    require (fromBalance >= amount) "Insufficient balance"

    if fromAddr == toAddr then
      pure ()
    else
      let toBalance ← getMapping balancesSlot toAddr
      let newToBalance ← requireSomeUint (safeAdd toBalance amount) "Recipient balance overflow"
      setMapping balancesSlot fromAddr (sub fromBalance amount)
      setMapping balancesSlot toAddr newToBalance

    if currentAllowance == 115792089237316195423570985008687907853269984665640564039457584007913129639935 then
      pure ()
    else
      setMapping2 allowancesSlot fromAddr spender (sub currentAllowance amount)

  function balanceOf (addr : Address) : Uint256 := do
    let currentBalance ← getMapping balancesSlot addr
    return currentBalance

  function allowanceOf (ownerAddr : Address, spender : Address) : Uint256 := do
    let currentAllowance ← getMapping2 allowancesSlot ownerAddr spender
    return currentAllowance

  function totalSupply () : Uint256 := do
    let currentSupply ← getStorage totalSupplySlot
    return currentSupply

  function owner () : Address := do
    let currentOwner ← getStorageAddr ownerSlot
    return currentOwner

namespace ERC20

abbrev getTotalSupply : Contract Uint256 := totalSupply
abbrev getOwner : Contract Address := owner

def isOwner : Contract Bool := do
  let sender ← msgSender
  let currentOwner ← getStorageAddr ownerSlot
  return sender == currentOwner

def onlyOwner : Contract Unit := do
  let ownerCheck ← isOwner
  require ownerCheck "Caller is not the owner"

end ERC20

end Contracts
