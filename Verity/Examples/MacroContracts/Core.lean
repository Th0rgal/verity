import Verity.Examples.MacroContracts.Common

namespace Verity.Examples.MacroContracts

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract SimpleStorage where
  storage
    storedData : Uint256 := slot 0

  function store (value : Uint256) : Unit := do
    setStorage storedData value

  function retrieve () : Uint256 := do
    let current ← getStorage storedData
    return current

verity_contract Counter where
  storage
    count : Uint256 := slot 0

  function increment () : Unit := do
    let current ← getStorage count
    setStorage count (add current 1)

  function decrement () : Unit := do
    let current ← getStorage count
    setStorage count (sub current 1)

  function getCount () : Uint256 := do
    let current ← getStorage count
    return current

  function previewAddTwice (delta : Uint256) : Uint256 := do
    let base ← getStorage count
    let mut acc := base
    acc := add acc delta
    acc := add acc delta
    return acc

  function previewOps (x : Uint256, y : Uint256, z : Uint256) : Uint256 := do
    let product := mul x y
    let quotient := div product z
    let remainder := mod product z
    let lowBits := bitAnd product 255
    let mixed := bitOr lowBits (bitXor x y)
    let shifted := shl 2 mixed
    let unshifted := shr 1 shifted
    let bounded := min (max quotient remainder) unshifted
    let scaledDown := mulDivDown bounded x z
    let scaledUp := mulDivUp bounded y z
    let wadDown := wMulDown scaledDown scaledUp
    let wadUp := wDivUp wadDown z
    let chosen := ite (x > y) wadUp (sub wadUp 1)
    return chosen

  function previewEnvOps (x : Uint256, y : Uint256) : Uint256 := do
    let ts := blockTimestamp
    let self := contractAddress
    let cid := chainid
    let flagAnd := logicalAnd x y
    let flagOr := logicalOr x y
    let flagNot := logicalNot x
    let hashInput := add (add ts self) cid
    let memWord := mload hashInput
    let digest := keccak256 memWord 64
    return (add (add digest flagAnd) (add flagOr flagNot))

  function previewLowLevel (target : Uint256, count : Uint256) : Uint256 := do
    let cds := calldatasize
    let head := calldataload 0
    mstore 0 head
    calldatacopy 32 4 32
    let ok := call 50000 target 0 0 64 0 32
    let okStatic := staticcall 50000 target 0 64 0 32
    let okDelegate := delegatecall 50000 target 0 64 0 32
    forEach "i" count (do
      mstore 96 count
      pure ())
    if ok == 0 then
      revertReturndata
    else
      pure ()
    returndataCopy 0 0 32
    let rds := returndataSize
    return (add (add (add cds rds) okStatic) okDelegate)

verity_contract Owned where
  storage
    owner : Address := slot 0

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  function transferOwnership (newOwner : Address) : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"
    setStorageAddr owner newOwner

  function getOwner () : Address := do
    let currentOwner ← getStorageAddr owner
    return currentOwner

namespace Owned

def isOwner : Contract Bool := do
  let sender ← msgSender
  let currentOwner ← getStorageAddr owner
  return sender == currentOwner

def onlyOwner : Contract Unit := do
  let ownerCheck ← isOwner
  require ownerCheck "Caller is not the owner"

end Owned

verity_contract Ledger where
  storage
    balances : Address → Uint256 := slot 0

  function deposit (amount : Uint256) : Unit := do
    let sender ← msgSender
    let currentBalance ← getMapping balances sender
    setMapping balances sender (add currentBalance amount)

  function withdraw (amount : Uint256) : Unit := do
    let sender ← msgSender
    let currentBalance ← getMapping balances sender
    require (currentBalance >= amount) "Insufficient balance"
    setMapping balances sender (sub currentBalance amount)

  function transfer (to : Address, amount : Uint256) : Unit := do
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

  function getBalance (addr : Address) : Uint256 := do
    let currentBalance ← getMapping balances addr
    return currentBalance

verity_contract SafeCounter where
  storage
    count : Uint256 := slot 0

  function increment () : Unit := do
    let current ← getStorage count
    let newCount ← requireSomeUint (safeAdd current 1) "Overflow in increment"
    setStorage count newCount

  function decrement () : Unit := do
    let current ← getStorage count
    let newCount ← requireSomeUint (safeSub current 1) "Underflow in decrement"
    setStorage count newCount

  function getCount () : Uint256 := do
    let current ← getStorage count
    return current

verity_contract OwnedCounter where
  storage
    owner : Address := slot 0
    count : Uint256 := slot 1

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  function increment () : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"
    let current ← getStorage count
    setStorage count (add current 1)

  function decrement () : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"
    let current ← getStorage count
    setStorage count (sub current 1)

  function getCount () : Uint256 := do
    let current ← getStorage count
    return current

  function getOwner () : Address := do
    let currentOwner ← getStorageAddr owner
    return currentOwner

  function transferOwnership (newOwner : Address) : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"
    setStorageAddr owner newOwner

namespace OwnedCounter

def isOwner : Contract Bool := do
  let sender ← msgSender
  let currentOwner ← getStorageAddr owner
  return sender == currentOwner

def onlyOwner : Contract Unit := do
  let ownerCheck ← isOwner
  require ownerCheck "Caller is not the owner"

end OwnedCounter


end Verity.Examples.MacroContracts
