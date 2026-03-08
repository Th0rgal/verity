import Contracts.Common

namespace Contracts

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

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
    let bn := blockNumber
    let self := contractAddress
    let cid := chainid
    let flagAnd := logicalAnd x y
    let flagOr := logicalOr x y
    let flagNot := logicalNot x
    let hashInput := add (add (add ts bn) self) cid
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

end Contracts
