import Compiler.CompilationModel
import Verity.Core
import Verity.EVM.Uint256
import Verity.Macro
import Verity.Stdlib.Math

namespace Contracts

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math


def bitAnd (a b : Uint256) : Uint256 := Verity.Core.Uint256.and a b
def bitOr (a b : Uint256) : Uint256 := Verity.Core.Uint256.or a b
def bitXor (a b : Uint256) : Uint256 := Verity.Core.Uint256.xor a b

def mulDivDown (a b c : Uint256) : Uint256 := div (mul a b) c
def mulDivUp (a b c : Uint256) : Uint256 := div (add (mul a b) (sub c 1)) c

def wMulDown (a b : Uint256) : Uint256 := mulDivDown a b 1000000000000000000
def wDivUp (a b : Uint256) : Uint256 := mulDivUp a 1000000000000000000 b

def min (a b : Uint256) : Uint256 := if a <= b then a else b
def max (a b : Uint256) : Uint256 := if a >= b then a else b
def ite (cond : Prop) [Decidable cond] (thenVal elseVal : Uint256) : Uint256 :=
  if cond then thenVal else elseVal
def logicalAnd (a b : Uint256) : Uint256 := if a != 0 && b != 0 then 1 else 0
def logicalOr (a b : Uint256) : Uint256 := if a != 0 || b != 0 then 1 else 0
def logicalNot (a : Uint256) : Uint256 := if a == 0 then 1 else 0
def calldatasize : Uint256 := 0
def returndataSize : Uint256 := 0
def calldataload (offset : Uint256) : Uint256 := offset
def mload (offset : Uint256) : Uint256 := offset
def extcodesize (addr : Uint256) : Uint256 := addr
def keccak256 (offset size : Uint256) : Uint256 := add offset size
def call (gas target value inOffset inSize outOffset outSize : Uint256) : Uint256 :=
  add gas (add target (add value (add inOffset (add inSize (add outOffset outSize)))))
def staticcall (gas target inOffset inSize outOffset outSize : Uint256) : Uint256 :=
  add gas (add target (add inOffset (add inSize (add outOffset outSize))))
def delegatecall (gas target inOffset inSize outOffset outSize : Uint256) : Uint256 :=
  add gas (add target (add inOffset (add inSize (add outOffset outSize))))
def calldatacopy (_destOffset _sourceOffset _size : Uint256) : Contract Unit := pure ()
def returndataCopy (_destOffset _sourceOffset _size : Uint256) : Contract Unit := pure ()
def revertReturndata : Contract Unit := pure ()
def returnValues (_values : List Uint256) : Contract Unit := pure ()
def returnBytes {α : Type} [Inhabited α] (_value : α) : Contract α := pure default
def returnStorageWords (_slots : Array Uint256) : Contract (Array Uint256) := pure #[]
def mstore (_offset _value : Uint256) : Contract Unit := pure ()
def getMappingWord (_slot : StorageSlot (Uint256 → Uint256)) (_key _wordOffset : Uint256) :
    Contract Uint256 := pure 0
def setMappingWord (_slot : StorageSlot (Uint256 → Uint256)) (_key _wordOffset _value : Uint256) :
    Contract Unit := pure ()
def structMember {κ α : Type} [Inhabited α] (_field : String) (_key : κ) (_member : String) :
    Contract α := pure default
def structMember2 {κ₁ κ₂ α : Type} [Inhabited α]
    (_field : String) (_key1 : κ₁) (_key2 : κ₂) (_member : String) : Contract α := pure default
def setStructMember {κ α : Type} (_field : String) (_key : κ) (_member : String) (_value : α) :
    Contract Unit := pure ()
def setStructMember2 {κ₁ κ₂ α : Type}
    (_field : String) (_key1 : κ₁) (_key2 : κ₂) (_member : String) (_value : α) : Contract Unit := pure ()
def forEach (_name : String) (_count : Uint256) (body : Contract Unit) : Contract Unit := body
def blockTimestamp : Uint256 := 0
def blockNumber : Uint256 := 0
def contractAddress : Uint256 := 0
def chainid : Uint256 := 0


end Contracts
