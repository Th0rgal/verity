import Compiler.CompilationModel
import Verity.Core
import Verity.Core.Semantics
import Verity.EVM.Uint256
import Verity.Macro
import Verity.Stdlib.Math

namespace Contracts

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

macro_rules
  | `(doElem| revert $errorName:ident($_args,*)) =>
      `(doElem| require false $(Lean.quote (toString errorName.getId)))
  | `(doElem| revertError $errorName:ident($_args,*)) =>
      `(doElem| require false $(Lean.quote (toString errorName.getId)))
  | `(doElem| requireError $cond:term $errorName:ident($_args,*)) =>
      `(doElem| if $cond then pure () else require false $(Lean.quote (toString errorName.getId)))
  | `(doElem| let $name:ident := arrayElement $values:term $index:term) => do
      let checked := Lean.mkIdentFrom name `_root_.Contracts.arrayElementChecked
      `(doElem| let $name ← $checked:ident $values $index)
  | `(doElem| let $name:ident := tload $offset:term) => do
      let load := Lean.mkIdentFrom name `_root_.Contracts.tload
      `(doElem| let $name ← $load:ident $offset)
  | `(doElem| let $pat:term := $rhs:term) => do
      if pat.raw.getKind != `Lean.Parser.Term.tuple then
        Lean.Macro.throwUnsupported
      match rhs.raw with
      | .node _ `Lean.Parser.Term.app args =>
          match args.getD 0 Lean.Syntax.missing with
          | .ident _ raw _ _ =>
              if raw.toString == "structMembers" || raw.toString == "structMembers2" then
                Lean.Macro.throwUnsupported
              else
                `(doElem| let $pat:term ← $rhs:term)
          | _ =>
              Lean.Macro.throwUnsupported
      | _ =>
          Lean.Macro.throwUnsupported


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
def tload (offset : Uint256) : Contract Uint256 := fun state =>
  ContractResult.success (state.transientStorage (offset : Nat)) state
def extcodesize (addr : Uint256) : Uint256 := addr
def keccak256 (offset size : Uint256) : Uint256 := add offset size
def call (gas target value inOffset inSize outOffset outSize : Uint256) : Uint256 :=
  add gas (add target (add value (add inOffset (add inSize (add outOffset outSize)))))
def staticcall (gas target inOffset inSize outOffset outSize : Uint256) : Uint256 :=
  add gas (add target (add inOffset (add inSize (add outOffset outSize))))
def delegatecall (gas target inOffset inSize outOffset outSize : Uint256) : Uint256 :=
  add gas (add target (add inOffset (add inSize (add outOffset outSize))))
def ecrecover (hash v r sigS : Uint256) : Contract Address := fun state =>
  ContractResult.success
    (wordToAddress ((Verity.Env.ofWorld state).callOracle "ecrecover" [hash, v, r, sigS]))
    state
def calldatacopy (_destOffset _sourceOffset _size : Uint256) : Contract Unit := pure ()
def returndataCopy (_destOffset _sourceOffset _size : Uint256) : Contract Unit := pure ()
def revertReturndata : Contract Unit := pure ()
def arrayLength {α : Type} (values : Array α) : Uint256 := values.size
def arrayElement {α : Type} [Inhabited α] (values : Array α) (index : Uint256) : α :=
  values.getD (index : Nat) default
def arrayElementChecked {α : Type} (values : Array α) (index : Uint256) : Contract α := fun state =>
  if h : (index : Nat) < values.size then
    ContractResult.success (values[(index : Nat)]'h) state
  else
    ContractResult.revert "Array index out of bounds" state
def returnArray {α : Type} (values : Array α) : Contract (Array α) := pure values
def returnValues (_values : List Uint256) : Contract Unit := pure ()
def returnBytes {α : Type} (value : α) : Contract α := pure value
def returnStorageWords (_slots : Array Uint256) : Contract (Array Uint256) := pure #[]
def emit (name : String) (args : List Uint256) : Contract Unit := emitEvent name args
def rawLog (topics : List Uint256) (dataOffset dataSize : Uint256) : Contract Unit := fun state =>
  if topics.length > 4 then
    ContractResult.revert s!"rawLog supports at most 4 topics, got {topics.length}" state
  else
    ContractResult.success () { state with
      events := state.events ++
        [{ name := s!"log{topics.length}", args := [dataOffset, dataSize], indexedArgs := topics }]
    }
def mstore (_offset _value : Uint256) : Contract Unit := pure ()
def tstore (offset value : Uint256) : Contract Unit := fun state =>
  ContractResult.success () { state with
    transientStorage := fun i => if i == (offset : Nat) then value else state.transientStorage i
  }
def getMappingWord (_slot : StorageSlot (Uint256 → Uint256)) (_key _wordOffset : Uint256) :
    Contract Uint256 := pure 0
def setMappingWord (_slot : StorageSlot (Uint256 → Uint256)) (_key _wordOffset _value : Uint256) :
    Contract Unit := pure ()
def structMember {κ α : Type} [Inhabited α] (_field : String) (_key : κ) (_member : String) :
    Contract α := pure default
def structMember2 {κ₁ κ₂ α : Type} [Inhabited α]
    (_field : String) (_key1 : κ₁) (_key2 : κ₂) (_member : String) : Contract α := pure default
def structMembers {κ α : Type} [Inhabited α]
    (_field : String) (_key : κ) (_members : List String) : α := default
def structMembers2 {κ₁ κ₂ α : Type} [Inhabited α]
    (_field : String) (_key1 : κ₁) (_key2 : κ₂) (_members : List String) : α := default
def setStructMember {κ α : Type} (_field : String) (_key : κ) (_member : String) (_value : α) :
    Contract Unit := pure ()
def setStructMember2 {κ₁ κ₂ α : Type}
    (_field : String) (_key1 : κ₁) (_key2 : κ₂) (_member : String) (_value : α) : Contract Unit := pure ()
def forEach (_name : String) (_count : Uint256) (body : Contract Unit) : Contract Unit := body
def blockTimestamp : Uint256 := 0
def blockNumber : Uint256 := 0
def blobbasefee : Uint256 := 0
def contractAddress : Uint256 := 0
def chainid : Uint256 := 0


end Contracts
