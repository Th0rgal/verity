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
  | `(term| ecmCall $_moduleFactory:term $_args:term) =>
      `(term| do
          let _ := $_moduleFactory
          let _ := $_args
          pure (0 : Uint256))
  | `(term| ecmDo $_module:term $_args:term) =>
      `(term| do
          let _ := $_module
          let _ := $_args
          pure ())
  | `(doElem| revert $errorName:ident($args,*)) => do
      let revertFn := Lean.mkIdentFrom errorName `_root_.Contracts.revertCustomError
      let encodeFn := Lean.mkIdentFrom errorName `_root_.Contracts.CustomErrorArg.encode
      let encodedArgs ← args.getElems.mapM fun arg => `(term| $encodeFn:ident $arg)
      `(doElem| $revertFn:ident
          $(Lean.quote (toString errorName.getId))
          [ $[$encodedArgs],* ])
  | `(doElem| revertError $errorName:ident($args,*)) => do
      let revertFn := Lean.mkIdentFrom errorName `_root_.Contracts.revertCustomError
      let encodeFn := Lean.mkIdentFrom errorName `_root_.Contracts.CustomErrorArg.encode
      let encodedArgs ← args.getElems.mapM fun arg => `(term| $encodeFn:ident $arg)
      `(doElem| $revertFn:ident
          $(Lean.quote (toString errorName.getId))
          [ $[$encodedArgs],* ])
  | `(doElem| requireError $cond:term $errorName:ident($args,*)) => do
      let requireFn := Lean.mkIdentFrom errorName `_root_.Contracts.requireCustomError
      let encodeFn := Lean.mkIdentFrom errorName `_root_.Contracts.CustomErrorArg.encode
      let encodedArgs ← args.getElems.mapM fun arg => `(term| $encodeFn:ident $arg)
      `(doElem| $requireFn:ident
          $cond
          $(Lean.quote (toString errorName.getId))
          [ $[$encodedArgs],* ])
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

structure Int256 where
  word : Uint256
  deriving Repr, BEq, DecidableEq, Inhabited

def toInt256 (value : Uint256) : Int256 := ⟨value⟩
def toUint256 (value : Int256) : Uint256 := value.word

instance : Coe Int256 Uint256 := ⟨Int256.word⟩
instance : OfNat Int256 n := ⟨toInt256 (n : Uint256)⟩

class CustomErrorArg (α : Type) where
  encode : α → String

instance : CustomErrorArg Uint256 where
  encode value := toString (value : Nat)

instance : CustomErrorArg Nat where
  encode value := toString value

instance : CustomErrorArg Address where
  encode value := toString value.toNat

instance : CustomErrorArg Bool where
  encode value := if value then "true" else "false"

instance : CustomErrorArg String where
  encode value := value

instance : CustomErrorArg ByteArray where
  encode value := reprStr value.toList

instance [CustomErrorArg α] : CustomErrorArg (Array α) where
  encode values := "[" ++ String.intercalate ", " (values.toList.map CustomErrorArg.encode) ++ "]"

instance [CustomErrorArg α] [CustomErrorArg β] : CustomErrorArg (α × β) where
  encode value := "(" ++ CustomErrorArg.encode value.1 ++ ", " ++ CustomErrorArg.encode value.2 ++ ")"

def formatCustomError (name : String) (args : List String) : String :=
  name ++ "(" ++ String.intercalate ", " args ++ ")"

def revertCustomError (name : String) (args : List String) : Contract Unit :=
  require false (formatCustomError name args)

def requireCustomError (condition : Bool) (name : String) (args : List String) : Contract Unit :=
  if condition then pure () else revertCustomError name args

private def signedWordLimit : Nat := Verity.Core.Uint256.modulus / 2

private def wordToSigned (value : Uint256) : Int :=
  let raw : Nat := value
  if raw < signedWordLimit then
    Int.ofNat raw
  else
    Int.ofNat raw - Int.ofNat Verity.Core.Uint256.modulus

private def signedToWord (value : Int) : Uint256 :=
  let reduced := Int.emod value (Int.ofNat Verity.Core.Uint256.modulus)
  (reduced.toNat : Uint256)

private def signedAbsNat (value : Int) : Nat :=
  Int.natAbs value

instance : CustomErrorArg Int256 where
  encode value := toString (wordToSigned value.word)

private def pow2 (n : Nat) : Nat := 2 ^ n

def sdiv (a b : Uint256) : Uint256 :=
  let lhs := wordToSigned a
  let rhs := wordToSigned b
  if rhs == 0 then
    0
  else
    let quotient := signedAbsNat lhs / signedAbsNat rhs
    let sameSign := (lhs < 0) == (rhs < 0)
    if sameSign then
      signedToWord (Int.ofNat quotient)
    else
      signedToWord (- Int.ofNat quotient)

def smod (a b : Uint256) : Uint256 :=
  let lhs := wordToSigned a
  let rhs := wordToSigned b
  if rhs == 0 then
    0
  else
    let modulus := signedAbsNat lhs % signedAbsNat rhs
    if lhs < 0 then
      signedToWord (- Int.ofNat modulus)
    else
      signedToWord (Int.ofNat modulus)

def slt (a b : Uint256) : Bool := wordToSigned a < wordToSigned b
def sgt (a b : Uint256) : Bool := wordToSigned a > wordToSigned b

def sar (shift value : Uint256) : Uint256 :=
  let shiftNat : Nat := shift
  if shiftNat >= 256 then
    if wordToSigned value < 0 then
      (Verity.Core.MAX_UINT256 : Uint256)
    else
      0
  else
    let divisor := Int.ofNat (pow2 shiftNat)
    signedToWord (Int.ediv (wordToSigned value) divisor)

def signextend (byteIndex value : Uint256) : Uint256 :=
  let idx : Nat := byteIndex
  if idx >= 32 then
    value
  else
    let bitIndex := 8 * idx + 7
    let width := bitIndex + 1
    let lowMask := pow2 width - 1
    let lowBits := (value : Nat) % pow2 width
    let signSet := ((lowBits / pow2 bitIndex) % 2) == 1
    if signSet then
      ((lowBits + (Verity.Core.Uint256.modulus - lowMask - 1)) : Uint256)
    else
      (lowBits : Uint256)

instance : Add Int256 := ⟨fun a b => toInt256 (a.word + b.word)⟩
instance : Sub Int256 := ⟨fun a b => toInt256 (a.word - b.word)⟩
instance : Mul Int256 := ⟨fun a b => toInt256 (a.word * b.word)⟩
instance : Div Int256 := ⟨fun a b => toInt256 (sdiv a.word b.word)⟩
instance : Mod Int256 := ⟨fun a b => toInt256 (smod a.word b.word)⟩
instance : LT Int256 := ⟨fun a b => wordToSigned a.word < wordToSigned b.word⟩
instance : LE Int256 := ⟨fun a b => wordToSigned a.word ≤ wordToSigned b.word⟩

abbrev mulDivDown := Verity.Stdlib.Math.mulDivDown
abbrev mulDivUp := Verity.Stdlib.Math.mulDivUp

abbrev wMulDown := Verity.Stdlib.Math.wMulDown
abbrev wDivUp := Verity.Stdlib.Math.wDivUp

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
class ExternalArg (α : Type) where
  toWord : α → Uint256
class ExternalResult (α : Type) where
  fromWord : Uint256 → α
instance : ExternalArg Uint256 where
  toWord value := value
instance : ExternalArg Int256 where
  toWord value := value.word
instance : ExternalArg Address where
  toWord value := value.toNat
instance : ExternalArg Bool where
  toWord value := if value then 1 else 0
instance : ExternalResult Uint256 where
  fromWord value := value
instance : ExternalResult Int256 where
  fromWord value := toInt256 value
instance : ExternalResult Address where
  fromWord value := wordToAddress value
instance : ExternalResult Bool where
  fromWord value := value != 0
private def externalCallStubWord (name : String) (args : List Uint256) : Uint256 :=
  match name, args with
  | "echo", [value] => value
  | _, _ => args.foldl add name.length
def externalCallWords {α : Type} [ExternalResult α] (name : String) (args : List Uint256) : α :=
  ExternalResult.fromWord (externalCallStubWord name args)
private def erc20ReadStubWord (name : String) (args : List Uint256) : Uint256 :=
  externalCallStubWord name args
macro_rules
  | `(term| externalCall $name:ident [ $[$args:term],* ]) =>
      `(externalCallWords $(Lean.quote (toString name.getId)) [ $[ExternalArg.toWord $args],* ])
  | `(term| externalCall $name:str [ $[$args:term],* ]) =>
      `(externalCallWords $name [ $[ExternalArg.toWord $args],* ])
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
def safeTransfer (_token _to : Address) (_amount : Uint256) : Contract Unit := pure ()
def safeTransferFrom (_token _fromAddr _to : Address) (_amount : Uint256) : Contract Unit := pure ()
def safeApprove (_token _spender : Address) (_amount : Uint256) : Contract Unit := pure ()
def balanceOf (token owner : Address) : Contract Uint256 := pure <| erc20ReadStubWord "balanceOf" [token.toNat, owner.toNat]
def allowance (token owner spender : Address) : Contract Uint256 := pure <| erc20ReadStubWord "allowance" [token.toNat, owner.toNat, spender.toNat]
def totalSupply (token : Address) : Contract Uint256 := pure <| erc20ReadStubWord "totalSupply" [token.toNat]
def forEach (_name : String) (_count : Uint256) (body : Contract Unit) : Contract Unit := body
def blockTimestamp : Uint256 := 0
def blockNumber : Uint256 := 0
def blobbasefee : Uint256 := 0
def contractAddress : Uint256 := 0
def chainid : Uint256 := 0


end Contracts
