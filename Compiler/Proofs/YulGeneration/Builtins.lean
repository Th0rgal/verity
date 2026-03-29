import Compiler.Constants
import Compiler.Proofs.MappingSlot
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter

namespace Compiler.Proofs.YulGeneration

open Compiler.Proofs
export Compiler.Constants (evmModulus selectorModulus selectorShift)

def selectorWord (selector : Nat) : Nat :=
  (selector % selectorModulus) * (2 ^ selectorShift)

def calldataloadWord (selector : Nat) (calldata : List Nat) (offset : Nat) : Nat :=
  if offset = 0 then
    selectorWord selector
  else if offset < 4 then
    0
  else
    let wordOffset := offset - 4
    if wordOffset % 32 != 0 then
      0
    else
      let idx := wordOffset / 32
      calldata.getD idx 0 % evmModulus

def evalBuiltinCallWithContext
    (storage : Nat → Nat)
    (sender : Nat)
    (msgValue : Nat)
    (thisAddress : Nat)
    (blockTimestamp : Nat)
    (blockNumber : Nat)
    (chainId : Nat)
    (blobBaseFee : Nat)
    (selector : Nat)
    (calldata : List Nat)
    (func : String)
    (argVals : List Nat) : Option Nat :=
  let toWord (x : Nat) : Nat := x % evmModulus
  if func = "mappingSlot" then
    match argVals with
    | [base, key] => some (Compiler.Proofs.abstractMappingSlot base key)
    | _ => none
  else if func = "sload" then
    match argVals with
    | [slot] => some (Compiler.Proofs.abstractLoadStorageOrMapping storage slot)
    | _ => none
  else if func = "add" then
    match argVals with
    | [a, b] => some ((a + b) % evmModulus)
    | _ => none
  else if func = "sub" then
    match argVals with
    | [a, b] =>
        let a := toWord a
        let b := toWord b
        some ((evmModulus + a - b) % evmModulus)
    | _ => none
  else if func = "mul" then
    match argVals with
    | [a, b] => some ((a * b) % evmModulus)
    | _ => none
  else if func = "div" then
    match argVals with
    | [a, b] =>
        let a := toWord a
        let b := toWord b
        if b = 0 then some 0 else some (a / b)
    | _ => none
  else if func = "mod" then
    match argVals with
    | [a, b] =>
        let a := toWord a
        let b := toWord b
        if b = 0 then some 0 else some (a % b)
    | _ => none
  else if func = "lt" then
    match argVals with
    | [a, b] => some (if a % evmModulus < b % evmModulus then 1 else 0)
    | _ => none
  else if func = "gt" then
    match argVals with
    | [a, b] => some (if a % evmModulus > b % evmModulus then 1 else 0)
    | _ => none
  else if func = "slt" then
    match argVals with
    | [a, b] =>
        let sa := Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % evmModulus)))
        let sb := Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % evmModulus)))
        some (if sa < sb then 1 else 0)
    | _ => none
  else if func = "sgt" then
    match argVals with
    | [a, b] =>
        let sa := Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % evmModulus)))
        let sb := Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % evmModulus)))
        some (if sb < sa then 1 else 0)
    | _ => none
  else if func = "sdiv" then
    match argVals with
    | [a, b] =>
        let sa := Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % evmModulus))
        let sb := Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % evmModulus))
        some (Verity.Core.Int256.div sa sb).toUint256.val
    | _ => none
  else if func = "smod" then
    match argVals with
    | [a, b] =>
        let sa := Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % evmModulus))
        let sb := Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % evmModulus))
        some (Verity.Core.Int256.mod sa sb).toUint256.val
    | _ => none
  else if func = "eq" then
    match argVals with
    | [a, b] => some (if a % evmModulus = b % evmModulus then 1 else 0)
    | _ => none
  else if func = "iszero" then
    match argVals with
    | [a] => some (if a % evmModulus = 0 then 1 else 0)
    | _ => none
  else if func = "and" then
    match argVals with
    | [a, b] => some (toWord a &&& toWord b)
    | _ => none
  else if func = "or" then
    match argVals with
    | [a, b] => some (toWord a ||| toWord b)
    | _ => none
  else if func = "xor" then
    match argVals with
    | [a, b] => some (Nat.xor (toWord a) (toWord b))
    | _ => none
  else if func = "not" then
    match argVals with
    | [a] => some (Nat.xor (toWord a) (evmModulus - 1))
    | _ => none
  else if func = "shl" then
    match argVals with
    | [shift, value] =>
        let shift := toWord shift
        if shift < 256 then
          some ((toWord value * (2 ^ shift)) % evmModulus)
        else
          some 0
    | _ => none
  else if func = "shr" then
    match argVals with
    | [shift, value] =>
        let shift := toWord shift
        let value := toWord value
        if shift < 256 then
          some (value / (2 ^ shift))
        else
          some 0
    | _ => none
  else if func = "caller" then
    match argVals with
    | [] => some sender
    | _ => none
  else if func = "address" then
    match argVals with
    | [] => some (toWord thisAddress)
    | _ => none
  else if func = "timestamp" then
    match argVals with
    | [] => some (toWord blockTimestamp)
    | _ => none
  else if func = "number" then
    match argVals with
    | [] => some (toWord blockNumber)
    | _ => none
  else if func = "chainid" then
    match argVals with
    | [] => some (toWord chainId)
    | _ => none
  else if func = "blobbasefee" then
    match argVals with
    | [] => some (toWord blobBaseFee)
    | _ => none
  else if func = "calldataload" then
    match argVals with
    | [offset] => some (calldataloadWord selector calldata offset)
    | _ => none
  else if func = "callvalue" then
    match argVals with
    | [] => some (toWord msgValue)
    | _ => none
  else if func = "calldatasize" then
    match argVals with
    | [] => some (4 + calldata.length * 32)
    | _ => none
  else
    none

inductive BuiltinBackend where
  | verity
  | evmYulLean
  deriving DecidableEq, Repr

abbrev defaultBuiltinBackend : BuiltinBackend := .verity

def evalBuiltinCallWithBackendContext
    (backend : BuiltinBackend)
    (storage : Nat → Nat)
    (sender : Nat)
    (msgValue : Nat)
    (thisAddress : Nat)
    (blockTimestamp : Nat)
    (blockNumber : Nat)
    (chainId : Nat)
    (blobBaseFee : Nat)
    (selector : Nat)
    (calldata : List Nat)
    (func : String)
    (argVals : List Nat) : Option Nat :=
  match backend with
  | .verity =>
      evalBuiltinCallWithContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata func argVals
  | .evmYulLean =>
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean
        storage sender selector calldata func argVals

def evalBuiltinCallWithBackend
    (backend : BuiltinBackend)
    (storage : Nat → Nat)
    (sender : Nat)
    (selector : Nat)
    (calldata : List Nat)
    (func : String)
    (argVals : List Nat) : Option Nat :=
  evalBuiltinCallWithBackendContext backend storage sender 0 0 0 0 0 0 selector calldata func argVals

def evalBuiltinCall
    (storage : Nat → Nat)
    (sender : Nat)
    (selector : Nat)
    (calldata : List Nat)
    (func : String)
    (argVals : List Nat) : Option Nat :=
  evalBuiltinCallWithContext storage sender 0 0 0 0 0 0 selector calldata func argVals

@[simp] theorem evalBuiltinCall_callvalue_nil
    (storage : Nat → Nat) (sender thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) :
    evalBuiltinCallWithContext storage sender 0 thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "callvalue" [] =
      some 0 := by
  simp [evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCall_callvalue_context
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) :
    evalBuiltinCallWithContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "callvalue" [] =
      some (msgValue % evmModulus) := by
  simp [evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCall_calldatasize_nil
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) :
    evalBuiltinCall storage sender selector calldata "calldatasize" [] =
      some (4 + calldata.length * 32) := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCall_caller_nil
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) :
    evalBuiltinCall storage sender selector calldata "caller" [] = some sender := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCall_address_nil
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) :
    evalBuiltinCallWithContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "address" [] =
      some (thisAddress % evmModulus) := by
  simp [evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCall_timestamp_nil
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) :
    evalBuiltinCallWithContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "timestamp" [] =
      some (blockTimestamp % evmModulus) := by
  simp [evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCall_number_nil
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) :
    evalBuiltinCallWithContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "number" [] =
      some (blockNumber % evmModulus) := by
  simp [evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCall_chainid_nil
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) :
    evalBuiltinCallWithContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "chainid" [] =
      some (chainId % evmModulus) := by
  simp [evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCall_blobbasefee_nil
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) :
    evalBuiltinCallWithContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "blobbasefee" [] =
      some (blobBaseFee % evmModulus) := by
  simp [evalBuiltinCallWithContext]

@[simp] theorem calldataloadWord_offset4
    (selector : Nat) (calldata : List Nat) :
    calldataloadWord selector calldata 4 = calldata.getD 0 0 % evmModulus := by
  simp [calldataloadWord]

@[simp] theorem evalBuiltinCall_calldataload_offset4_single
    (storage : Nat → Nat) (sender selector value : Nat) :
    evalBuiltinCall storage sender selector [value] "calldataload" [4] = some (value % evmModulus) := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext, calldataloadWord]

@[simp] theorem evalBuiltinCallWithBackend_calldataload_offset4_single
    (storage : Nat → Nat) (sender selector value : Nat) :
    evalBuiltinCallWithBackend
        defaultBuiltinBackend
        storage
        sender
        selector
        [value]
        "calldataload"
        [4] =
      some (value % evmModulus) := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallWithContext,
    calldataloadWord]

@[simp] theorem evalBuiltinCall_sload_single
    (storage : Nat → Nat) (sender selector : Nat) (slot : Nat) :
    evalBuiltinCall storage sender selector [] "sload" [slot] =
      some (Compiler.Proofs.abstractLoadStorageOrMapping storage slot) := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackend_sload_single
    (storage : Nat → Nat) (sender selector : Nat) (slot : Nat) :
    evalBuiltinCallWithBackend
        defaultBuiltinBackend
        storage
        sender
        selector
        []
        "sload"
        [slot] =
      some (Compiler.Proofs.abstractLoadStorageOrMapping storage slot) := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallWithContext]

end Compiler.Proofs.YulGeneration
