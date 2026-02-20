import Compiler.Proofs.MappingSlot
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter

namespace Compiler.Proofs.YulGeneration

open Compiler.Proofs

abbrev evmModulus : Nat := Compiler.Proofs.evmModulus

def selectorModulus : Nat := 2 ^ 32

def selectorShift : Nat := 224

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

def evalBuiltinCall
    (storage : Nat → Nat)
    (mappings : Nat → Nat → Nat)
    (sender : Nat)
    (selector : Nat)
    (calldata : List Nat)
    (func : String)
    (argVals : List Nat) : Option Nat :=
  if func = "mappingSlot" then
    match argVals with
    | [base, key] => some (Compiler.Proofs.abstractMappingSlot base key)
    | _ => none
  else if func = "sload" then
    match argVals with
    | [slot] => some (Compiler.Proofs.abstractLoadStorageOrMapping storage mappings slot)
    | _ => none
  else if func = "add" then
    match argVals with
    | [a, b] => some ((a + b) % evmModulus)
    | _ => none
  else if func = "sub" then
    match argVals with
    | [a, b] => some ((evmModulus + a - b) % evmModulus)
    | _ => none
  else if func = "mul" then
    match argVals with
    | [a, b] => some ((a * b) % evmModulus)
    | _ => none
  else if func = "div" then
    match argVals with
    | [a, b] => if b = 0 then some 0 else some (a / b)
    | _ => none
  else if func = "mod" then
    match argVals with
    | [a, b] => if b = 0 then some 0 else some (a % b)
    | _ => none
  else if func = "lt" then
    match argVals with
    | [a, b] => some (if a < b then 1 else 0)
    | _ => none
  else if func = "gt" then
    match argVals with
    | [a, b] => some (if a > b then 1 else 0)
    | _ => none
  else if func = "eq" then
    match argVals with
    | [a, b] => some (if a = b then 1 else 0)
    | _ => none
  else if func = "iszero" then
    match argVals with
    | [a] => some (if a = 0 then 1 else 0)
    | _ => none
  else if func = "and" then
    match argVals with
    | [a, b] => some (a &&& b)
    | _ => none
  else if func = "or" then
    match argVals with
    | [a, b] => some (a ||| b)
    | _ => none
  else if func = "xor" then
    match argVals with
    | [a, b] => some (Nat.xor a b)
    | _ => none
  else if func = "not" then
    match argVals with
    | [a] => some (Nat.xor a (evmModulus - 1))
    | _ => none
  else if func = "shl" then
    match argVals with
    | [shift, value] => some ((value * (2 ^ shift)) % evmModulus)
    | _ => none
  else if func = "shr" then
    match argVals with
    | [shift, value] => some (value / (2 ^ shift))
    | _ => none
  else if func = "caller" then
    match argVals with
    | [] => some sender
    | _ => none
  else if func = "calldataload" then
    match argVals with
    | [offset] => some (calldataloadWord selector calldata offset)
    | _ => none
  else
    none

inductive BuiltinBackend where
  | verity
  | evmYulLean
  deriving DecidableEq, Repr

abbrev defaultBuiltinBackend : BuiltinBackend := .verity

def evalBuiltinCallWithBackend
    (backend : BuiltinBackend)
    (storage : Nat → Nat)
    (mappings : Nat → Nat → Nat)
    (sender : Nat)
    (selector : Nat)
    (calldata : List Nat)
    (func : String)
    (argVals : List Nat) : Option Nat :=
  match backend with
  | .verity =>
      evalBuiltinCall storage mappings sender selector calldata func argVals
  | .evmYulLean =>
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean
        storage mappings sender selector calldata func argVals

end Compiler.Proofs.YulGeneration
