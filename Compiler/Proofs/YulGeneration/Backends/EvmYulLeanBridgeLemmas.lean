import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgePredicates
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBuiltinSemantics
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeLowering
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanPureBuiltinLemmas
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanSignedArithSpec

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Proofs.IRGeneration (IRStorageWord IRStorageSlot)

/-!
Native EVMYulLean builtin routing facts.

The historical reference-oracle comparison layer has been removed. These lemmas
record only the native `.evmYulLean` dispatch surface used by the public
EndToEnd target and by reporting scripts that audit available builtin coverage.
-/

@[simp] theorem evalBuiltinCall_add_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "add" [a, b] =
      evalPureBuiltinViaEvmYulLean "add" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_sub_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "sub" [a, b] =
      evalPureBuiltinViaEvmYulLean "sub" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_mul_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "mul" [a, b] =
      evalPureBuiltinViaEvmYulLean "mul" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_div_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "div" [a, b] =
      evalPureBuiltinViaEvmYulLean "div" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_mod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "mod" [a, b] =
      evalPureBuiltinViaEvmYulLean "mod" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_addmod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b n : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "addmod" [a, b, n] =
      evalPureBuiltinViaEvmYulLean "addmod" [a, b, n] := by
  rfl

@[simp] theorem evalBuiltinCall_mulmod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b n : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "mulmod" [a, b, n] =
      evalPureBuiltinViaEvmYulLean "mulmod" [a, b, n] := by
  rfl

@[simp] theorem evalBuiltinCall_exp_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "exp" [a, b] =
      evalPureBuiltinViaEvmYulLean "exp" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_sdiv_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "sdiv" [a, b] =
      evalPureBuiltinViaEvmYulLean "sdiv" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_smod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "smod" [a, b] =
      evalPureBuiltinViaEvmYulLean "smod" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_lt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "lt" [a, b] =
      evalPureBuiltinViaEvmYulLean "lt" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_gt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "gt" [a, b] =
      evalPureBuiltinViaEvmYulLean "gt" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_slt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "slt" [a, b] =
      evalPureBuiltinViaEvmYulLean "slt" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_sgt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "sgt" [a, b] =
      evalPureBuiltinViaEvmYulLean "sgt" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_eq_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "eq" [a, b] =
      evalPureBuiltinViaEvmYulLean "eq" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_iszero_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "iszero" [a] =
      evalPureBuiltinViaEvmYulLean "iszero" [a] := by
  rfl

@[simp] theorem evalBuiltinCall_and_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "and" [a, b] =
      evalPureBuiltinViaEvmYulLean "and" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_or_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "or" [a, b] =
      evalPureBuiltinViaEvmYulLean "or" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_xor_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "xor" [a, b] =
      evalPureBuiltinViaEvmYulLean "xor" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_not_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "not" [a] =
      evalPureBuiltinViaEvmYulLean "not" [a] := by
  rfl

@[simp] theorem evalBuiltinCall_shl_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "shl" [shift, value] =
      evalPureBuiltinViaEvmYulLean "shl" [shift, value] := by
  rfl

@[simp] theorem evalBuiltinCall_shr_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "shr" [shift, value] =
      evalPureBuiltinViaEvmYulLean "shr" [shift, value] := by
  rfl

@[simp] theorem evalBuiltinCall_sar_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "sar" [shift, value] =
      evalPureBuiltinViaEvmYulLean "sar" [shift, value] := by
  rfl

@[simp] theorem evalBuiltinCall_signextend_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (byteIdx value : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "signextend" [byteIdx, value] =
      evalPureBuiltinViaEvmYulLean "signextend" [byteIdx, value] := by
  rfl

@[simp] theorem evalBuiltinCall_byte_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (i x : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "byte" [i, x] =
      evalPureBuiltinViaEvmYulLean "byte" [i, x] := by
  rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_sload (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "sload" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_caller (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "caller" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_address (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "address" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_callvalue (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "callvalue" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_timestamp (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "timestamp" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_number (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "number" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_chainid (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "chainid" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_blobbasefee (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "blobbasefee" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_calldataload (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "calldataload" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_calldatasize (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "calldatasize" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_mappingSlot (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "mappingSlot" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

@[simp] theorem evalBuiltinCall_calldataload_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (offset : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "calldataload" [offset] =
      some (Compiler.Proofs.YulGeneration.calldataloadWord selector calldata offset) := by
  rfl

@[simp] theorem evalBuiltinCall_sload_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (slot : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "sload" [slot] =
      some (storage (IRStorageSlot.ofNat slot)).toNat := by
  rfl

@[simp] theorem evalBuiltinCall_mappingSlot_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (base key : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "mappingSlot" [base, key] =
      some (Compiler.Proofs.abstractMappingSlot base key) := by
  rfl


end Compiler.Proofs.YulGeneration.Backends
