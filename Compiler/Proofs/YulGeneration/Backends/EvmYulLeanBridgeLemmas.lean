import Compiler.Proofs.YulGeneration.Builtins
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Proofs.YulGeneration

private theorem verity_eval_eq_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "eq" [a, b] =
      some (if a % evmModulus = b % evmModulus then 1 else 0) := by
  simp [evalBuiltinCall]

private theorem bridge_eval_eq_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "eq" [a, b] =
      some (if a % EvmYul.UInt256.size = b % EvmYul.UInt256.size then 1 else 0) := by
  rfl

private theorem verity_eval_iszero_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a : Nat) :
    evalBuiltinCall storage sender selector calldata "iszero" [a] =
      some (if a % evmModulus = 0 then 1 else 0) := by
  simp [evalBuiltinCall]

private theorem bridge_eval_iszero_normalized (a : Nat) :
    evalPureBuiltinViaEvmYulLean "iszero" [a] =
      some (if a % EvmYul.UInt256.size = 0 then 1 else 0) := by
  rfl

set_option maxHeartbeats 2000000 in
private theorem verity_eval_lt_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "lt" [a, b] =
      some (if a % evmModulus < b % evmModulus then 1 else 0) := by
  simp [evalBuiltinCall]

private theorem bridge_eval_lt_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "lt" [a, b] =
      some (if a % EvmYul.UInt256.size < b % EvmYul.UInt256.size then 1 else 0) := by
  rfl

set_option maxHeartbeats 2000000 in
private theorem verity_eval_gt_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "gt" [a, b] =
      some (if a % evmModulus > b % evmModulus then 1 else 0) := by
  simp [evalBuiltinCall]

private theorem bridge_eval_gt_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "gt" [a, b] =
      some (if b % EvmYul.UInt256.size < a % EvmYul.UInt256.size then 1 else 0) := by
  rfl

/-- Universal bridge theorem for `eq`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_eq_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "eq" [a, b] =
      evalPureBuiltinViaEvmYulLean "eq" [a, b] := by
  rw [verity_eval_eq_normalized, bridge_eval_eq_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

/-- Universal bridge theorem for `iszero`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_iszero_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a : Nat) :
    evalBuiltinCall storage sender selector calldata "iszero" [a] =
      evalPureBuiltinViaEvmYulLean "iszero" [a] := by
  rw [verity_eval_iszero_normalized, bridge_eval_iszero_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

/-- Universal bridge theorem for `lt`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_lt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "lt" [a, b] =
      evalPureBuiltinViaEvmYulLean "lt" [a, b] := by
  rw [verity_eval_lt_normalized, bridge_eval_lt_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

/-- Universal bridge theorem for `gt`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_gt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "gt" [a, b] =
      evalPureBuiltinViaEvmYulLean "gt" [a, b] := by
  rw [verity_eval_gt_normalized, bridge_eval_gt_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_eq_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "eq" [a, b] =
      evalBuiltinCall storage sender selector calldata "eq" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallViaEvmYulLean, evalBuiltinCall_eq_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_iszero_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "iszero" [a] =
      evalBuiltinCall storage sender selector calldata "iszero" [a] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallViaEvmYulLean, evalBuiltinCall_iszero_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_lt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "lt" [a, b] =
      evalBuiltinCall storage sender selector calldata "lt" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallViaEvmYulLean, evalBuiltinCall_lt_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_gt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "gt" [a, b] =
      evalBuiltinCall storage sender selector calldata "gt" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallViaEvmYulLean, evalBuiltinCall_gt_bridge]

end Compiler.Proofs.YulGeneration.Backends
