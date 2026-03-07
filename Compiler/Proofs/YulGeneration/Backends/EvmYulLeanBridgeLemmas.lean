import Compiler.Proofs.YulGeneration.Builtins
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Proofs.YulGeneration

private theorem verity_eval_add_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "add" [a, b] =
      some ((a + b) % evmModulus) := by
  simp [evalBuiltinCall]

private theorem bridge_eval_add_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "add" [a, b] =
      some ((a + b) % EvmYul.UInt256.size) := by
  change some ((Fin.ofNat EvmYul.UInt256.size a + Fin.ofNat EvmYul.UInt256.size b).val) =
      some ((a + b) % EvmYul.UInt256.size)
  simp [Fin.val_add, Nat.add_mod]

private theorem verity_eval_sub_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "sub" [a, b] =
      some ((evmModulus + a % evmModulus - b % evmModulus) % evmModulus) := by
  simp [evalBuiltinCall]

private theorem bridge_eval_sub_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "sub" [a, b] =
      some ((EvmYul.UInt256.size - b % EvmYul.UInt256.size + a % EvmYul.UInt256.size) %
        EvmYul.UInt256.size) := by
  change some ((Fin.ofNat EvmYul.UInt256.size a - Fin.ofNat EvmYul.UInt256.size b).val) =
      some ((EvmYul.UInt256.size - b % EvmYul.UInt256.size + a % EvmYul.UInt256.size) %
        EvmYul.UInt256.size)
  simp [Fin.sub_def, Nat.add_mod]

private theorem verity_eval_mul_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "mul" [a, b] =
      some ((a * b) % evmModulus) := by
  simp [evalBuiltinCall]

private theorem bridge_eval_mul_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "mul" [a, b] =
      some ((a * b) % EvmYul.UInt256.size) := by
  change some ((Fin.ofNat EvmYul.UInt256.size a * Fin.ofNat EvmYul.UInt256.size b).val) =
      some ((a * b) % EvmYul.UInt256.size)
  simp [Fin.mul_def, Nat.mul_mod]

private theorem verity_eval_div_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "div" [a, b] =
      (if b % evmModulus = 0 then some 0 else some ((a % evmModulus) / (b % evmModulus))) := by
  simp [evalBuiltinCall]

private theorem bridge_eval_div_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "div" [a, b] =
      (if b % EvmYul.UInt256.size = 0 then some 0 else
        some ((a % EvmYul.UInt256.size) / (b % EvmYul.UInt256.size))) := by
  change some ((Fin.ofNat EvmYul.UInt256.size a / Fin.ofNat EvmYul.UInt256.size b).val) =
      (if b % EvmYul.UInt256.size = 0 then some 0 else
        some ((a % EvmYul.UInt256.size) / (b % EvmYul.UInt256.size)))
  by_cases hb : b % EvmYul.UInt256.size = 0
  · simp [hb]
  · simp [hb]

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

@[simp] theorem evalBuiltinCall_add_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "add" [a, b] =
      evalPureBuiltinViaEvmYulLean "add" [a, b] := by
  rw [verity_eval_add_normalized, bridge_eval_add_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

@[simp] theorem evalBuiltinCall_sub_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "sub" [a, b] =
      evalPureBuiltinViaEvmYulLean "sub" [a, b] := by
  rw [verity_eval_sub_normalized, bridge_eval_sub_normalized]
  have hb : b % evmModulus ≤ evmModulus := by
    exact Nat.le_of_lt (Nat.mod_lt _ (by simp [evmModulus]))
  have hsub : evmModulus + a % evmModulus - b % evmModulus =
      evmModulus - b % evmModulus + a % evmModulus := by
    omega
  simp [EvmYul.UInt256.size, evmModulus, hsub]

@[simp] theorem evalBuiltinCall_mul_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "mul" [a, b] =
      evalPureBuiltinViaEvmYulLean "mul" [a, b] := by
  rw [verity_eval_mul_normalized, bridge_eval_mul_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

@[simp] theorem evalBuiltinCall_div_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "div" [a, b] =
      evalPureBuiltinViaEvmYulLean "div" [a, b] := by
  rw [verity_eval_div_normalized, bridge_eval_div_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

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

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_add_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "add" [a, b] =
      evalBuiltinCall storage sender selector calldata "add" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallViaEvmYulLean, evalBuiltinCall_add_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_sub_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "sub" [a, b] =
      evalBuiltinCall storage sender selector calldata "sub" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallViaEvmYulLean, evalBuiltinCall_sub_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_mul_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "mul" [a, b] =
      evalBuiltinCall storage sender selector calldata "mul" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallViaEvmYulLean, evalBuiltinCall_mul_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_div_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "div" [a, b] =
      evalBuiltinCall storage sender selector calldata "div" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallViaEvmYulLean, evalBuiltinCall_div_bridge]

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
