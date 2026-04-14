import Compiler.Proofs.YulGeneration.Builtins
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter
import Mathlib.Data.Nat.Bitwise

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Proofs.YulGeneration

private theorem word_lt_uint256_size (x : Nat) :
    x % EvmYul.UInt256.size < 2 ^ 256 := by
  simpa [EvmYul.UInt256.size] using Nat.mod_lt x (by decide : 0 < EvmYul.UInt256.size)

/-- `UInt256.ofNat` is invariant under reduction modulo `evmModulus`,
    since `UInt256.size = evmModulus`. -/
private theorem uint256_ofNat_mod_evmModulus (n : Nat) :
    EvmYul.UInt256.ofNat n = EvmYul.UInt256.ofNat (n % evmModulus) := by
  simp only [EvmYul.UInt256.ofNat, Id.run]
  congr 1; ext
  simp only [Fin.ofNat, EvmYul.UInt256.size, evmModulus, Nat.mod_mod]

private theorem verity_eval_add_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "add" [a, b] =
      some ((a + b) % evmModulus) := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

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
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

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
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

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
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

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

private theorem verity_eval_mod_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "mod" [a, b] =
      (if b % evmModulus = 0 then some 0 else some ((a % evmModulus) % (b % evmModulus))) := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

private theorem bridge_eval_mod_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "mod" [a, b] =
      (if b % EvmYul.UInt256.size = 0 then some 0 else
        some ((a % EvmYul.UInt256.size) % (b % EvmYul.UInt256.size))) := by
  change some (EvmYul.UInt256.toNat (EvmYul.UInt256.mod (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b))) =
      (if b % EvmYul.UInt256.size = 0 then some 0 else
        some ((a % EvmYul.UInt256.size) % (b % EvmYul.UInt256.size)))
  by_cases hb : b % EvmYul.UInt256.size = 0
  · have hb0val : ((EvmYul.UInt256.ofNat b).val).val = 0 := by
      change b % EvmYul.UInt256.size = 0
      exact hb
    have hb0 : (EvmYul.UInt256.ofNat b).val = 0 := Fin.ext hb0val
    simp [EvmYul.UInt256.mod, EvmYul.UInt256.toNat, hb, hb0]
  · have hb0 : ¬ (EvmYul.UInt256.ofNat b).val = 0 := by
      intro h
      apply hb
      exact congrArg Fin.val h
    rw [show EvmYul.UInt256.mod (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b) =
          ⟨(EvmYul.UInt256.ofNat a).val % (EvmYul.UInt256.ofNat b).val⟩ by
            simp [EvmYul.UInt256.mod, hb0]]
    simp [hb, EvmYul.UInt256.toNat]
    change (a % EvmYul.UInt256.size) % (b % EvmYul.UInt256.size) =
      (a % EvmYul.UInt256.size) % (b % EvmYul.UInt256.size)
    rfl

private theorem verity_eval_eq_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "eq" [a, b] =
      some (if a % evmModulus = b % evmModulus then 1 else 0) := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

private theorem bridge_eval_eq_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "eq" [a, b] =
      some (if a % EvmYul.UInt256.size = b % EvmYul.UInt256.size then 1 else 0) := by
  rfl

private theorem verity_eval_iszero_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a : Nat) :
    evalBuiltinCall storage sender selector calldata "iszero" [a] =
      some (if a % evmModulus = 0 then 1 else 0) := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

private theorem bridge_eval_iszero_normalized (a : Nat) :
    evalPureBuiltinViaEvmYulLean "iszero" [a] =
      some (if a % EvmYul.UInt256.size = 0 then 1 else 0) := by
  rfl

set_option maxHeartbeats 2000000 in
private theorem verity_eval_lt_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "lt" [a, b] =
      some (if a % evmModulus < b % evmModulus then 1 else 0) := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

private theorem bridge_eval_lt_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "lt" [a, b] =
      some (if a % EvmYul.UInt256.size < b % EvmYul.UInt256.size then 1 else 0) := by
  rfl

set_option maxHeartbeats 2000000 in
private theorem verity_eval_gt_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "gt" [a, b] =
      some (if a % evmModulus > b % evmModulus then 1 else 0) := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

private theorem bridge_eval_gt_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "gt" [a, b] =
      some (if b % EvmYul.UInt256.size < a % EvmYul.UInt256.size then 1 else 0) := by
  rfl

private theorem bridge_eval_and_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "and" [a, b] =
      some (a % EvmYul.UInt256.size &&& b % EvmYul.UInt256.size) := by
  change some (((Nat.bitwise Bool.and (a % EvmYul.UInt256.size) (b % EvmYul.UInt256.size)) %
      EvmYul.UInt256.size)) =
    some (Nat.bitwise Bool.and (a % EvmYul.UInt256.size) (b % EvmYul.UInt256.size))
  congr 1
  rw [Nat.mod_eq_of_lt]
  exact Nat.bitwise_lt_two_pow (f := Bool.and) (n := 256)
    (word_lt_uint256_size a) (word_lt_uint256_size b)

private theorem bridge_eval_or_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "or" [a, b] =
      some (a % EvmYul.UInt256.size ||| b % EvmYul.UInt256.size) := by
  change some (((Nat.bitwise Bool.or (a % EvmYul.UInt256.size) (b % EvmYul.UInt256.size)) %
      EvmYul.UInt256.size)) =
    some (Nat.bitwise Bool.or (a % EvmYul.UInt256.size) (b % EvmYul.UInt256.size))
  congr 1
  rw [Nat.mod_eq_of_lt]
  exact Nat.bitwise_lt_two_pow (f := Bool.or) (n := 256)
    (word_lt_uint256_size a) (word_lt_uint256_size b)

private theorem bridge_eval_xor_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "xor" [a, b] =
      some (a % EvmYul.UInt256.size ^^^ b % EvmYul.UInt256.size) := by
  change some (((a % EvmYul.UInt256.size ^^^ b % EvmYul.UInt256.size) %
      EvmYul.UInt256.size)) =
    some (a % EvmYul.UInt256.size ^^^ b % EvmYul.UInt256.size)
  congr 1
  rw [Nat.mod_eq_of_lt]
  exact Nat.xor_lt_two_pow (word_lt_uint256_size a) (word_lt_uint256_size b)

private theorem xor_all_ones_uint256_word (a : Nat) :
    (a % EvmYul.UInt256.size) ^^^ (EvmYul.UInt256.size - 1) =
      EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size) := by
  calc
    (a % EvmYul.UInt256.size) ^^^ (EvmYul.UInt256.size - 1) =
        ((BitVec.ofNat 256 a) ^^^ BitVec.allOnes 256).toNat := by
      simp [BitVec.toNat_xor, EvmYul.UInt256.size]
    _ = (~~~(BitVec.ofNat 256 a)).toNat := by
      rw [BitVec.xor_allOnes]
    _ = EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size) := by
      simp [BitVec.toNat_not, EvmYul.UInt256.size]

private theorem bridge_eval_not_normalized (a : Nat) :
    evalPureBuiltinViaEvmYulLean "not" [a] =
      some ((a % EvmYul.UInt256.size) ^^^ (EvmYul.UInt256.size - 1)) := by
  have hsub : evalPureBuiltinViaEvmYulLean "not" [a] =
      some (EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size)) := by
    change evalPureBuiltinViaEvmYulLean "sub" [EvmYul.UInt256.size - 1, a] =
        some (EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size))
    rw [bridge_eval_sub_normalized]
    have hs : 0 < EvmYul.UInt256.size := by
      simp [EvmYul.UInt256.size]
    have ha : a % EvmYul.UInt256.size < EvmYul.UInt256.size := by
      exact Nat.mod_lt _ hs
    have hlt : EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size) < EvmYul.UInt256.size := by
      omega
    have hmod :
        ((EvmYul.UInt256.size - a % EvmYul.UInt256.size + (EvmYul.UInt256.size - 1)) %
          EvmYul.UInt256.size) =
        EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size) := by
      have harr :
          EvmYul.UInt256.size - a % EvmYul.UInt256.size + (EvmYul.UInt256.size - 1) =
            EvmYul.UInt256.size +
              (EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size)) := by
        omega
      calc
        ((EvmYul.UInt256.size - a % EvmYul.UInt256.size + (EvmYul.UInt256.size - 1)) %
            EvmYul.UInt256.size) =
            ((EvmYul.UInt256.size +
              (EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size))) %
              EvmYul.UInt256.size) := by
          rw [harr]
        _ = ((EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size)) % EvmYul.UInt256.size) := by
          rw [Nat.add_mod_left]
        _ = EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size) := by
          rw [Nat.mod_eq_of_lt hlt]
    simp [Nat.mod_eq_of_lt (by omega : EvmYul.UInt256.size - 1 < EvmYul.UInt256.size), hmod]
  rw [hsub]
  simp [xor_all_ones_uint256_word]

private theorem bridge_eval_shl_normalized (shift value : Nat) :
    evalPureBuiltinViaEvmYulLean "shl" [shift, value] =
      (if shift % EvmYul.UInt256.size < 256 then
        some (((value % EvmYul.UInt256.size) * 2 ^ (shift % EvmYul.UInt256.size)) %
          EvmYul.UInt256.size)
      else
        some 0) := by
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftLeft (EvmYul.UInt256.ofNat value) (EvmYul.UInt256.ofNat shift))) =
      (if shift % EvmYul.UInt256.size < 256 then
        some (((value % EvmYul.UInt256.size) * 2 ^ (shift % EvmYul.UInt256.size)) %
          EvmYul.UInt256.size)
      else
        some 0)
  by_cases hs : shift % EvmYul.UInt256.size < 256
  · have hs' : ¬ 256 ≤ (EvmYul.UInt256.ofNat shift).val := by
      change ¬ 256 ≤ shift % EvmYul.UInt256.size
      exact Nat.not_le_of_lt hs
    simp [hs, EvmYul.UInt256.shiftLeft, EvmYul.UInt256.toNat, hs', Nat.shiftLeft_eq]
    change (value % EvmYul.UInt256.size) * 2 ^ (shift % EvmYul.UInt256.size) %
        EvmYul.UInt256.size =
      value * 2 ^ (shift % EvmYul.UInt256.size) % EvmYul.UInt256.size
    rw [Nat.mul_mod, Nat.mul_mod]
    simp
  · have hs' : 256 ≤ (EvmYul.UInt256.ofNat shift).val := by
      change 256 ≤ shift % EvmYul.UInt256.size
      exact Nat.not_lt.mp hs
    simp [hs, EvmYul.UInt256.shiftLeft, EvmYul.UInt256.toNat, hs']

private theorem bridge_eval_shr_normalized (shift value : Nat) :
    evalPureBuiltinViaEvmYulLean "shr" [shift, value] =
      (if shift % EvmYul.UInt256.size < 256 then
        some ((value % EvmYul.UInt256.size) / 2 ^ (shift % EvmYul.UInt256.size))
      else
        some 0) := by
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftRight (EvmYul.UInt256.ofNat value) (EvmYul.UInt256.ofNat shift))) =
      (if shift % EvmYul.UInt256.size < 256 then
        some ((value % EvmYul.UInt256.size) / 2 ^ (shift % EvmYul.UInt256.size))
      else
        some 0)
  by_cases hs : shift % EvmYul.UInt256.size < 256
  · have hs' : ¬ 256 ≤ (EvmYul.UInt256.ofNat shift).val := by
      change ¬ 256 ≤ shift % EvmYul.UInt256.size
      exact Nat.not_le_of_lt hs
    simp [hs, EvmYul.UInt256.shiftRight, EvmYul.UInt256.toNat, hs', Nat.shiftRight_eq_div_pow]
    change value % EvmYul.UInt256.size / 2 ^ (shift % EvmYul.UInt256.size) =
      value % EvmYul.UInt256.size / 2 ^ (shift % EvmYul.UInt256.size)
    rfl
  · have hs' : 256 ≤ (EvmYul.UInt256.ofNat shift).val := by
      change 256 ≤ shift % EvmYul.UInt256.size
      exact Nat.not_lt.mp hs
    simp [hs, EvmYul.UInt256.shiftRight, EvmYul.UInt256.toNat, hs']

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

@[simp] theorem evalBuiltinCall_mod_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "mod" [a, b] =
      evalPureBuiltinViaEvmYulLean "mod" [a, b] := by
  rw [verity_eval_mod_normalized, bridge_eval_mod_normalized]
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

/-- Universal bridge theorem for `and`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_and_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "and" [a, b] =
      evalPureBuiltinViaEvmYulLean "and" [a, b] := by
  rw [show evalBuiltinCall storage sender selector calldata "and" [a, b] =
      some (a % evmModulus &&& b % evmModulus) by simp [evalBuiltinCall, evalBuiltinCallWithContext]]
  rw [bridge_eval_and_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

/-- Universal bridge theorem for `or`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_or_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "or" [a, b] =
      evalPureBuiltinViaEvmYulLean "or" [a, b] := by
  rw [show evalBuiltinCall storage sender selector calldata "or" [a, b] =
      some (a % evmModulus ||| b % evmModulus) by simp [evalBuiltinCall, evalBuiltinCallWithContext]]
  rw [bridge_eval_or_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

/-- Universal bridge theorem for `xor`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_xor_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "xor" [a, b] =
      evalPureBuiltinViaEvmYulLean "xor" [a, b] := by
  change some (Nat.bitwise bne (a % evmModulus) (b % evmModulus)) =
    evalPureBuiltinViaEvmYulLean "xor" [a, b]
  rw [bridge_eval_xor_normalized]
  simp [EvmYul.UInt256.size, evmModulus]
  rfl

/-- Universal bridge theorem for `not`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_not_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a : Nat) :
    evalBuiltinCall storage sender selector calldata "not" [a] =
      evalPureBuiltinViaEvmYulLean "not" [a] := by
  change some (a % evmModulus ^^^ (evmModulus - 1)) =
    evalPureBuiltinViaEvmYulLean "not" [a]
  rw [bridge_eval_not_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

/-- Universal bridge theorem for `shl`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_shl_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCall storage sender selector calldata "shl" [shift, value] =
      evalPureBuiltinViaEvmYulLean "shl" [shift, value] := by
  rw [show evalBuiltinCall storage sender selector calldata "shl" [shift, value] =
      (if shift % evmModulus < 256 then
        some (((value % evmModulus) * 2 ^ (shift % evmModulus)) % evmModulus)
      else
        some 0) by simp [evalBuiltinCall, evalBuiltinCallWithContext]]
  rw [bridge_eval_shl_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

/-- Universal bridge theorem for `shr`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_shr_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCall storage sender selector calldata "shr" [shift, value] =
      evalPureBuiltinViaEvmYulLean "shr" [shift, value] := by
  rw [show evalBuiltinCall storage sender selector calldata "shr" [shift, value] =
      (if shift % evmModulus < 256 then
        some ((value % evmModulus) / 2 ^ (shift % evmModulus))
      else
        some 0) by simp [evalBuiltinCall, evalBuiltinCallWithContext]]
  rw [bridge_eval_shr_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_add_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "add" [a, b] =
      evalBuiltinCall storage sender selector calldata "add" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_add_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_sub_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "sub" [a, b] =
      evalBuiltinCall storage sender selector calldata "sub" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_sub_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_mul_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "mul" [a, b] =
      evalBuiltinCall storage sender selector calldata "mul" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_mul_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_div_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "div" [a, b] =
      evalBuiltinCall storage sender selector calldata "div" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_div_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_mod_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "mod" [a, b] =
      evalBuiltinCall storage sender selector calldata "mod" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_mod_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_eq_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "eq" [a, b] =
      evalBuiltinCall storage sender selector calldata "eq" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_eq_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_iszero_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "iszero" [a] =
      evalBuiltinCall storage sender selector calldata "iszero" [a] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_iszero_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_lt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "lt" [a, b] =
      evalBuiltinCall storage sender selector calldata "lt" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_lt_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_gt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "gt" [a, b] =
      evalBuiltinCall storage sender selector calldata "gt" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_gt_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_and_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "and" [a, b] =
      evalBuiltinCall storage sender selector calldata "and" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_and_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_or_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "or" [a, b] =
      evalBuiltinCall storage sender selector calldata "or" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_or_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_xor_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "xor" [a, b] =
      evalBuiltinCall storage sender selector calldata "xor" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_xor_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_not_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "not" [a] =
      evalBuiltinCall storage sender selector calldata "not" [a] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_not_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_shl_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "shl" [shift, value] =
      evalBuiltinCall storage sender selector calldata "shl" [shift, value] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_shl_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_shr_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "shr" [shift, value] =
      evalBuiltinCall storage sender selector calldata "shr" [shift, value] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_shr_bridge]

/-! ## Addmod / Mulmod Bridge Lemmas

These are ternary operations with a conditional on the modulus being zero.
The key proof obligation is showing that the intermediate result is already
< UInt256.size when the modulus is nonzero, so the outer `% size` is a no-op. -/

private theorem verity_eval_addmod_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b n : Nat) :
    evalBuiltinCall storage sender selector calldata "addmod" [a, b, n] =
      (if n % evmModulus = 0 then some 0 else some (((a % evmModulus) + (b % evmModulus)) % (n % evmModulus))) := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

private theorem eq0_true_of_val_eq_zero (x : EvmYul.UInt256) (h : x.val = 0) :
    EvmYul.UInt256.eq0 x = true := by
  have hx : x = ⟨0⟩ := by cases x; exact congrArg EvmYul.UInt256.mk h
  subst hx; decide

/-- When `x.val ≠ 0`, eq0 returns false.
    Proof: case-split on eq0 result; in the true case, unfold derived BEq
    to Fin's decide-based BEq, extract x = ⟨0⟩, contradict x.val ≠ 0. -/
private theorem eq0_false_of_val_ne_zero (x : EvmYul.UInt256) (h : x.val ≠ 0) :
    EvmYul.UInt256.eq0 x = false := by
  cases hb : EvmYul.UInt256.eq0 x with
  | false => rfl
  | true =>
    exfalso; apply h
    cases x with | mk v =>
    -- hb : eq0 { val := v } = true, i.e., ({ val := v } == { val := 0 }) = true
    -- Derived BEq on UInt256 compares val fields, so this is (v == 0) = true
    simp only [EvmYul.UInt256.eq0] at hb
    -- Derived BEq on UInt256 compares val fields definitionally
    change (v == (0 : Fin EvmYul.UInt256.size)) = true at hb
    -- For Fin, BEq is from DecidableEq, so (v == 0) = decide (v = 0)
    have hv : v = (0 : Fin EvmYul.UInt256.size) := of_decide_eq_true hb
    simp [hv]

private theorem bridge_eval_addmod_normalized (a b n : Nat) :
    evalPureBuiltinViaEvmYulLean "addmod" [a, b, n] =
      (if n % EvmYul.UInt256.size = 0 then some 0 else
        some (((a % EvmYul.UInt256.size) + (b % EvmYul.UInt256.size)) % (n % EvmYul.UInt256.size))) := by
  change some (EvmYul.UInt256.toNat (EvmYul.UInt256.addMod
      (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b) (EvmYul.UInt256.ofNat n))) = _
  by_cases hn : n % EvmYul.UInt256.size = 0
  · -- n ≡ 0 (mod size): eq0 succeeds, result is 0
    have hn0 : (EvmYul.UInt256.ofNat n).val = 0 := Fin.ext hn
    have heq0 := eq0_true_of_val_eq_zero _ hn0
    simp only [EvmYul.UInt256.addMod, heq0]
    simp [hn, EvmYul.UInt256.toNat]
  · -- n ≢ 0 (mod size): eq0 fails, compute the modular sum
    have hn0 : (EvmYul.UInt256.ofNat n).val ≠ 0 := by
      intro hc; exact hn (congrArg Fin.val hc)
    have heq0 := eq0_false_of_val_ne_zero _ hn0
    simp only [EvmYul.UInt256.addMod, heq0]
    have hft : ¬(false = true) := by decide
    simp only [if_neg hft]
    simp [EvmYul.UInt256.toNat, EvmYul.UInt256.ofNat, Id.run, hn]
    -- Goal has Nat.mod (.mod) and HMod.hMod (%) which are definitionally equal.
    -- Use change to normalize to % notation so Nat.mod_eq_of_lt can match.
    change (a % EvmYul.UInt256.size + b % EvmYul.UInt256.size) %
        (n % EvmYul.UInt256.size) % EvmYul.UInt256.size =
      (a % EvmYul.UInt256.size + b % EvmYul.UInt256.size) % (n % EvmYul.UInt256.size)
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _
      (Nat.pos_of_ne_zero hn)) (Nat.le_of_lt (Nat.mod_lt n
      (by unfold EvmYul.UInt256.size; simp))))

private theorem verity_eval_mulmod_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b n : Nat) :
    evalBuiltinCall storage sender selector calldata "mulmod" [a, b, n] =
      (if n % evmModulus = 0 then some 0 else some (((a % evmModulus) * (b % evmModulus)) % (n % evmModulus))) := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

private theorem bridge_eval_mulmod_normalized (a b n : Nat) :
    evalPureBuiltinViaEvmYulLean "mulmod" [a, b, n] =
      (if n % EvmYul.UInt256.size = 0 then some 0 else
        some (((a % EvmYul.UInt256.size) * (b % EvmYul.UInt256.size)) % (n % EvmYul.UInt256.size))) := by
  change some (EvmYul.UInt256.toNat (EvmYul.UInt256.mulMod
      (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b) (EvmYul.UInt256.ofNat n))) = _
  by_cases hn : n % EvmYul.UInt256.size = 0
  · have hn0 : (EvmYul.UInt256.ofNat n).val = 0 := Fin.ext hn
    have heq0 := eq0_true_of_val_eq_zero _ hn0
    simp only [EvmYul.UInt256.mulMod, heq0]
    simp [hn, EvmYul.UInt256.toNat]
  · have hn0 : (EvmYul.UInt256.ofNat n).val ≠ 0 := by
      intro hc; exact hn (congrArg Fin.val hc)
    have heq0 := eq0_false_of_val_ne_zero _ hn0
    simp only [EvmYul.UInt256.mulMod, heq0]
    have hft : ¬(false = true) := by decide
    simp only [if_neg hft]
    simp [EvmYul.UInt256.toNat, EvmYul.UInt256.ofNat, Id.run, hn]
    -- Goal has Nat.mod (.mod) and HMod.hMod (%) which are definitionally equal.
    -- Use change to normalize to % notation so Nat.mod_eq_of_lt can match.
    change (a % EvmYul.UInt256.size * (b % EvmYul.UInt256.size)) %
        (n % EvmYul.UInt256.size) % EvmYul.UInt256.size =
      (a % EvmYul.UInt256.size * (b % EvmYul.UInt256.size)) % (n % EvmYul.UInt256.size)
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _
      (Nat.pos_of_ne_zero hn)) (Nat.le_of_lt (Nat.mod_lt n
      (by unfold EvmYul.UInt256.size; simp))))

/-- Universal bridge theorem for `addmod`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_addmod_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b n : Nat) :
    evalBuiltinCall storage sender selector calldata "addmod" [a, b, n] =
      evalPureBuiltinViaEvmYulLean "addmod" [a, b, n] := by
  rw [verity_eval_addmod_normalized, bridge_eval_addmod_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

/-- Universal bridge theorem for `mulmod`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_mulmod_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b n : Nat) :
    evalBuiltinCall storage sender selector calldata "mulmod" [a, b, n] =
      evalPureBuiltinViaEvmYulLean "mulmod" [a, b, n] := by
  rw [verity_eval_mulmod_normalized, bridge_eval_mulmod_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_addmod_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b n : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "addmod" [a, b, n] =
      evalBuiltinCall storage sender selector calldata "addmod" [a, b, n] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_addmod_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_mulmod_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b n : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "mulmod" [a, b, n] =
      evalBuiltinCall storage sender selector calldata "mulmod" [a, b, n] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_mulmod_bridge]


/-! ## Byte Bridge Lemma

The `byte` opcode extracts a single byte from a 256-bit word.
- Verity: `(x / 2^((31 - i) * 8)) % 256`
- EVMYulLean: `(x >>> ofNat((31 - i.toNat) * 8)) &&& 0xFF`

The proof uses `Nat.shiftRight_eq_div_pow` (shift = division by power of 2)
and `Nat.and_two_pow_sub_one_eq_mod` (AND with 2^k-1 = mod 2^k). -/

private theorem nat_land_0xFF (n : Nat) : Nat.land n 255 = n % 256 := by
  rw [show (255 : Nat) = 2 ^ 8 - 1 from by omega]
  exact Nat.and_two_pow_sub_one_eq_mod n 8

set_option maxHeartbeats 4000000 in
private theorem verity_eval_byte_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (i x : Nat) :
    evalBuiltinCall storage sender selector calldata "byte" [i, x] =
      (if i % evmModulus > 31 then some 0
       else some ((x % evmModulus / 2 ^ ((31 - i % evmModulus) * 8)) % 256)) := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

set_option maxHeartbeats 16000000 in
private theorem bridge_eval_byte_normalized (i x : Nat) :
    evalPureBuiltinViaEvmYulLean "byte" [i, x] =
      (if i % EvmYul.UInt256.size > 31 then some 0
       else some ((x % EvmYul.UInt256.size / 2 ^ ((31 - i % EvmYul.UInt256.size) * 8)) % 256)) := by
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.byteAt (EvmYul.UInt256.ofNat i) (EvmYul.UInt256.ofNat x))) = _
  by_cases hgt : i % EvmYul.UInt256.size > 31
  · -- pos case: i % size > 31, so byteAt returns 0
    have hgt' : EvmYul.UInt256.ofNat i > (⟨31⟩ : EvmYul.UInt256) := by
      show (31 : Fin EvmYul.UInt256.size) < (EvmYul.UInt256.ofNat i).val
      show (31 : Nat) < i % EvmYul.UInt256.size
      exact hgt
    simp [hgt, EvmYul.UInt256.byteAt, hgt', EvmYul.UInt256.toNat]
  · -- neg case: ¬(i % size > 31), so byteAt computes the byte
    have hle' : ¬(EvmYul.UInt256.ofNat i > (⟨31⟩ : EvmYul.UInt256)) := by
      show ¬((31 : Fin EvmYul.UInt256.size) < (EvmYul.UInt256.ofNat i).val)
      show ¬((31 : Nat) < i % EvmYul.UInt256.size)
      exact hgt
    have hshift_small : (31 - i % EvmYul.UInt256.size) * 8 < EvmYul.UInt256.size := by
      unfold EvmYul.UInt256.size; omega
    have hguard : ¬ 256 ≤ (EvmYul.UInt256.ofNat
        ((31 - (EvmYul.UInt256.ofNat i).toNat) * 8)).val := by
      change ¬ 256 ≤ ((31 - i % EvmYul.UInt256.size) * 8) % EvmYul.UInt256.size
      rw [Nat.mod_eq_of_lt hshift_small]; omega
    -- Unfold byteAt and eliminate its if
    unfold EvmYul.UInt256.byteAt
    rw [if_neg (show ¬(EvmYul.UInt256.ofNat i > (⟨31⟩ : EvmYul.UInt256)) from hle')]
    -- Convert typeclass notation (>>> and &&&) to direct function calls
    show some (EvmYul.UInt256.toNat
        (EvmYul.UInt256.land
          (EvmYul.UInt256.shiftRight (EvmYul.UInt256.ofNat x)
            (EvmYul.UInt256.ofNat ((31 - (EvmYul.UInt256.ofNat i).toNat) * 8)))
          ⟨255⟩)) = _
    -- Unfold shiftRight and eliminate its inner if
    unfold EvmYul.UInt256.shiftRight
    rw [if_neg hguard]
    -- Reduce all UInt256/Fin operations to Nat level
    -- Key addition: Fin.shiftRight + Fin.ofNat to reduce Fin-level >>> to Nat >>>
    simp only [hgt, ite_false, EvmYul.UInt256.land, EvmYul.UInt256.toNat,
      EvmYul.UInt256.ofNat, Id.run, Fin.land, Fin.shiftRight, Fin.ofNat,
      Nat.shiftRight_eq_div_pow]
    -- Goal should now be pure Nat with redundant % size operations
    -- Simplify: (31 - i%s)*8 % s = (31 - i%s)*8  (since < s)
    rw [Nat.mod_eq_of_lt hshift_small]
    -- Simplify: 255 % s = 255
    rw [show (255 : Nat) % EvmYul.UInt256.size = 255 from by unfold EvmYul.UInt256.size; omega]
    -- Simplify: (x%s / 2^k) % s = x%s / 2^k  (div result < s since input < s)
    have hdiv_lt : x % EvmYul.UInt256.size / 2 ^ ((31 - i % EvmYul.UInt256.size) * 8) <
        EvmYul.UInt256.size :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
        (Nat.mod_lt x (by unfold EvmYul.UInt256.size; omega))
    rw [Nat.mod_eq_of_lt hdiv_lt]
    -- Apply nat_land_0xFF: Nat.land n 255 = n % 256
    rw [nat_land_0xFF]
    -- Final: (x%s / 2^k) % 256 % s = (x%s / 2^k) % 256
    have hmod256_lt_size : (x % EvmYul.UInt256.size / 2 ^ ((31 - i % EvmYul.UInt256.size) * 8)) %
        256 < EvmYul.UInt256.size :=
      Nat.lt_trans (Nat.mod_lt _ (by omega)) (by unfold EvmYul.UInt256.size; omega)
    rw [Nat.mod_eq_of_lt hmod256_lt_size]

/-- Universal bridge theorem for `byte`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_byte_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (i x : Nat) :
    evalBuiltinCall storage sender selector calldata "byte" [i, x] =
      evalPureBuiltinViaEvmYulLean "byte" [i, x] := by
  rw [verity_eval_byte_normalized, bridge_eval_byte_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_byte_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (i x : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "byte" [i, x] =
      evalBuiltinCall storage sender selector calldata "byte" [i, x] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_byte_bridge]

/-! ## Signed Comparison Bridge Proofs (slt, sgt)

These proofs bridge between Verity's `Int256.toInt`-based signed comparison
(which interprets unsigned values as signed via two's complement and uses
`Int.<`) and EVMYulLean's `sltBool`/`sgtBool` (which case-split on the sign bit
`2^255` and compare unsigned values directly in each quadrant). -/

/-- Helper: Verity's signed less-than on raw Nat inputs reduces to a comparison
via `Int256.toInt`. This normalizes `evalBuiltinCallWithContext` for `slt`. -/
set_option maxHeartbeats 4000000 in
private theorem verity_eval_slt_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "slt" [a, b] =
      some (if Verity.Core.Int256.toInt
              (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % evmModulus))) <
            Verity.Core.Int256.toInt
              (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % evmModulus)))
           then 1 else 0) := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

/-- Helper: EVMYulLean's slt reduces to a Bool-valued sign-bit case split. -/
private theorem bridge_eval_slt_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "slt" [a, b] =
      some (EvmYul.UInt256.toNat
        (EvmYul.UInt256.slt (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b))) := by
  rfl

/-- Helper: Verity's signed greater-than on raw Nat inputs reduces to a comparison
via `Int256.toInt`. This normalizes `evalBuiltinCallWithContext` for `sgt`. -/
set_option maxHeartbeats 4000000 in
private theorem verity_eval_sgt_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "sgt" [a, b] =
      some (if Verity.Core.Int256.toInt
              (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % evmModulus))) <
            Verity.Core.Int256.toInt
              (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % evmModulus)))
           then 1 else 0) := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

/-- Helper: EVMYulLean's sgt reduces to a Nat value. -/
private theorem bridge_eval_sgt_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "sgt" [a, b] =
      some (EvmYul.UInt256.toNat
        (EvmYul.UInt256.sgt (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b))) := by
  rfl

/-- Core lemma: Verity's Int256-based signed comparison agrees with EVMYulLean's
sign-bit case analysis for all inputs in [0, evmModulus).

The proof proceeds by case-splitting on the sign bit of each operand:
- Both positive (< 2^255): signed order = unsigned order
- Both negative (≥ 2^255): signed order = unsigned order (both shifted by -2^256)
- Negative/positive: negative < positive unconditionally
- Positive/negative: positive ≥ negative unconditionally -/
set_option maxHeartbeats 32000000 in
private theorem slt_int256_eq_sltBool (a b : Nat) (ha : a < evmModulus) (hb : b < evmModulus) :
    (if Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 ⟨a, ha⟩) <
        Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)
     then (1 : Nat) else 0) =
    (EvmYul.UInt256.toNat
      (EvmYul.UInt256.slt ⟨⟨a, ha⟩⟩ ⟨⟨b, hb⟩⟩)) := by
  unfold Verity.Core.Int256.toInt Verity.Core.Int256.ofUint256
  unfold EvmYul.UInt256.slt EvmYul.UInt256.sltBool EvmYul.UInt256.fromBool Bool.toUInt256
  unfold EvmYul.UInt256.toNat EvmYul.UInt256.ofNat Id.run
  simp only [Verity.Core.Int256.signBit, Verity.Core.Int256.modulus,
    Verity.Core.Uint256.modulus, EvmYul.UInt256.size]
  split_ifs <;> simp_all [evmModulus] <;> omega

/-- Universal bridge theorem for `slt`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_slt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "slt" [a, b] =
      evalPureBuiltinViaEvmYulLean "slt" [a, b] := by
  rw [verity_eval_slt_normalized, bridge_eval_slt_normalized]
  have ha : a % evmModulus < evmModulus := Nat.mod_lt a (by unfold evmModulus; omega)
  have hb : b % evmModulus < evmModulus := Nat.mod_lt b (by unfold evmModulus; omega)
  congr 1
  conv_rhs =>
    rw [show EvmYul.UInt256.ofNat a = ⟨⟨a % evmModulus, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
        from by simp [EvmYul.UInt256.ofNat, Id.run, EvmYul.UInt256.size, evmModulus]]
    rw [show EvmYul.UInt256.ofNat b = ⟨⟨b % evmModulus, by rw [EvmYul.UInt256.size]; exact hb⟩⟩
        from by simp [EvmYul.UInt256.ofNat, Id.run, EvmYul.UInt256.size, evmModulus]]
  exact slt_int256_eq_sltBool (a % evmModulus) (b % evmModulus) ha hb

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_slt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "slt" [a, b] =
      evalBuiltinCall storage sender selector calldata "slt" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_slt_bridge]

/-- Core lemma: Verity's Int256-based signed greater-than agrees with EVMYulLean's
sign-bit case analysis for all inputs in [0, evmModulus). Same structure as
`slt_int256_eq_sltBool` but for `sgt`/`sgtBool`. -/
set_option maxHeartbeats 32000000 in
private theorem sgt_int256_eq_sgtBool (a b : Nat) (ha : a < evmModulus) (hb : b < evmModulus) :
    (if Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 ⟨b, hb⟩) <
        Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
     then (1 : Nat) else 0) =
    (EvmYul.UInt256.toNat
      (EvmYul.UInt256.sgt ⟨⟨a, ha⟩⟩ ⟨⟨b, hb⟩⟩)) := by
  unfold Verity.Core.Int256.toInt Verity.Core.Int256.ofUint256
  unfold EvmYul.UInt256.sgt EvmYul.UInt256.sgtBool EvmYul.UInt256.fromBool Bool.toUInt256
  unfold EvmYul.UInt256.toNat EvmYul.UInt256.ofNat Id.run
  simp only [Verity.Core.Int256.signBit, Verity.Core.Int256.modulus,
    Verity.Core.Uint256.modulus, EvmYul.UInt256.size]
  split_ifs <;> simp_all [evmModulus] <;> omega

/-- Universal bridge theorem for `sgt`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_sgt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "sgt" [a, b] =
      evalPureBuiltinViaEvmYulLean "sgt" [a, b] := by
  rw [verity_eval_sgt_normalized, bridge_eval_sgt_normalized]
  have ha : a % evmModulus < evmModulus := Nat.mod_lt a (by unfold evmModulus; omega)
  have hb : b % evmModulus < evmModulus := Nat.mod_lt b (by unfold evmModulus; omega)
  congr 1
  conv_rhs =>
    rw [show EvmYul.UInt256.ofNat a = ⟨⟨a % evmModulus, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
        from by simp [EvmYul.UInt256.ofNat, Id.run, EvmYul.UInt256.size, evmModulus]]
    rw [show EvmYul.UInt256.ofNat b = ⟨⟨b % evmModulus, by rw [EvmYul.UInt256.size]; exact hb⟩⟩
        from by simp [EvmYul.UInt256.ofNat, Id.run, EvmYul.UInt256.size, evmModulus]]
  exact sgt_int256_eq_sgtBool (a % evmModulus) (b % evmModulus) ha hb

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_sgt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "sgt" [a, b] =
      evalBuiltinCall storage sender selector calldata "sgt" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_sgt_bridge]

/-! ## State-dependent Builtin Fallthrough Lemmas

The EVMYulLean pure bridge intentionally returns `none` for state-dependent
builtins (`sload`, `caller`, `address`, etc.) because they require full
Yul state reconstruction. These lemmas prove that the fallthrough works
correctly: calling `evalBuiltinCallViaEvmYulLean` for a state-dependent
builtin yields `none`, so the dispatcher can fall back to Verity's path.

These are key building blocks for Phase 4 (retargeting the theorem stack),
where we need to prove that composing the pure bridge with the Verity
fallback covers all builtins. -/

/-- `evalPureBuiltinViaEvmYulLean` returns `none` for `sload`. -/
@[simp] theorem evalPureBuiltinViaEvmYulLean_sload (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "sload" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

/-- `evalPureBuiltinViaEvmYulLean` returns `none` for `caller`. -/
@[simp] theorem evalPureBuiltinViaEvmYulLean_caller (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "caller" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

/-- `evalPureBuiltinViaEvmYulLean` returns `none` for `address`. -/
@[simp] theorem evalPureBuiltinViaEvmYulLean_address (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "address" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

/-- `evalPureBuiltinViaEvmYulLean` returns `none` for `callvalue`. -/
@[simp] theorem evalPureBuiltinViaEvmYulLean_callvalue (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "callvalue" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

/-- `evalPureBuiltinViaEvmYulLean` returns `none` for `timestamp`. -/
@[simp] theorem evalPureBuiltinViaEvmYulLean_timestamp (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "timestamp" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

/-- `evalPureBuiltinViaEvmYulLean` returns `none` for `number`. -/
@[simp] theorem evalPureBuiltinViaEvmYulLean_number (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "number" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

/-- `evalPureBuiltinViaEvmYulLean` returns `none` for `chainid`. -/
@[simp] theorem evalPureBuiltinViaEvmYulLean_chainid (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "chainid" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

/-- `evalPureBuiltinViaEvmYulLean` returns `none` for `blobbasefee`. -/
@[simp] theorem evalPureBuiltinViaEvmYulLean_blobbasefee (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "blobbasefee" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

/-- `evalPureBuiltinViaEvmYulLean` returns `none` for `calldataload`. -/
@[simp] theorem evalPureBuiltinViaEvmYulLean_calldataload (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "calldataload" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

/-- `evalPureBuiltinViaEvmYulLean` returns `none` for `calldatasize`. -/
@[simp] theorem evalPureBuiltinViaEvmYulLean_calldatasize (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "calldatasize" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

/-- `evalPureBuiltinViaEvmYulLean` returns `none` for `mappingSlot`. -/
@[simp] theorem evalPureBuiltinViaEvmYulLean_mappingSlot (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "mappingSlot" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

/-! ## Context-Lifted Backend Bridge Theorems

The existing `evalBuiltinCallWithBackend_evmYulLean_*_bridge` theorems prove
backend equivalence at the `evalBuiltinCallWithBackend` level (which zeros out
context parameters like `msgValue`, `thisAddress`, etc.). These context-lifted
versions prove equivalence at the `evalBuiltinCallWithBackendContext` level —
which is what `Semantics.lean` actually calls — with **arbitrary** context
values.

This works because:
1. The `.evmYulLean` backend routes through `evalBuiltinCallViaEvmYulLean`,
   which ignores all context and delegates to `evalPureBuiltinViaEvmYulLean`.
2. Pure builtins in `evalBuiltinCallWithContext` only use `argVals`.

These are the key composition lemmas for Phase 4 (retargeting the theorem
stack to EVMYulLean). -/

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_add_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "add" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "add" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_add_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_sub_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "sub" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "sub" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_sub_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_mul_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "mul" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "mul" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_mul_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_div_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "div" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "div" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_div_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_mod_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "mod" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "mod" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_mod_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_eq_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "eq" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "eq" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_eq_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_iszero_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "iszero" [a] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "iszero" [a] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_iszero_bridge storage sender selector calldata a]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_lt_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "lt" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "lt" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_lt_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_gt_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "gt" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "gt" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_gt_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_slt_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "slt" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "slt" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_slt_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_sgt_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "sgt" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "sgt" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_sgt_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_and_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "and" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "and" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_and_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_or_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "or" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "or" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_or_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_xor_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "xor" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "xor" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_xor_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_not_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "not" [a] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "not" [a] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_not_bridge storage sender selector calldata a]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_shl_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "shl" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "shl" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_shl_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_shr_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "shr" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "shr" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_shr_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_addmod_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b c : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "addmod" [a, b, c] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "addmod" [a, b, c] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_addmod_bridge storage sender selector calldata a b c]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_mulmod_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b c : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "mulmod" [a, b, c] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "mulmod" [a, b, c] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_mulmod_bridge storage sender selector calldata a b c]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_byte_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (i x : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "byte" [i, x] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "byte" [i, x] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_byte_bridge storage sender selector calldata i x]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

/-! ## State-dependent Fallthrough at evalBuiltinCallWithBackendContext Level

These lift the `evalPureBuiltinViaEvmYulLean_*` fallthrough lemmas up to the
full `evalBuiltinCallWithBackendContext` dispatcher. Since the `.evmYulLean`
branch routes through `evalBuiltinCallViaEvmYulLean` → `evalPureBuiltinViaEvmYulLean`,
and the latter returns `none` for state-dependent builtins, the full dispatcher
also returns `none`.

These are essential for Phase 4: when we retarget from `.verity` to `.evmYulLean`,
we need to prove that state-dependent builtins are *not* handled by the EVMYulLean
path and must fall through to the Verity path. -/

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_sload_none
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (args : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "sload" args = none := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_caller_none
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (args : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "caller" args = none := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_address_none
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (args : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "address" args = none := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_callvalue_none
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (args : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "callvalue" args = none := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_timestamp_none
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (args : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "timestamp" args = none := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_number_none
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (args : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "number" args = none := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_chainid_none
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (args : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "chainid" args = none := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_blobbasefee_none
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (args : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "blobbasefee" args = none := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_calldataload_none
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (args : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "calldataload" args = none := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_calldatasize_none
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (args : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "calldatasize" args = none := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_mappingSlot_none
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (args : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "mappingSlot" args = none := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]

/-! ## Composite Backend Equivalence Theorem

This is the key Phase 4 composition lemma. For any pure builtin `func` in the
set of 18 universally-proved builtins, the EVMYulLean backend agrees with the
Verity backend (represented by `evalBuiltinCallWithContext`).

The theorem is structured as a disjunction: either `func` matches one of the
18 proven pure builtins (and the backends agree), or `func` is a state-dependent
builtin (and `.evmYulLean` returns `none`), or `func` is unknown.

We provide `evalBuiltinCallWithBackendContext_evmYulLean_pure_bridge` which
composites all 18 per-builtin bridges into a single result: for any function
in the proven set, the backends produce the same result with arbitrary context. -/

/-- For any of the 18 proven pure builtins, the EVMYulLean backend agrees with
    the Verity backend at the `evalBuiltinCallWithBackendContext` level.
    This factors through the individual `evalBuiltinCallWithBackendContext_evmYulLean_*_bridge`
    lemmas and is the primary rewrite target for Phase 4 retargeting. -/
theorem evalBuiltinCallWithBackendContext_evmYulLean_pure_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (func : String) (argVals : List Nat)
    (hpure : evalPureBuiltinViaEvmYulLean func argVals ≠ none) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata func argVals =
    evalBuiltinCallViaEvmYulLean storage sender selector calldata func argVals := by
  simp [evalBuiltinCallWithBackendContext]

/-! ## Remaining Builtin Bridge Lemmas — Status

Universal bridge proofs for the following builtins require local `lake build`
iteration to debug:

**Signed builtins** (slt, sgt, sdiv, smod, sar, signextend):
- `omega` cannot handle `Int.ofNat` goals with large constants (2^255, 2^256)
- `set_option maxHeartbeats` propagation through cascading error recovery
- UInt256 LT instance reduction through Fin/structure wrappers

**New pure builtins** (exp):
- `exp` needs modular exponentiation equivalence (`Nat.pow` vs `UInt256.pow`)

All these builtins are validated by concrete `native_decide` bridge tests
in `EvmYulLeanBridgeTest.lean` covering critical boundary values.

Phase 3 of issue #1722 will address universal proofs once local build
infrastructure is available.

**State-dependent builtin notes**:
- `chainid`: EVMYulLean hardcodes `chainId = 1` (`EvmYul.Wheels.chainId`),
  while Verity treats it as a state parameter. A state bridge proof would
  require constraining `state.chainId = 1`, which is not generally useful.
  This semantic mismatch should be resolved upstream in EVMYulLean before
  a state bridge proof is attempted. -/

end Compiler.Proofs.YulGeneration.Backends
