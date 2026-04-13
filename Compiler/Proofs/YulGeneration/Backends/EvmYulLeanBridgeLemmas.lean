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

/-! ## Signed Comparison Bridge Lemmas (slt, sgt)

Both Verity and EVMYulLean implement EVM two's complement signed comparison.
The proof strategy: both sides reduce to a 4-case analysis on the sign bits
(whether `a % 2^256 ≥ 2^255` and `b % 2^256 ≥ 2^255`), and in each case
the results agree.

Verity uses `Int256.toInt` (convert to `Int`, then `Int.<`).
EVMYulLean uses `sltBool` (case-split on `toNat ≥ 2^255`, then unsigned `<`). -/

/-- Helper: `toNat (fromBool b)` reduces to `if b then 1 else 0`. -/
private theorem toNat_fromBool (b : Bool) :
    EvmYul.UInt256.toNat (EvmYul.UInt256.fromBool b) = if b then 1 else 0 := by
  cases b <;> simp [EvmYul.UInt256.fromBool, Bool.toUInt256, EvmYul.UInt256.toNat,
    EvmYul.UInt256.ofNat, Id.run, Fin.ofNat, EvmYul.UInt256.size]

/-- UInt256 `<` reduces to Nat `<` on underlying Fin values.
    The standalone LT instance (lt a b := a.val < b.val) is the active one,
    NOT the Preorder-derived one (a ≤ b ∧ ¬b ≤ a). -/
@[simp] private theorem uint256_lt_val (a b : EvmYul.UInt256) :
    (a < b) ↔ (a.val.val < b.val.val) := Iff.rfl

@[simp] private theorem uint256_gt_val (a b : EvmYul.UInt256) :
    (a > b) ↔ (b.val.val < a.val.val) :=
  uint256_lt_val b a

/-- For Nat values cast to Int, Int emod equals cast of Nat mod.
    This is key for bridging Verity's Int arithmetic with EVMYulLean's Nat arithmetic. -/
private theorem int_natCast_emod (a M : Nat) :
    (↑a : Int) % (↑M : Int) = ↑(a % M) := by
  omega

set_option maxHeartbeats 16000000 in
/-- The Verity signed-less-than semantics agree with EVMYulLean's `sltBool`
    when both sides operate on the same reduced values `a % M` and `b % M`. -/
private theorem verity_slt_eq_evmyullean_sltBool (a b : Nat) :
    (if Verity.Core.Int256.toInt
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % evmModulus))) <
        Verity.Core.Int256.toInt
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % evmModulus)))
      then (1 : Nat) else 0) =
    (if EvmYul.UInt256.sltBool (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b)
      then (1 : Nat) else 0) := by
  have hma : a % evmModulus % Verity.Core.UINT256_MODULUS = a % evmModulus := by
    simp [evmModulus, Verity.Core.UINT256_MODULUS]
  have hmb : b % evmModulus % Verity.Core.UINT256_MODULUS = b % evmModulus := by
    simp [evmModulus, Verity.Core.UINT256_MODULUS]
  -- Phase 1: Unfold definitions but keep EvmYul.UInt256.size opaque so
  -- int_natCast_emod can rewrite ↑a % ↑UInt256.size to ↑(a % UInt256.size).
  -- This ensures Int and Nat sides use the same modular expressions.
  simp only [Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
    Verity.Core.Int256.signBit, Verity.Core.Int256.modulus,
    Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS, evmModulus, hma, hmb,
    EvmYul.UInt256.sltBool, EvmYul.UInt256.toNat, EvmYul.UInt256.ofNat,
    Id.run, Fin.ofNat, uint256_lt_val, Fin.val, int_natCast_emod]
  -- Phase 2: Now unfold UInt256.size to the literal.
  simp only [EvmYul.UInt256.size]
  -- Case-split on sign bits.
  by_cases ha : a % EvmYul.UInt256.size < 2 ^ 255 <;>
  by_cases hb : b % EvmYul.UInt256.size < 2 ^ 255
  -- Use simp_all only to prevent @[simp] Int.ofNat_emod from
  -- rewriting ↑(a % M) back to ↑a % ↑M (which breaks omega).
  all_goals simp_all only [EvmYul.UInt256.size, Int.ofNat_lt, not_lt,
    ite_true, ite_false, ite_not, decide_true, decide_false,
    Bool.true_and, Bool.false_and, Bool.true_or, Bool.false_or,
    ge_iff_le, not_le, Int.ofNat_le, Int.ofNat_nonneg]
  all_goals omega

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

private theorem bridge_eval_slt_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "slt" [a, b] =
      some (if EvmYul.UInt256.sltBool (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b)
        then 1 else 0) := by
  change some (EvmYul.UInt256.toNat (EvmYul.UInt256.slt (EvmYul.UInt256.ofNat a)
      (EvmYul.UInt256.ofNat b))) = _
  simp [EvmYul.UInt256.slt, EvmYul.UInt256.fromBool, toNat_fromBool]

set_option maxHeartbeats 4000000 in
/-- Universal bridge theorem for `slt`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_slt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "slt" [a, b] =
      evalPureBuiltinViaEvmYulLean "slt" [a, b] := by
  rw [verity_eval_slt_normalized, bridge_eval_slt_normalized,
    verity_slt_eq_evmyullean_sltBool]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_slt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "slt" [a, b] =
      evalBuiltinCall storage sender selector calldata "slt" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_slt_bridge]

set_option maxHeartbeats 16000000 in
/-- The Verity signed-greater-than semantics agree with EVMYulLean's `sgtBool`.
    `sgt(a, b)` is equivalent to `slt(b, a)`, so we reuse the slt equivalence. -/
private theorem verity_sgt_eq_evmyullean_sgtBool (a b : Nat) :
    (if Verity.Core.Int256.toInt
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % evmModulus))) <
        Verity.Core.Int256.toInt
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % evmModulus)))
      then (1 : Nat) else 0) =
    (if EvmYul.UInt256.sgtBool (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b)
      then (1 : Nat) else 0) := by
  have hma : a % evmModulus % Verity.Core.UINT256_MODULUS = a % evmModulus := by
    simp [evmModulus, Verity.Core.UINT256_MODULUS]
  have hmb : b % evmModulus % Verity.Core.UINT256_MODULUS = b % evmModulus := by
    simp [evmModulus, Verity.Core.UINT256_MODULUS]
  -- Phase 1: Unfold definitions but keep EvmYul.UInt256.size opaque so
  -- int_natCast_emod can rewrite ↑a % ↑UInt256.size to ↑(a % UInt256.size).
  simp only [Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
    Verity.Core.Int256.signBit, Verity.Core.Int256.modulus,
    Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS, evmModulus, hma, hmb,
    EvmYul.UInt256.sgtBool, EvmYul.UInt256.toNat, EvmYul.UInt256.ofNat,
    Id.run, Fin.ofNat, uint256_gt_val, uint256_lt_val, Fin.val, int_natCast_emod]
  -- Phase 2: Now unfold UInt256.size to the literal.
  simp only [EvmYul.UInt256.size]
  -- Case-split on sign bits.
  by_cases ha : a % EvmYul.UInt256.size < 2 ^ 255 <;>
  by_cases hb : b % EvmYul.UInt256.size < 2 ^ 255
  -- Use simp_all only to prevent @[simp] Int.ofNat_emod from
  -- rewriting ↑(a % M) back to ↑a % ↑M (which breaks omega).
  all_goals simp_all only [EvmYul.UInt256.size, Int.ofNat_lt, not_lt,
    ite_true, ite_false, ite_not, decide_true, decide_false,
    Bool.true_and, Bool.false_and, Bool.true_or, Bool.false_or,
    ge_iff_le, not_le, Int.ofNat_le, Int.ofNat_nonneg]
  all_goals omega

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

private theorem bridge_eval_sgt_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "sgt" [a, b] =
      some (if EvmYul.UInt256.sgtBool (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b)
        then 1 else 0) := by
  change some (EvmYul.UInt256.toNat (EvmYul.UInt256.sgt (EvmYul.UInt256.ofNat a)
      (EvmYul.UInt256.ofNat b))) = _
  simp [EvmYul.UInt256.sgt, EvmYul.UInt256.fromBool, toNat_fromBool]

set_option maxHeartbeats 4000000 in
/-- Universal bridge theorem for `sgt`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_sgt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "sgt" [a, b] =
      evalPureBuiltinViaEvmYulLean "sgt" [a, b] := by
  rw [verity_eval_sgt_normalized, bridge_eval_sgt_normalized,
    verity_sgt_eq_evmyullean_sgtBool]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_sgt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "sgt" [a, b] =
      evalBuiltinCall storage sender selector calldata "sgt" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_sgt_bridge]

/-! ## Remaining Builtin Bridge Lemmas — Status

Universal bridge proofs for the following builtins require local `lake build`
iteration to debug:

**Signed arithmetic** (sdiv, smod, sar, signextend):
- Two's complement arithmetic with absolute values and sign functions
- Complex conditional logic in the EVMYulLean definitions
- `sdiv` needs 4-case sign-bit analysis + `Fin` negation equivalence

**New pure builtins** (exp):
- `exp` needs modular exponentiation equivalence (`Nat.pow` vs `UInt256.pow`)

All these builtins are validated by concrete `native_decide` bridge tests
in `EvmYulLeanBridgeTest.lean` covering critical boundary values.

Phase 3 of issue #1722 will address universal proofs once local build
infrastructure is available. -/

end Compiler.Proofs.YulGeneration.Backends
