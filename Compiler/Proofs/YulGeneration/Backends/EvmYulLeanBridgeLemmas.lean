import Compiler.Proofs.YulGeneration.Builtins
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanSignedArithSpec
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

set_option maxHeartbeats 4000000 in
/-- Helper: Verity's signed less-than on raw Nat inputs reduces to a comparison
via `Int256.toInt`. This normalizes `evalBuiltinCallWithContext` for `slt`. -/
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

set_option maxHeartbeats 4000000 in
/-- Helper: Verity's signed greater-than on raw Nat inputs reduces to a comparison
via `Int256.toInt`. This normalizes `evalBuiltinCallWithContext` for `sgt`. -/
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

-- Helper: Int.ofNat preserves strict ordering on Nats
-- Note: omega in CI sees `Int.ofNat a` and `↑a` as different; use Int.ofNat_lt directly
private theorem int_ofNat_lt_iff {a b : Nat} : Int.ofNat a < Int.ofNat b ↔ a < b :=
  Int.ofNat_lt

-- Helper: shifting both sides of Int < by the same Nat value preserves ordering
private theorem int_sub_lt_sub_iff (a b M : Nat) :
    (Int.ofNat a - Int.ofNat M < Int.ofNat b - Int.ofNat M) ↔ (a < b) := by
  rw [sub_lt_sub_iff_right]
  exact Int.ofNat_lt

-- Helper: negative two's complement value (≥ 2^255) wrapped by -M is less than positive value (< 2^255)
private theorem int_neg_lt_pos_evm (a b : Nat) (haM : a < evmModulus) (_hb : b < 2 ^ 255) :
    Int.ofNat a - Int.ofNat evmModulus < Int.ofNat b := by
  have h1 : Int.ofNat a < Int.ofNat evmModulus := Int.ofNat_lt.mpr haM
  have h2 : (0 : Int) ≤ Int.ofNat b := Int.natCast_nonneg b
  omega

-- Helper: positive value (< 2^255) is never less than negative two's complement value wrapped by -M
private theorem int_pos_not_lt_neg_evm (a b : Nat) (_ha : a < 2 ^ 255) (hbM : b < evmModulus) :
    ¬ (Int.ofNat a < Int.ofNat b - Int.ofNat evmModulus) := by
  have h1 : Int.ofNat b < Int.ofNat evmModulus := Int.ofNat_lt.mpr hbM
  have h2 : (0 : Int) ≤ Int.ofNat a := Int.natCast_nonneg a
  omega

/-- Helper: `UInt256.toNat (Bool.toUInt256 b) = if b then 1 else 0`. -/
private theorem toNat_fromBool (b : Bool) :
    EvmYul.UInt256.toNat (Bool.toUInt256 b) = if b then 1 else 0 := by
  cases b <;> rfl

/-- Reduce `UInt256` `<` to `Nat` `<` on concrete constructors.  The direct `LT`
    instance forwards to `Fin.lt` which is definitionally `Nat.lt`. -/
private theorem uint256_lt_iff_nat_lt {a b : Nat}
    (ha : a < EvmYul.UInt256.size) (hb : b < EvmYul.UInt256.size) :
    ((⟨⟨a, ha⟩⟩ : EvmYul.UInt256) < ⟨⟨b, hb⟩⟩) ↔ (a < b) :=
  Iff.rfl

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 2048 in
/-- Core lemma: Verity's Int256-based signed comparison agrees with EVMYulLean's
sign-bit case analysis for all inputs in [0, evmModulus).

The proof works by case-splitting on the sign bits of both operands and
showing that Verity's `Int.ofNat - Int.ofNat modulus` representation agrees
with EVMYulLean's `sltBool` sign-bit dispatch in all four quadrants. -/
private theorem slt_int256_eq_sltBool (a b : Nat) (ha : a < evmModulus) (hb : b < evmModulus) :
    (if Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 ⟨a, ha⟩) <
        Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)
     then (1 : Nat) else 0) =
    (EvmYul.UInt256.toNat
      (EvmYul.UInt256.slt ⟨⟨a, ha⟩⟩ ⟨⟨b, hb⟩⟩)) := by
  -- Unfold slt to fromBool (sltBool ...) then rewrite toNat via toNat_fromBool
  -- BEFORE unfolding sltBool, keeping if-branches as Nat 1/0 (not UInt256 structs)
  unfold EvmYul.UInt256.slt
  rw [toNat_fromBool]
  -- Now unfold sltBool: Bool-valued sign-bit case analysis
  unfold EvmYul.UInt256.sltBool
  simp only [EvmYul.UInt256.toNat, ge_iff_le]
  -- Reduce UInt256 < to Nat <
  have ha' : a < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact ha
  have hb' : b < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hb
  simp only [uint256_lt_iff_nat_lt ha' hb']
  -- Unfold Verity side
  simp only [Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
    Verity.Core.Int256.signBit, Verity.Core.Int256.modulus,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
  -- Eliminate all `if` expressions, then close each branch with omega
  split_ifs <;> simp_all [evmModulus, EvmYul.UInt256.size] <;> omega

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
  have ha' : a % evmModulus < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact ha
  have hb' : b % evmModulus < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hb
  -- Normalize EvmYul.UInt256.ofNat to raw struct
  rw [show EvmYul.UInt256.ofNat a = (⟨⟨a % evmModulus, ha'⟩⟩ : EvmYul.UInt256)
      from by simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  rw [show EvmYul.UInt256.ofNat b = (⟨⟨b % evmModulus, hb'⟩⟩ : EvmYul.UInt256)
      from by simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  -- Normalize Verity.Core.Uint256.ofNat to raw struct matching slt_int256_eq_sltBool
  have hmod_a : (a % evmModulus) % Verity.Core.UINT256_MODULUS = a % evmModulus :=
    Nat.mod_eq_of_lt (by rw [Verity.Core.UINT256_MODULUS]; exact ha)
  have hmod_b : (b % evmModulus) % Verity.Core.UINT256_MODULUS = b % evmModulus :=
    Nat.mod_eq_of_lt (by rw [Verity.Core.UINT256_MODULUS]; exact hb)
  simp only [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, hmod_a, hmod_b]
  exact slt_int256_eq_sltBool (a % evmModulus) (b % evmModulus) ha hb

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_slt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "slt" [a, b] =
      evalBuiltinCall storage sender selector calldata "slt" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_slt_bridge]

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 2048 in
/-- Core lemma: Verity's Int256-based signed greater-than agrees with EVMYulLean's
sign-bit case analysis for all inputs in [0, evmModulus). Same structure as
`slt_int256_eq_sltBool` but for `sgt`/`sgtBool`. -/
private theorem sgt_int256_eq_sgtBool (a b : Nat) (ha : a < evmModulus) (hb : b < evmModulus) :
    (if Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 ⟨b, hb⟩) <
        Verity.Core.Int256.toInt (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
     then (1 : Nat) else 0) =
    (EvmYul.UInt256.toNat
      (EvmYul.UInt256.sgt ⟨⟨a, ha⟩⟩ ⟨⟨b, hb⟩⟩)) := by
  -- Unfold sgt to fromBool (sgtBool ...) then rewrite toNat via toNat_fromBool
  -- BEFORE unfolding sgtBool, keeping if-branches as Nat 1/0 (not UInt256 structs)
  unfold EvmYul.UInt256.sgt
  rw [toNat_fromBool]
  -- Now unfold sgtBool: Bool-valued sign-bit case analysis
  unfold EvmYul.UInt256.sgtBool
  simp only [EvmYul.UInt256.toNat, ge_iff_le, GT.gt]
  -- Reduce UInt256 < to Nat <
  have ha' : a < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact ha
  have hb' : b < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hb
  simp only [uint256_lt_iff_nat_lt hb' ha']
  -- Unfold Verity side
  simp only [Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
    Verity.Core.Int256.signBit, Verity.Core.Int256.modulus,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
  -- Eliminate all `if` expressions, then close each branch with omega
  split_ifs <;> simp_all [evmModulus, EvmYul.UInt256.size] <;> omega

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
  have ha' : a % evmModulus < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact ha
  have hb' : b % evmModulus < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hb
  -- Normalize EvmYul.UInt256.ofNat to raw struct
  rw [show EvmYul.UInt256.ofNat a = (⟨⟨a % evmModulus, ha'⟩⟩ : EvmYul.UInt256)
      from by simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  rw [show EvmYul.UInt256.ofNat b = (⟨⟨b % evmModulus, hb'⟩⟩ : EvmYul.UInt256)
      from by simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  -- Normalize Verity.Core.Uint256.ofNat to raw struct matching sgt_int256_eq_sgtBool
  have hmod_a : (a % evmModulus) % Verity.Core.UINT256_MODULUS = a % evmModulus :=
    Nat.mod_eq_of_lt (by rw [Verity.Core.UINT256_MODULUS]; exact ha)
  have hmod_b : (b % evmModulus) % Verity.Core.UINT256_MODULUS = b % evmModulus :=
    Nat.mod_eq_of_lt (by rw [Verity.Core.UINT256_MODULUS]; exact hb)
  simp only [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, hmod_a, hmod_b]
  exact sgt_int256_eq_sgtBool (a % evmModulus) (b % evmModulus) ha hb

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_sgt_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "sgt" [a, b] =
      evalBuiltinCall storage sender selector calldata "sgt" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_sgt_bridge]

/-! ## Exp Bridge Proof

The `exp` bridge connects Verity's `natModPow` (repeated-squaring on Nat)
with EVMYulLean's `UInt256.pow` (repeated-squaring on Fin 2^256).
Both implement binary exponentiation but differ in representation:
Verity uses explicit `% modulus` while EVMYulLean uses implicit Fin wrapping.

The core equivalence requires showing both repeated-squaring loops compute
the same result. This needs an induction proof matching the loop invariants. -/

private theorem verity_eval_exp_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "exp" [a, b] =
      some (natModPow (a % evmModulus) (b % evmModulus) evmModulus) := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

private theorem bridge_eval_exp_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "exp" [a, b] =
      some (EvmYul.UInt256.toNat
        (EvmYul.UInt256.exp (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b))) := by
  rfl

/-- UInt256 multiplication extracts to modular Nat multiplication. -/
private theorem uint256_mul_toNat (x y : EvmYul.UInt256) :
    (x * y).toNat = (x.toNat * y.toNat) % EvmYul.UInt256.size := by
  show (EvmYul.UInt256.mul x y).val.val = (x.val.val * y.val.val) % EvmYul.UInt256.size
  simp [EvmYul.UInt256.mul]
  exact Fin.val_mul x.val y.val

/-- `evmModulus` equals `EvmYul.UInt256.size`. -/
private theorem evmModulus_eq_uint256Size : evmModulus = EvmYul.UInt256.size := by
  unfold evmModulus EvmYul.UInt256.size; rfl

/-- UInt256.toNat is always less than UInt256.size. -/
private theorem uint256_toNat_lt (x : EvmYul.UInt256) : x.toNat < EvmYul.UInt256.size :=
  x.val.isLt

/-- The generalized loop equivalence: `modPowAux` on Nat values agrees with
`powAux` on UInt256 values, for all exponents and accumulator/base states.
This is the induction core for the exp bridge. -/
private theorem modPowAux_eq_powAux (acc base : EvmYul.UInt256) :
    ∀ (e : Nat), modPowAux EvmYul.UInt256.size base.toNat e acc.toNat =
      (EvmYul.UInt256.powAux acc base e).toNat := by
  intro e
  induction e using Nat.strongRecOn generalizing acc base with
  | _ e ih =>
    match e with
    | 0 =>
      unfold modPowAux EvmYul.UInt256.powAux
      exact Nat.mod_eq_of_lt (uint256_toNat_lt acc)
    | e + 1 =>
      unfold modPowAux
      rw [EvmYul.UInt256.powAux]
      have hdiv : (e + 1) / 2 < e + 1 := Nat.div_lt_self (by omega) (by omega)
      -- Both sides branch on whether (e+1) is odd.
      -- LHS uses: if (e+1) % 2 = 1 then ... (Prop equality)
      -- RHS uses: if ((e+1) % 2 == 1) = true then ... (BEq)
      -- These are equivalent for Nat, so we case-split on the Prop and derive the BEq
      by_cases hodd : (e + 1) % 2 = 1
      · -- Odd case: both multiply accumulator by base
        -- LHS: modPowAux simplifies its if using hodd (Prop)
        simp only [hodd, ite_true]
        -- RHS: powAux already evaluated (e+1)%2 to 1, giving `if (1 == 1) = true`
        -- which reduces to `if true = true`, i.e. the then-branch
        simp (config := { decide := true }) only [ite_true]
        -- Both sides recurse with (acc*base, base*base, (e+1)/2)
        have := ih ((e + 1) / 2) hdiv (acc * base) (base * base)
        rw [uint256_mul_toNat acc base, uint256_mul_toNat base base] at this
        exact this
      · -- Even case: accumulator unchanged
        -- LHS: modPowAux if is false
        simp only [hodd, ite_false]
        -- RHS has `if (e.succ % 2 == 1) = true`. Since hodd: ¬(e+1)%2 = 1,
        -- we know e.succ%2 = 0, so (0 == 1) = false, so if branch goes to else
        have hmod_zero : e.succ % 2 = 0 := by omega
        rw [hmod_zero]
        -- Now RHS has `if (0 == 1) = true` which is `if false = true`
        -- Use norm_num to evaluate the BEq and simplify the if
        norm_num
        -- Both sides recurse with (acc, base*base, (e+1)/2)
        have := ih ((e + 1) / 2) hdiv acc (base * base)
        rw [uint256_mul_toNat base base] at this
        exact this

/-- Core exp equivalence: Verity's `natModPow` agrees with EVMYulLean's `UInt256.exp`
on all inputs. Both implement modular exponentiation via repeated squaring.

The proof proceeds by strong induction on the exponent, showing that both
repeated-squaring loops compute identical results because UInt256 Fin wrapping
is equivalent to explicit `% modulus` on Nat values. -/
private theorem exp_natModPow_eq_uint256Exp (a b : Nat)
    (ha : a < evmModulus) (hb : b < evmModulus) :
    natModPow a b evmModulus =
    EvmYul.UInt256.toNat (EvmYul.UInt256.exp ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
                                               ⟨⟨b, by rw [EvmYul.UInt256.size]; exact hb⟩⟩) := by
  -- Unfold natModPow: since evmModulus > 1, we get modPowAux
  unfold natModPow
  have hmod_gt : ¬ (evmModulus ≤ 1) := by unfold evmModulus; omega
  simp only [hmod_gt, ite_false]
  -- Since a < evmModulus, a % evmModulus = a
  have ha_mod : a % evmModulus = a := Nat.mod_eq_of_lt ha
  rw [evmModulus_eq_uint256Size] at ha_mod ⊢
  rw [ha_mod]
  -- Unfold exp → pow → powAux
  unfold EvmYul.UInt256.exp EvmYul.UInt256.pow
  -- Apply the generalized loop equivalence
  -- The goal after unfold has specific UInt256 values; show they match
  -- powAux ⟨1⟩ ⟨⟨a,_⟩⟩ (↑⟨b,_⟩) where ↑ is Fin.val coercion giving b
  -- We need to instantiate modPowAux_eq_powAux with matching acc/base
  have key := modPowAux_eq_powAux
    (⟨⟨1, by rw [EvmYul.UInt256.size]; omega⟩⟩ : EvmYul.UInt256)
    (⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩ : EvmYul.UInt256)
    b
  -- key : modPowAux size (⟨⟨a,_⟩⟩).toNat b (⟨⟨1,_⟩⟩).toNat = (powAux ⟨⟨1,_⟩⟩ ⟨⟨a,_⟩⟩ b).toNat
  -- toNat of ⟨⟨x,_⟩⟩ is x, so this simplifies to our goal
  simp only [EvmYul.UInt256.toNat] at key
  exact key

/-- Universal bridge theorem for `exp`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_exp_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "exp" [a, b] =
      evalPureBuiltinViaEvmYulLean "exp" [a, b] := by
  rw [verity_eval_exp_normalized, bridge_eval_exp_normalized]
  have ha : a % evmModulus < evmModulus := Nat.mod_lt a (by unfold evmModulus; omega)
  have hb : b % evmModulus < evmModulus := Nat.mod_lt b (by unfold evmModulus; omega)
  congr 1
  have ha' : a % evmModulus < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact ha
  have hb' : b % evmModulus < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hb
  rw [show EvmYul.UInt256.ofNat a = (⟨⟨a % evmModulus, ha'⟩⟩ : EvmYul.UInt256)
      from by simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  rw [show EvmYul.UInt256.ofNat b = (⟨⟨b % evmModulus, hb'⟩⟩ : EvmYul.UInt256)
      from by simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  exact exp_natModPow_eq_uint256Exp (a % evmModulus) (b % evmModulus) ha hb

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_exp_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "exp" [a, b] =
      evalBuiltinCall storage sender selector calldata "exp" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_exp_bridge]

/-! ## Sdiv Bridge Proof

The `sdiv` bridge connects Verity's `Int256.div` (sign-magnitude division via Int)
with EVMYulLean's `UInt256.sdiv` (sign-bit case-split with abs/negate). Both
implement EVM SDIV: signed division with truncation toward zero, where
`sdiv(MIN_INT256, -1) = MIN_INT256`. -/

private theorem verity_eval_sdiv_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "sdiv" [a, b] =
      some (Verity.Core.Int256.div
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % evmModulus)))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % evmModulus)))).toUint256.val := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

private theorem bridge_eval_sdiv_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "sdiv" [a, b] =
      some (EvmYul.UInt256.toNat
        (EvmYul.UInt256.sdiv (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b))) := by
  rfl

/-- In Fin n, `x * (n - 1) % n = n - x` when `0 < x < n`. This captures the
    semantics of EVMYulLean's `⟨v.val * (-1)⟩` negation via Fin multiplication. -/
private theorem fin_val_mul_neg1 (n x : Nat) (hn : 0 < n) (hx : x < n) (hxpos : 0 < x) :
    (x * (n - 1)) % n = n - x := by
  -- x * (n - 1) + x = x * n (uses left_distrib to factor out x)
  have h1le : 1 ≤ n := hn
  have hadd : x * (n - 1) + x = x * n := by
    have : x * (n - 1) + x * 1 = x * n := by
      rw [← Nat.left_distrib, Nat.sub_add_cancel h1le]
    rwa [Nat.mul_one] at this
  -- (x - 1) * n + n = x * n (uses left_distrib to factor out n)
  have h1lex : 1 ≤ x := hxpos
  have hadd2 : (x - 1) * n + n = x * n := by
    have : (x - 1) * n + 1 * n = x * n := by
      rw [← Nat.right_distrib, Nat.sub_add_cancel h1lex]
    rwa [Nat.one_mul] at this
  -- Therefore x * (n - 1) = (x - 1) * n + (n - x) (both + x give x * n)
  have hdiv : x * (n - 1) = (x - 1) * n + (n - x) := by omega
  rw [hdiv]
  exact Nat.mul_add_mod_of_lt (by omega)

private theorem natAbs_ofNat_sub (a b : Nat) (h : a < b) :
    (Int.ofNat a - Int.ofNat b).natAbs = b - a := by
  simp only [Int.ofNat_eq_coe]
  rw [show (a : Int) - ((b : Nat) : Int) = -(((b : Nat) : Int) - (a : Int)) from by omega]
  rw [Int.natAbs_neg]
  rw [show ((b : Nat) : Int) - (a : Int) = ((b - a : Nat) : Int) from by omega]
  simp only [Int.natAbs_natCast]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 4096 in
/-- Core sdiv equivalence: Verity's `Int256.div` agrees with EVMYulLean's `UInt256.sdiv`.

Both implement signed division by:
1. Case-splitting on the sign bit (2^255 threshold)
2. Taking absolute values (Verity: `Int.natAbs`; EVMYulLean: `UInt256.abs`)
3. Dividing the absolute values
4. Negating the result if signs differ

Proved via 5-way case analysis: b=0, PP, PN, NP, NN. -/
private theorem sdiv_int256_eq_uint256Sdiv (a b : Nat)
    (ha : a < evmModulus) (hb : b < evmModulus) :
    (Verity.Core.Int256.div
      (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
      (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)).toUint256.val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.sdiv ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
                                               ⟨⟨b, by rw [EvmYul.UInt256.size]; exact hb⟩⟩) := by
  -- Unfold evmModulus so omega can relate to 2^256
  unfold evmModulus at ha hb
  by_cases hb0 : b = 0
  · -- b = 0: both sides return 0
    subst hb0
    simp only [Verity.Core.Int256.div, Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
      Verity.Core.Int256.signBit, Verity.Core.Int256.signedAbsNat,
      Verity.Core.Int256.ofInt, Verity.Core.Int256.toUint256,
      Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
      Verity.Core.Uint256.ofNat,
      EvmYul.UInt256.sdiv, EvmYul.UInt256.abs, EvmYul.UInt256.toNat,
      EvmYul.UInt256.size,
      HDiv.hDiv, Div.div, EvmYul.UInt256.div, Fin.div]
    simp only [show (0 : Nat) < 2^255 from by omega,
      show ¬(2^255 ≤ (0:Nat)) from by omega, ↓reduceIte]
    norm_num
    conv_rhs => simp only [show ∀ (n : Nat), Nat.div n 0 = 0 from Nat.div_zero]
    split <;> simp [Neg.neg] <;> decide
  · -- b ≠ 0
    by_cases haS : a < 2 ^ 255 <;> by_cases hbS : b < 2 ^ 255
    · -- PP case: a < 2^255, b < 2^255 (both positive)
      simp only [Verity.Core.Int256.div, Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
        Verity.Core.Int256.signBit, Verity.Core.Int256.signedAbsNat,
        Verity.Core.Int256.ofInt, Verity.Core.Int256.toUint256,
        Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
        Verity.Core.Uint256.ofNat,
        EvmYul.UInt256.sdiv, EvmYul.UInt256.abs, EvmYul.UInt256.toNat,
        EvmYul.UInt256.size]
      simp only [eq_true haS, eq_true hbS, ↓reduceIte,
        eq_false (show ¬(2^255 ≤ a) from by omega),
        eq_false (show ¬(2^255 ≤ b) from by omega),
        eq_false (show ¬((Int.ofNat b : Int) = 0) from Int.ofNat_ne_zero.mpr hb0),
        eq_false (show ¬(Int.ofNat a < (0 : Int)) from not_lt.mpr (Int.natCast_nonneg a)),
        eq_false (show ¬(Int.ofNat b < (0 : Int)) from not_lt.mpr (Int.natCast_nonneg b)),
        decide_false]
      simp only [BEq.beq, decide_true, ↓reduceIte]
      simp only [Int.natAbs]
      simp only [eq_false (show ¬(Int.ofNat (a / b) < (0 : Int)) from not_lt.mpr (Int.natCast_nonneg _)),
        ↓reduceIte]
      simp only [Int.toNat]
      simp only [HDiv.hDiv, Div.div, EvmYul.UInt256.div, Fin.div]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha)
    · -- PN case: a < 2^255, b ≥ 2^255 (a positive, b negative)
      have hb' : (Int.ofNat b : Int) < Int.ofNat (2^256) := Int.ofNat_lt.mpr hb
      simp only [Verity.Core.Int256.div, Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
        Verity.Core.Int256.signBit, Verity.Core.Int256.signedAbsNat,
        Verity.Core.Int256.ofInt, Verity.Core.Int256.toUint256,
        Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
        Verity.Core.Uint256.ofNat,
        EvmYul.UInt256.sdiv, EvmYul.UInt256.abs, EvmYul.UInt256.toNat,
        EvmYul.UInt256.size]
      simp only [eq_true haS, eq_false hbS,
        eq_false (show ¬(2^255 ≤ a) from by omega),
        eq_true (show 2^255 ≤ b from by omega), ↓reduceIte,
        eq_false (show ¬(Int.ofNat b - Int.ofNat (2^256) = (0 : Int)) from by omega),
        eq_false (show ¬(Int.ofNat a < (0 : Int)) from not_lt.mpr (Int.natCast_nonneg a)),
        eq_true (show Int.ofNat b - Int.ofNat (2^256) < (0 : Int) from by omega)]
      simp only [BEq.beq, decide_false]
      simp only [show (Int.ofNat a).natAbs = a from rfl,
                 natAbs_ofNat_sub b (2^256) hb]
      simp only [HDiv.hDiv, Div.div, EvmYul.UInt256.div, Fin.div, Fin.mul]
      norm_num
      have habs_b_lit : b * 115792089237316195423570985008687907853269984665640564039457584007913129639935 %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 - b := by
        have := fin_val_mul_neg1 (2^256) b (by omega) hb (by omega)
        norm_num at this; exact this
      simp only [habs_b_lit]
      simp only [Fin.val_neg]
      split
      · rename_i hqpos
        have hqlt : a.div (115792089237316195423570985008687907853269984665640564039457584007913129639936 - b) <
          115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
          Nat.lt_of_le_of_lt (Nat.div_le_self a _) ha
        split
        · rename_i h_fin_zero
          exfalso; have hval := Fin.val_eq_of_eq h_fin_zero; simp at hval; omega
        · show (115792089237316195423570985008687907853269984665640564039457584007913129639936 -
              a.div (115792089237316195423570985008687907853269984665640564039457584007913129639936 - b) %
                115792089237316195423570985008687907853269984665640564039457584007913129639936) %
              115792089237316195423570985008687907853269984665640564039457584007913129639936 =
            115792089237316195423570985008687907853269984665640564039457584007913129639936 -
              a.div (115792089237316195423570985008687907853269984665640564039457584007913129639936 - b)
          rw [Nat.mod_eq_of_lt hqlt]
          exact Nat.mod_eq_of_lt (by omega)
      · rename_i hq0
        split
        · rfl
        · rename_i h_fin_ne; exfalso; apply h_fin_ne
          have : a.div (115792089237316195423570985008687907853269984665640564039457584007913129639936 - b) = 0 := by omega
          ext; simp [this]
    · -- NP case: a ≥ 2^255, b < 2^255 (a negative, b positive)
      have ha' : (Int.ofNat a : Int) < Int.ofNat (2^256) := Int.ofNat_lt.mpr ha
      simp only [Verity.Core.Int256.div, Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
        Verity.Core.Int256.signBit, Verity.Core.Int256.signedAbsNat,
        Verity.Core.Int256.ofInt, Verity.Core.Int256.toUint256,
        Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
        Verity.Core.Uint256.ofNat,
        EvmYul.UInt256.sdiv, EvmYul.UInt256.abs, EvmYul.UInt256.toNat,
        EvmYul.UInt256.size]
      simp only [eq_false haS, eq_true hbS,
        eq_true (show 2^255 ≤ a from by omega),
        eq_false (show ¬(2^255 ≤ b) from by omega), ↓reduceIte,
        eq_true (show Int.ofNat a - Int.ofNat (2^256) < (0 : Int) from by omega),
        eq_false (show ¬(Int.ofNat b < (0 : Int)) from not_lt.mpr (Int.natCast_nonneg b)),
        eq_false (show ¬((Int.ofNat b : Int) = 0) from Int.ofNat_ne_zero.mpr hb0)]
      simp only [BEq.beq, decide_false]
      simp only [natAbs_ofNat_sub a (2^256) ha,
                 show (Int.ofNat b).natAbs = b from rfl]
      simp only [HDiv.hDiv, Div.div, EvmYul.UInt256.div, Fin.div, Fin.mul]
      norm_num
      have habs_a_lit : a * 115792089237316195423570985008687907853269984665640564039457584007913129639935 %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 - a := by
        have := fin_val_mul_neg1 (2^256) a (by omega) ha (by omega)
        norm_num at this; exact this
      simp only [habs_a_lit]
      simp only [Fin.val_neg]
      split
      · rename_i hqpos
        have hqlt : (115792089237316195423570985008687907853269984665640564039457584007913129639936 - a).div b <
          115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
          Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
        split
        · rename_i h_fin_zero
          exfalso; have hval := Fin.val_eq_of_eq h_fin_zero; simp at hval; omega
        · show (115792089237316195423570985008687907853269984665640564039457584007913129639936 -
              (115792089237316195423570985008687907853269984665640564039457584007913129639936 - a).div b %
                115792089237316195423570985008687907853269984665640564039457584007913129639936) %
              115792089237316195423570985008687907853269984665640564039457584007913129639936 =
            115792089237316195423570985008687907853269984665640564039457584007913129639936 -
              (115792089237316195423570985008687907853269984665640564039457584007913129639936 - a).div b
          rw [Nat.mod_eq_of_lt hqlt]
          exact Nat.mod_eq_of_lt (by omega)
      · rename_i hq0
        split
        · rfl
        · rename_i h_fin_ne; exfalso; apply h_fin_ne
          have : (115792089237316195423570985008687907853269984665640564039457584007913129639936 - a).div b = 0 := by omega
          ext; simp [this]
    · -- NN case: a ≥ 2^255, b ≥ 2^255 (both negative)
      have ha' : (Int.ofNat a : Int) < Int.ofNat (2^256) := Int.ofNat_lt.mpr ha
      have hb' : (Int.ofNat b : Int) < Int.ofNat (2^256) := Int.ofNat_lt.mpr hb
      simp only [Verity.Core.Int256.div, Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
        Verity.Core.Int256.signBit, Verity.Core.Int256.signedAbsNat,
        Verity.Core.Int256.ofInt, Verity.Core.Int256.toUint256,
        Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
        Verity.Core.Uint256.ofNat,
        EvmYul.UInt256.sdiv, EvmYul.UInt256.abs, EvmYul.UInt256.toNat,
        EvmYul.UInt256.size]
      simp only [eq_false haS, eq_false hbS,
        eq_true (show 2^255 ≤ a from by omega),
        eq_true (show 2^255 ≤ b from by omega), ↓reduceIte,
        eq_false (show ¬(Int.ofNat b - Int.ofNat (2^256) = (0 : Int)) from by omega),
        eq_true (show Int.ofNat a - Int.ofNat (2^256) < (0 : Int) from by omega),
        eq_true (show Int.ofNat b - Int.ofNat (2^256) < (0 : Int) from by omega)]
      simp only [BEq.beq]
      simp only [natAbs_ofNat_sub a (2^256) ha,
                 natAbs_ofNat_sub b (2^256) hb]
      simp only [decide_true, ↓reduceIte,
        eq_false (show ¬(Int.ofNat ((2^256 - a) / (2^256 - b)) < (0 : Int)) from
          not_lt.mpr (Int.natCast_nonneg _))]
      simp only [Int.toNat]
      simp only [HDiv.hDiv, Div.div, EvmYul.UInt256.div, Fin.div, Fin.mul]
      norm_num
      rw [fin_val_mul_neg1 (2^256) a (by omega) ha (by omega),
          fin_val_mul_neg1 (2^256) b (by omega) hb (by omega)]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))

/-- Universal bridge theorem for `sdiv`. -/
@[simp] theorem evalBuiltinCall_sdiv_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "sdiv" [a, b] =
      evalPureBuiltinViaEvmYulLean "sdiv" [a, b] := by
  rw [verity_eval_sdiv_normalized, bridge_eval_sdiv_normalized]
  have ha : a % evmModulus < evmModulus := Nat.mod_lt a (by unfold evmModulus; omega)
  have hb : b % evmModulus < evmModulus := Nat.mod_lt b (by unfold evmModulus; omega)
  congr 1
  have ha' : a % evmModulus < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact ha
  have hb' : b % evmModulus < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hb
  rw [show EvmYul.UInt256.ofNat a = (⟨⟨a % evmModulus, ha'⟩⟩ : EvmYul.UInt256)
      from by simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  rw [show EvmYul.UInt256.ofNat b = (⟨⟨b % evmModulus, hb'⟩⟩ : EvmYul.UInt256)
      from by simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  have hmod_a : (a % evmModulus) % Verity.Core.UINT256_MODULUS = a % evmModulus :=
    Nat.mod_eq_of_lt (by rw [Verity.Core.UINT256_MODULUS]; exact ha)
  have hmod_b : (b % evmModulus) % Verity.Core.UINT256_MODULUS = b % evmModulus :=
    Nat.mod_eq_of_lt (by rw [Verity.Core.UINT256_MODULUS]; exact hb)
  simp only [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, hmod_a, hmod_b]
  exact sdiv_int256_eq_uint256Sdiv (a % evmModulus) (b % evmModulus) ha hb

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_sdiv_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "sdiv" [a, b] =
      evalBuiltinCall storage sender selector calldata "sdiv" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_sdiv_bridge]

/-! ## Smod Bridge Proof

The `smod` bridge connects Verity's `Int256.mod` (sign-magnitude remainder via Int)
with EVMYulLean's `UInt256.smod` (sign/abs decomposition with `sgn`/`toSigned`). -/

private theorem verity_eval_smod_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "smod" [a, b] =
      some (Verity.Core.Int256.mod
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % evmModulus)))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % evmModulus)))).toUint256.val := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

private theorem bridge_eval_smod_normalized (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "smod" [a, b] =
      some (EvmYul.UInt256.toNat
        (EvmYul.UInt256.smod (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b))) := by
  rfl

private theorem int256_ofInt_nat_toUint256_val (r : Nat) (hr : r < evmModulus) :
    (Verity.Core.Int256.ofInt (Int.ofNat r)).toUint256.val = r := by
  simp [Verity.Core.Int256.ofInt, Verity.Core.Int256.toUint256,
    Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
  exact Nat.mod_eq_of_lt (by simpa [evmModulus, Verity.Core.UINT256_MODULUS] using hr)

/-- Negative-wrapper counterpart to `int256_ofInt_nat_toUint256_val` used by
    the NP/NN sign cases of the `smod` core equivalence:
    `(Verity.Core.Int256.ofInt (-Int.ofNat r)).toUint256.val =
       if r = 0 then 0 else evmModulus - r`. -/
private theorem int256_ofInt_neg_nat_toUint256_val (r : Nat) (hr : r < evmModulus) :
    (Verity.Core.Int256.ofInt (-Int.ofNat r)).toUint256.val =
      if r = 0 then 0 else evmModulus - r := by
  by_cases hr0 : r = 0
  · subst hr0
    simp [Verity.Core.Int256.ofInt, Verity.Core.Int256.toUint256,
          Verity.Core.Int256.ofUint256, Verity.Core.Uint256.ofNat]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hneg : (-Int.ofNat r : Int) < 0 := by
      have : (0 : Int) < Int.ofNat r := Int.natCast_pos.mpr hrpos
      omega
    have hnatAbs : Int.natAbs (-Int.ofNat r) = r := by
      simp [Int.natAbs_neg]
    have hmod_eq : Verity.Core.Int256.modulus = evmModulus := by
      simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
            Verity.Core.UINT256_MODULUS, evmModulus]
    have hr_lt_mod : r < Verity.Core.Int256.modulus := by rw [hmod_eq]; exact hr
    have hmod_r : r % Verity.Core.Int256.modulus = r := Nat.mod_eq_of_lt hr_lt_mod
    have hsub_lt : Verity.Core.Int256.modulus - r < Verity.Core.Int256.modulus := by
      have : 0 < Verity.Core.Int256.modulus := by rw [hmod_eq]; unfold evmModulus; omega
      omega
    rw [if_neg hr0]
    simp only [Verity.Core.Int256.ofInt, if_pos hneg,
      Verity.Core.Int256.toUint256, Verity.Core.Int256.ofUint256,
      Verity.Core.Uint256.ofNat, hnatAbs, hmod_r]
    show (Verity.Core.Int256.modulus - r) % Verity.Core.Uint256.modulus = evmModulus - r
    have hmod_eq' : Verity.Core.Int256.modulus = Verity.Core.Uint256.modulus := rfl
    rw [hmod_eq', Nat.mod_eq_of_lt (by rw [← hmod_eq']; exact hsub_lt)]
    show Verity.Core.Uint256.modulus - r = evmModulus - r
    rw [hmod_eq.symm.trans hmod_eq']

/-! ### Verity-side reduction for A2

The next three lemmas reduce Verity's `Int256.signedAbsNat ∘ toInt` on a
word to the Nat-level `SignedArithSpec.specAbs`, and reduce the sign
tests on `(ofUint256 ⟨n, _⟩ : Int)` to comparisons on `n`. They compose
into `int256_mod_toUint256_val_eq_smodSpec`, which is the Verity-side
half of the `smod` core equivalence (A2). -/

private theorem int256_ofUint256_coe_eq (a : Nat) (ha : a < evmModulus) :
    ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) =
      if a < SignedArithSpec.specSignBit then Int.ofNat a
      else Int.ofNat a - Int.ofNat Verity.Core.Int256.modulus := by
  show Verity.Core.Int256.toInt _ = _
  unfold Verity.Core.Int256.toInt
  have hword : (Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256).word.val = a := rfl
  have hSB : SignedArithSpec.specSignBit = Verity.Core.Int256.signBit := rfl
  rw [hword, hSB]

private theorem evmModulus_eq_specModulus : evmModulus = SignedArithSpec.specModulus := rfl

private theorem int256_modulus_eq_specModulus :
    Verity.Core.Int256.modulus = SignedArithSpec.specModulus := by
  simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
        Verity.Core.UINT256_MODULUS, SignedArithSpec.specModulus]

private theorem signedAbsNat_of_ofUint256 (a : Nat) (ha : a < evmModulus) :
    Verity.Core.Int256.signedAbsNat
      ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) =
    SignedArithSpec.specAbs a := by
  unfold Verity.Core.Int256.signedAbsNat SignedArithSpec.specAbs
  rw [int256_ofUint256_coe_eq a ha]
  have hMod : Verity.Core.Int256.modulus = evmModulus := by
    simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
          Verity.Core.UINT256_MODULUS, evmModulus]
  by_cases hS : a < SignedArithSpec.specSignBit
  · rw [if_pos hS, if_pos hS]
    show (Int.ofNat a).natAbs = a
    rfl
  · rw [if_neg hS, if_neg hS]
    have ha' : a < Verity.Core.Int256.modulus := by rw [hMod]; exact ha
    have hle : a ≤ Verity.Core.Int256.modulus := Nat.le_of_lt ha'
    have hcast : (Int.ofNat (Verity.Core.Int256.modulus - a) : Int) =
                 Int.ofNat Verity.Core.Int256.modulus - Int.ofNat a :=
      Int.ofNat_sub hle
    have hsub : Int.ofNat a - Int.ofNat Verity.Core.Int256.modulus =
                -(Int.ofNat (Verity.Core.Int256.modulus - a)) := by
      rw [hcast]; ring
    rw [hsub, Int.natAbs_neg]
    show Verity.Core.Int256.modulus - a = SignedArithSpec.specModulus - a
    rw [int256_modulus_eq_specModulus]

private theorem int256_coe_lt_zero_iff (a : Nat) (ha : a < evmModulus) :
    ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) < 0 ↔
    SignedArithSpec.specSignBit ≤ a := by
  rw [int256_ofUint256_coe_eq a ha]
  have hMod : Verity.Core.Int256.modulus = evmModulus := by
    simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
          Verity.Core.UINT256_MODULUS, evmModulus]
  have ha' : a < Verity.Core.Int256.modulus := by rw [hMod]; exact ha
  by_cases hS : a < SignedArithSpec.specSignBit
  · rw [if_pos hS]
    have hnn : (0 : Int) ≤ Int.ofNat a := Int.natCast_nonneg a
    constructor
    · intro h; omega
    · intro h; exact absurd h (Nat.not_le.mpr hS)
  · rw [if_neg hS]
    have hge : SignedArithSpec.specSignBit ≤ a := Nat.le_of_not_lt hS
    have hlt_int : Int.ofNat a < Int.ofNat Verity.Core.Int256.modulus := Int.ofNat_lt.mpr ha'
    constructor
    · intro _; exact hge
    · intro _; omega

private theorem int256_coe_eq_zero_iff (a : Nat) (ha : a < evmModulus) :
    ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) = 0 ↔
    a = 0 := by
  rw [int256_ofUint256_coe_eq a ha]
  have hMod : Verity.Core.Int256.modulus = evmModulus := by
    simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
          Verity.Core.UINT256_MODULUS, evmModulus]
  have ha' : a < Verity.Core.Int256.modulus := by rw [hMod]; exact ha
  by_cases hS : a < SignedArithSpec.specSignBit
  · rw [if_pos hS]; exact Int.ofNat_eq_zero
  · rw [if_neg hS]
    have hge : SignedArithSpec.specSignBit ≤ a := Nat.le_of_not_lt hS
    have hSBpos : 0 < SignedArithSpec.specSignBit := SignedArithSpec.specSignBit_pos
    constructor
    · intro h
      have : Int.ofNat a < Int.ofNat Verity.Core.Int256.modulus := Int.ofNat_lt.mpr ha'
      omega
    · intro h; subst h; exact absurd hge (Nat.not_le.mpr hSBpos)

/-- Verity-side half of A2: `Int256.mod`'s `.toUint256.val` view
reduces exactly to `smodSpec` at the Nat level. Composes
`int256_ofInt_nat_toUint256_val` / `int256_ofInt_neg_nat_toUint256_val`
for the non-negative/negative `a` sign cases with the sign-case
characterizations `smodSpec_of_nonneg` / `smodSpec_of_neg`. -/
private theorem int256_mod_toUint256_val_eq_smodSpec (a b : Nat)
    (ha : a < evmModulus) (hb : b < evmModulus) :
    (Verity.Core.Int256.mod
      (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
      (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)).toUint256.val =
    SignedArithSpec.smodSpec a b := by
  unfold Verity.Core.Int256.mod
  have habs_a := signedAbsNat_of_ofUint256 a ha
  have habs_b := signedAbsNat_of_ofUint256 b hb
  have hzero_b := int256_coe_eq_zero_iff b hb
  have hneg_a := int256_coe_lt_zero_iff a ha
  by_cases hb0 : b = 0
  · -- b = 0 branch on both sides
    subst hb0
    simp only [hzero_b.mpr rfl, if_true]
    show ((0 : Verity.Core.Int256) : Verity.Core.Uint256).val = _
    rw [SignedArithSpec.smodSpec_b_zero]
    rfl
  · -- b ≠ 0
    have hrhs_ne : ((Verity.Core.Int256.ofUint256 ⟨b, hb⟩ : Verity.Core.Int256) : Int) ≠ 0 := by
      intro h; exact hb0 (hzero_b.mp h)
    simp only [hrhs_ne, if_false]
    have habs_b_pos : 0 < SignedArithSpec.specAbs b := by
      unfold SignedArithSpec.specAbs
      by_cases hbs : b < SignedArithSpec.specSignBit
      · simp [hbs]; exact Nat.pos_of_ne_zero hb0
      · simp [hbs]
        have hb_ge : SignedArithSpec.specSignBit ≤ b := Nat.le_of_not_lt hbs
        have hmod := SignedArithSpec.specModulus_pos
        have hSBlt := SignedArithSpec.specSignBit_lt_specModulus
        have hbmod : b < SignedArithSpec.specModulus := by
          show b < 2^256
          exact hb
        omega
    have hr_lt_specAbsB : SignedArithSpec.specAbs a % SignedArithSpec.specAbs b < SignedArithSpec.specAbs b :=
      Nat.mod_lt _ habs_b_pos
    have habs_b_le : SignedArithSpec.specAbs b ≤ SignedArithSpec.specSignBit :=
      SignedArithSpec.specAbs_le_specSignBit b
    have hSBlt : SignedArithSpec.specSignBit < SignedArithSpec.specModulus :=
      SignedArithSpec.specSignBit_lt_specModulus
    have hr_lt_mod : SignedArithSpec.specAbs a % SignedArithSpec.specAbs b < evmModulus := by
      have : SignedArithSpec.specAbs a % SignedArithSpec.specAbs b < SignedArithSpec.specModulus := by
        omega
      exact this
    rw [habs_a, habs_b]
    by_cases haS : a < SignedArithSpec.specSignBit
    · -- non-negative a
      have hnlt : ¬ ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) < 0 := by
        rw [hneg_a]; exact Nat.not_le.mpr haS
      simp only [hnlt, if_false]
      rw [int256_ofInt_nat_toUint256_val _ hr_lt_mod]
      rw [SignedArithSpec.smodSpec_of_nonneg a b haS hb0]
    · -- negative a
      have hge : SignedArithSpec.specSignBit ≤ a := Nat.le_of_not_lt haS
      have hlt : ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) < 0 := by
        rw [hneg_a]; exact hge
      simp only [hlt, if_true]
      rw [int256_ofInt_neg_nat_toUint256_val _ hr_lt_mod]
      rw [SignedArithSpec.smodSpec_of_neg a b hge hb0]
      rw [evmModulus_eq_specModulus]

/-! ### EVMYulLean-side abs reduction for A2

Mirror of the Verity-side `signedAbsNat_of_ofUint256` helper: reduces
`EvmYul.UInt256.abs` on a raw-Nat word to `SignedArithSpec.specAbs`. The
negative branch applies `fin_val_mul_neg1` to collapse Fin-multiplication
by `-1` into two's-complement subtraction. Future A2b work can compose
this with `smodSpec_of_nonneg`/`_of_neg` + `toSigned` characterizations to
close the EVMYulLean side of the `smod` core equivalence, symmetric to
`int256_mod_toUint256_val_eq_smodSpec` on the Verity side. -/
private theorem uint256_abs_toNat_eq_specAbs (a : Nat) (ha : a < evmModulus) :
    EvmYul.UInt256.toNat
      (EvmYul.UInt256.abs ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩) =
    SignedArithSpec.specAbs a := by
  unfold evmModulus at ha
  unfold EvmYul.UInt256.abs EvmYul.UInt256.toNat SignedArithSpec.specAbs
  by_cases haS : a < SignedArithSpec.specSignBit
  · -- Non-negative branch: abs returns the value unchanged, specAbs returns `a`.
    have hnot : ¬ (2^255 ≤ a) := by
      have : a < 2^255 := haS
      omega
    show (if 2^255 ≤ a then _ else (⟨⟨a, _⟩⟩ : EvmYul.UInt256)).val.val =
         if a < SignedArithSpec.specSignBit then a else SignedArithSpec.specModulus - a
    rw [if_neg hnot, if_pos haS]
  · -- Negative branch: abs returns `⟨a.val * (-1)⟩`; specAbs returns `specModulus - a`.
    have hge : 2^255 ≤ a := by
      have hnot : ¬ a < SignedArithSpec.specSignBit := haS
      have : SignedArithSpec.specSignBit = 2^255 := rfl
      omega
    have hpos : 0 < a := by
      have h255 : 0 < (2 : Nat)^255 := by positivity
      omega
    show (if 2^255 ≤ a then (⟨⟨a, _⟩ * (-1 : Fin EvmYul.UInt256.size)⟩ : EvmYul.UInt256)
          else _).val.val =
         if a < SignedArithSpec.specSignBit then a else SignedArithSpec.specModulus - a
    rw [if_pos hge, if_neg haS]
    show ((⟨a, _⟩ : Fin EvmYul.UInt256.size) * (-1 : Fin EvmYul.UInt256.size)).val =
         SignedArithSpec.specModulus - a
    simp only [EvmYul.UInt256.size]
    norm_num
    simp only [Fin.val_neg]
    norm_num
    -- After simp + norm_num, the goal reduces to
    -- `(if a = 0 then 0 else 115792... - a) = SignedArithSpec.specModulus - a`.
    -- `hpos : 0 < a` discharges the `a = 0` branch, and the literal is
    -- definitionally `specModulus`.
    have ha0 : a ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    rw [if_neg ha0]
    rfl

/-! ### EVMYulLean-side mod reduction to Nat-level mod (for A2b)

Reduces `(a % b : UInt256).toNat` to `a.toNat % b.toNat` under the nonzero
hypothesis on `b` (the zero branch forces a `0` result on the UInt256 side
but yields `a` on the Nat side, so the conditional is necessary). This is
the straightforward `Fin.mod` unfolding needed to let the A2b composition
push `UInt256.mod` through to `Nat.mod`. -/
private theorem uint256_mod_toNat_of_nonzero
    (a b : EvmYul.UInt256) (hb : EvmYul.UInt256.toNat b ≠ 0) :
    EvmYul.UInt256.toNat (a % b) =
      EvmYul.UInt256.toNat a % EvmYul.UInt256.toNat b := by
  show EvmYul.UInt256.toNat (EvmYul.UInt256.mod a b) = _
  unfold EvmYul.UInt256.mod EvmYul.UInt256.toNat
  split_ifs with h
  · exfalso
    apply hb
    simp only [beq_iff_eq] at h
    show b.val.val = 0
    rw [h]; rfl
  · rfl

/-- Core smod equivalence: Verity's `Int256.mod` agrees with EVMYulLean's `UInt256.smod`.

**Status**: sorry — requires showing Int sign-magnitude remainder matches
UInt256 sgn/abs decomposition. Validated by concrete tests. -/
private theorem smod_int256_eq_uint256Smod (a b : Nat)
    (ha : a < evmModulus) (hb : b < evmModulus) :
    (Verity.Core.Int256.mod
      (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
      (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)).toUint256.val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.smod ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
                                               ⟨⟨b, by rw [EvmYul.UInt256.size]; exact hb⟩⟩) := by
  sorry

/-- Universal bridge theorem for `smod`. -/
@[simp] theorem evalBuiltinCall_smod_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "smod" [a, b] =
      evalPureBuiltinViaEvmYulLean "smod" [a, b] := by
  rw [verity_eval_smod_normalized, bridge_eval_smod_normalized]
  have ha : a % evmModulus < evmModulus := Nat.mod_lt a (by unfold evmModulus; omega)
  have hb : b % evmModulus < evmModulus := Nat.mod_lt b (by unfold evmModulus; omega)
  congr 1
  have ha' : a % evmModulus < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact ha
  have hb' : b % evmModulus < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hb
  rw [show EvmYul.UInt256.ofNat a = (⟨⟨a % evmModulus, ha'⟩⟩ : EvmYul.UInt256)
      from by simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  rw [show EvmYul.UInt256.ofNat b = (⟨⟨b % evmModulus, hb'⟩⟩ : EvmYul.UInt256)
      from by simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  have hmod_a : (a % evmModulus) % Verity.Core.UINT256_MODULUS = a % evmModulus :=
    Nat.mod_eq_of_lt (by rw [Verity.Core.UINT256_MODULUS]; exact ha)
  have hmod_b : (b % evmModulus) % Verity.Core.UINT256_MODULUS = b % evmModulus :=
    Nat.mod_eq_of_lt (by rw [Verity.Core.UINT256_MODULUS]; exact hb)
  simp only [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, hmod_a, hmod_b]
  exact smod_int256_eq_uint256Smod (a % evmModulus) (b % evmModulus) ha hb

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_smod_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "smod" [a, b] =
      evalBuiltinCall storage sender selector calldata "smod" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_smod_bridge]

/-! ## SAR (Signed Arithmetic Right Shift) Bridge Proof

The `sar` bridge connects Verity's `Int256.sar` (floor division by 2^shift via Int)
with EVMYulLean's `UInt256.sar` (complement-shift-complement for negatives). -/

private theorem verity_eval_sar_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCall storage sender selector calldata "sar" [shift, value] =
      some (Verity.Core.Int256.sar
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (shift % evmModulus)))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (value % evmModulus)))).toUint256.val := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

private theorem bridge_eval_sar_normalized (shift value : Nat) :
    evalPureBuiltinViaEvmYulLean "sar" [shift, value] =
      some (EvmYul.UInt256.toNat
        (EvmYul.UInt256.sar (EvmYul.UInt256.ofNat shift) (EvmYul.UInt256.ofNat value))) := by
  rfl

/-- Core sar equivalence: Verity's `Int256.sar` agrees with EVMYulLean's `UInt256.sar`.

**Status**: sorry — requires showing Int.fdiv-based shift matches complement-shift-
complement. Validated by concrete tests. -/
private theorem sar_int256_eq_uint256Sar (shift value : Nat)
    (hs : shift < evmModulus) (hv : value < evmModulus) :
    (Verity.Core.Int256.sar
      (Verity.Core.Int256.ofUint256 ⟨shift, hs⟩)
      (Verity.Core.Int256.ofUint256 ⟨value, hv⟩)).toUint256.val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.sar ⟨⟨shift, by rw [EvmYul.UInt256.size]; exact hs⟩⟩
                                               ⟨⟨value, by rw [EvmYul.UInt256.size]; exact hv⟩⟩) := by
  sorry

/-- Universal bridge theorem for `sar`. -/
@[simp] theorem evalBuiltinCall_sar_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCall storage sender selector calldata "sar" [shift, value] =
      evalPureBuiltinViaEvmYulLean "sar" [shift, value] := by
  rw [verity_eval_sar_normalized, bridge_eval_sar_normalized]
  have hs : shift % evmModulus < evmModulus := Nat.mod_lt shift (by unfold evmModulus; omega)
  have hv : value % evmModulus < evmModulus := Nat.mod_lt value (by unfold evmModulus; omega)
  congr 1
  have hs' : shift % evmModulus < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hs
  have hv' : value % evmModulus < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hv
  rw [show EvmYul.UInt256.ofNat shift = (⟨⟨shift % evmModulus, hs'⟩⟩ : EvmYul.UInt256)
      from by simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  rw [show EvmYul.UInt256.ofNat value = (⟨⟨value % evmModulus, hv'⟩⟩ : EvmYul.UInt256)
      from by simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  have hmod_s : (shift % evmModulus) % Verity.Core.UINT256_MODULUS = shift % evmModulus :=
    Nat.mod_eq_of_lt (by rw [Verity.Core.UINT256_MODULUS]; exact hs)
  have hmod_v : (value % evmModulus) % Verity.Core.UINT256_MODULUS = value % evmModulus :=
    Nat.mod_eq_of_lt (by rw [Verity.Core.UINT256_MODULUS]; exact hv)
  simp only [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, hmod_s, hmod_v]
  exact sar_int256_eq_uint256Sar (shift % evmModulus) (value % evmModulus) hs hv

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_sar_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "sar" [shift, value] =
      evalBuiltinCall storage sender selector calldata "sar" [shift, value] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_sar_bridge]

/-! ## Signextend Bridge Proof

The `signextend` bridge connects Verity's `Uint256.signextend` (bitwise mask with
Nat arithmetic) with EVMYulLean's `UInt256.signextend` (shift-based bit test).
Both implement EVM SIGNEXTEND: extending the sign bit at byte position `b`. -/

private theorem verity_eval_signextend_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (byteIdx value : Nat) :
    evalBuiltinCall storage sender selector calldata "signextend" [byteIdx, value] =
      some (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat (byteIdx % evmModulus))
        (Verity.Core.Uint256.ofNat (value % evmModulus))).val := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

private theorem bridge_eval_signextend_normalized (byteIdx value : Nat) :
    evalPureBuiltinViaEvmYulLean "signextend" [byteIdx, value] =
      some (EvmYul.UInt256.toNat
        (EvmYul.UInt256.signextend (EvmYul.UInt256.ofNat byteIdx) (EvmYul.UInt256.ofNat value))) := by
  rfl

-- Signextend helper lemmas

private theorem se_uint256_eq_of_val (a b : EvmYul.UInt256) (h : a.val.val = b.val.val) :
    a = b := by cases a; cases b; congr 1; ext; exact h

private theorem se_lor_val (a b : EvmYul.UInt256) :
    (EvmYul.UInt256.lor a b).val.val = (a.val.val ||| b.val.val) % EvmYul.UInt256.size := by
  unfold EvmYul.UInt256.lor; simp only [Fin.lor]; rfl

private theorem se_land_val (a b : EvmYul.UInt256) :
    (EvmYul.UInt256.land a b).val.val = (a.val.val &&& b.val.val) % EvmYul.UInt256.size := by
  unfold EvmYul.UInt256.land; simp only [Fin.land]; rfl

private theorem se_sub_val (a b : EvmYul.UInt256) :
    (EvmYul.UInt256.sub a b).val.val =
      (EvmYul.UInt256.size - b.val.val + a.val.val) % EvmYul.UInt256.size := by
  unfold EvmYul.UInt256.sub; simp only [Fin.sub_def]

private theorem se_tb_pow_sub_pow {n k : Nat} (hkn : k ≤ n) (i : Nat) :
    (2^n - 2^k).testBit i = (decide (k ≤ i) && decide (i < n)) := by
  have := Nat.one_le_pow k 2 (by omega)
  have := Nat.pow_le_pow_right (show 0 < 2 from by omega) hkn
  rw [show 2^k = (2^k - 1) + 1 from by omega,
      Nat.testBit_two_pow_sub_succ (by omega),
      Nat.testBit_two_pow_sub_one]
  by_cases h1 : i < k <;> by_cases h2 : i < n <;> simp_all

private theorem se_tb_ne_zero {v k : Nat} (h : v &&& 2^k ≠ 0) : v.testBit k = true := by
  by_contra hf; simp only [Bool.not_eq_true] at hf
  apply h; apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hik : k = i
  · subst hik; simp [hf]
  · simp [hik]

private theorem se_tb_eq_zero {v k : Nat} (h : v &&& 2^k = 0) : v.testBit k = false := by
  by_contra hf; simp only [Bool.not_eq_false] at hf
  have : (v &&& 2^k).testBit k = true := by simp [Nat.testBit_and, hf]
  rw [h] at this; simp at this

private theorem se_set_eq {v n k : Nat} (hk1n : k + 1 ≤ n) (hsign : v &&& 2^k ≠ 0) :
    v ||| (2^n - 2^(k+1)) = v ||| (2^n - 2^k) := by
  have hbit := se_tb_ne_zero hsign
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, se_tb_pow_sub_pow (by omega : k + 1 ≤ n),
             se_tb_pow_sub_pow (by omega : k ≤ n)]
  by_cases hik : i = k
  · subst hik; simp [hbit]
  · congr 1
    by_cases hi : i < k
    · simp [show ¬(k ≤ i) from by omega, show ¬(k+1 ≤ i) from by omega]
    · simp [show k ≤ i from by omega, show k+1 ≤ i from by omega]

private theorem se_clear_eq {v k : Nat} (hsign : v &&& 2^k = 0) :
    v &&& (2^(k+1) - 1) = v &&& (2^k - 1) := by
  have hbit := se_tb_eq_zero hsign
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hik : i = k
  · subst hik; simp [hbit, show i < i + 1 from by omega]
  · congr 1; congr 1
    by_cases hi : i < k
    · simp [hi, show i < k + 1 from by omega]
    · simp [show ¬(i < k) from hi, show ¬(i < k + 1) from by omega]

set_option maxHeartbeats 4000000 in
private theorem se_tb_val (byteIdx : Nat) (hb : byteIdx < EvmYul.UInt256.size)
    (hle : byteIdx ≤ 31) :
    (({ val := ⟨byteIdx, hb⟩ } : EvmYul.UInt256) * { val := 8 } + { val := 7 }).val.val =
    byteIdx * 8 + 7 := by
  show ((EvmYul.UInt256.add (EvmYul.UInt256.mul ⟨⟨byteIdx, hb⟩⟩ ⟨8⟩) ⟨7⟩)).val.val = _
  unfold EvmYul.UInt256.add EvmYul.UInt256.mul
  simp only [Fin.mul_def, Fin.add_def]
  have h8 : (8 : Fin EvmYul.UInt256.size).val = 8 := by simp [EvmYul.UInt256.size]
  have h7 : (7 : Fin EvmYul.UInt256.size).val = 7 := by simp [EvmYul.UInt256.size]
  rw [h8, h7, Nat.mod_eq_of_lt (by rw [EvmYul.UInt256.size]; omega),
      Nat.mod_eq_of_lt (by rw [EvmYul.UInt256.size]; omega)]

private theorem se_shiftLeft_one_val (bitPos : Nat) (hbp : bitPos ≤ 255) :
    (EvmYul.UInt256.shiftLeft ⟨⟨1, by rw [EvmYul.UInt256.size]; omega⟩⟩
      ⟨⟨bitPos, by rw [EvmYul.UInt256.size]; omega⟩⟩).val.val = 2^bitPos := by
  unfold EvmYul.UInt256.shiftLeft; split
  · rename_i h; exact absurd (show bitPos ≥ 256 from h) (by omega)
  · change (1 <<< bitPos) % EvmYul.UInt256.size = 2^bitPos
    simp only [Nat.shiftLeft_eq, Nat.one_mul]
    have : 2^bitPos < 2^256 := Nat.pow_lt_pow_right (by omega) (by omega)
    rw [EvmYul.UInt256.size]; exact Nat.mod_eq_of_lt this

private theorem se_val_val_of_eq (a b : EvmYul.UInt256) (h : a = b) :
    a.val.val = b.val.val := by subst h; rfl

private theorem se_sign_set (value : Nat) (hvS : value < EvmYul.UInt256.size)
    (sb : EvmYul.UInt256) (bp : Nat) (hsb : sb.val.val = 2^bp)
    (h : EvmYul.UInt256.land ⟨⟨value, hvS⟩⟩ sb ≠
      ⟨⟨0, by rw [EvmYul.UInt256.size]; omega⟩⟩) :
    value &&& 2^bp ≠ 0 := by
  intro heq; apply h; apply se_uint256_eq_of_val
  rw [se_land_val, hsb, heq]; simp [EvmYul.UInt256.size]

private theorem se_sign_clear (value : Nat) (hvS : value < EvmYul.UInt256.size)
    (sb : EvmYul.UInt256) (bp : Nat) (hsb : sb.val.val = 2^bp)
    (h : ¬(EvmYul.UInt256.land ⟨⟨value, hvS⟩⟩ sb ≠
      ⟨⟨0, by rw [EvmYul.UInt256.size]; omega⟩⟩)) :
    value &&& 2^bp = 0 := by
  push_neg at h
  have h1 := se_val_val_of_eq _ _ h
  rw [se_land_val, hsb] at h1
  rwa [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hvS)] at h1

private theorem se_nat_to_sign (value : Nat) (hvS : value < EvmYul.UInt256.size)
    (sb : EvmYul.UInt256) (bp : Nat) (hsb : sb.val.val = 2^bp)
    (h : value &&& 2^bp ≠ 0) :
    EvmYul.UInt256.land ⟨⟨value, hvS⟩⟩ sb ≠
      ⟨⟨0, by rw [EvmYul.UInt256.size]; omega⟩⟩ := by
  intro heq; apply h
  have h1 := se_val_val_of_eq _ _ heq
  rw [se_land_val, hsb] at h1
  rwa [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hvS)] at h1

private theorem se_verity_ofNat (n : Nat) :
    (Verity.Core.Uint256.ofNat n).val = n % evmModulus := by
  unfold Verity.Core.Uint256.ofNat Verity.Core.Uint256.modulus
    Verity.Core.UINT256_MODULUS evmModulus
  simp

private theorem se_size_to_uint256_val :
    (EvmYul.UInt256.size.toUInt256 : EvmYul.UInt256).val.val = 0 := by
  simp [Nat.toUInt256, EvmYul.UInt256.ofNat, Id.run, EvmYul.UInt256.size]

set_option maxHeartbeats 16000000 in
/-- Core signextend equivalence: Verity's `Uint256.signextend` agrees with
EVMYulLean's `UInt256.signextend`.

Both implement EVM SIGNEXTEND using the same bit-level algorithm:
1. Compute sign bit position = byteIdx * 8 + 7
2. Test the sign bit
3. If set: fill high bits (OR with complement mask)
4. If clear: clear high bits (AND with mask)
5. If byteIdx ≥ 31: return value unchanged -/
private theorem signextend_uint256_eq (byteIdx value : Nat)
    (hb : byteIdx < evmModulus) (hv : value < evmModulus) :
    (Verity.Core.Uint256.signextend ⟨byteIdx, hb⟩ ⟨value, hv⟩).val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.signextend
      ⟨⟨byteIdx, by rw [EvmYul.UInt256.size]; exact hb⟩⟩
      ⟨⟨value, by rw [EvmYul.UInt256.size]; exact hv⟩⟩) := by
  have hvS : value < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hv
  have hbS : byteIdx < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hb
  have hv256 : value < 2^256 := by rw [show (2:Nat)^256 = evmModulus from rfl]; exact hv
  unfold Verity.Core.Uint256.signextend EvmYul.UInt256.signextend
  simp only [EvmYul.UInt256.toNat]
  by_cases hle31 : byteIdx ≤ 31
  · -- byteIdx ≤ 31: EVMYulLean does signextend
    simp only [hle31, ite_true]
    set bitPos := byteIdx * 8 + 7
    have hbp : bitPos ≤ 255 := by omega
    have hbpS : bitPos < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; omega
    have hpow_pos := Nat.one_le_pow bitPos 2 (by omega)
    have hpow_lt := Nat.pow_lt_pow_right (show 1 < 2 from by omega)
      (show bitPos < 256 from by omega)
    have htb_val := se_tb_val byteIdx hbS hle31
    set tb := ({ val := ⟨byteIdx, hbS⟩ } : EvmYul.UInt256) * { val := 8 } + { val := 7 }
    have htbvv : tb.val.val = bitPos := htb_val
    have htb_eq : tb = ⟨⟨bitPos, hbpS⟩⟩ := se_uint256_eq_of_val _ _ htbvv
    set sb := EvmYul.UInt256.shiftLeft ⟨⟨1, by rw [EvmYul.UInt256.size]; omega⟩⟩ tb
    have hsb_val : sb.val.val = 2^bitPos := by
      show (EvmYul.UInt256.shiftLeft ⟨⟨1, _⟩⟩ tb).val.val = 2^bitPos
      rw [htb_eq]; exact se_shiftLeft_one_val bitPos hbp
    have hmod_sub : (2^256 - 2^bitPos) % 2^256 = 2^256 - 2^bitPos :=
      Nat.mod_eq_of_lt (by omega)
    have hmod_mask : (2^bitPos - 1) % 2^256 = 2^bitPos - 1 :=
      Nat.mod_eq_of_lt (by omega)
    by_cases hge31 : byteIdx ≥ 31
    · -- byteIdx = 31: Verity identity, EVMYulLean signextend at bitPos=255
      have hb31 : byteIdx = 31 := by omega
      simp only [hb31, show (31 : Nat) ≥ 31 from le_refl _, ite_true]
      have hbp255 : bitPos = 255 := by omega
      split
      · -- sign set
        rename_i hsign
        change value = (EvmYul.UInt256.lor ⟨⟨value, hvS⟩⟩
          (EvmYul.UInt256.sub EvmYul.UInt256.size.toUInt256 sb)).val.val
        rw [se_lor_val, se_sub_val, se_size_to_uint256_val, hsb_val]
        simp only [show EvmYul.UInt256.size = 2^256 from rfl]
        simp only [Nat.add_zero, hmod_sub]
        have hsign_nat := se_sign_set value hvS sb bitPos hsb_val hsign
        rw [hbp255] at hsign_nat ⊢
        rw [show (2:Nat)^256 - 2^255 = 2^255 from by omega]
        have hbit := se_tb_ne_zero hsign_nat
        have hor : value ||| 2^255 = value := by
          apply Nat.eq_of_testBit_eq; intro i
          simp only [Nat.testBit_or, Nat.testBit_two_pow]
          by_cases hik : 255 = i
          · subst hik; simp [hbit]
          · simp [hik]
        rw [hor, Nat.mod_eq_of_lt hv256]
      · -- sign clear
        rename_i hsign
        change value = (EvmYul.UInt256.land ⟨⟨value, hvS⟩⟩
          (EvmYul.UInt256.sub sb ⟨⟨1, by rw [EvmYul.UInt256.size]; omega⟩⟩)).val.val
        rw [se_land_val, se_sub_val, hsb_val]
        simp only [show EvmYul.UInt256.size = 2^256 from rfl]
        rw [show (2:Nat)^256 - 1 + 2^bitPos = (2^bitPos - 1) + 1 * 2^256 from by omega,
            Nat.add_mul_mod_self_right, hmod_mask]
        have hsign_nat := se_sign_clear value hvS sb bitPos hsb_val hsign
        rw [hbp255] at hsign_nat ⊢
        have htb_false := se_tb_eq_zero hsign_nat
        have hv255 : value < 2^255 := by
          apply Nat.lt_of_testBit 255 htb_false
          · rw [Nat.testBit_two_pow]; simp
          · intro j hj
            have hj256 : 256 ≤ j := by omega
            have hvj : value < 2^j :=
              lt_of_lt_of_le hv256 (Nat.pow_le_pow_right (by omega) hj256)
            rw [Nat.testBit_lt_two_pow hvj, Nat.testBit_two_pow_of_ne (by omega)]
        have hmask : value &&& (2^255 - 1) = value := by
          apply Nat.eq_of_testBit_eq; intro i
          simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
          by_cases hi : i < 255
          · simp [hi]
          · have hi255 : 255 ≤ i := by omega
            have hvi : value < 2^i :=
              lt_of_lt_of_le hv255 (Nat.pow_le_pow_right (by omega) hi255)
            simp [show ¬(i < 255) from hi, Nat.testBit_lt_two_pow hvi]
        rw [hmask, Nat.mod_eq_of_lt hv256]
    · -- byteIdx ≤ 30: both do signextend
      simp only [show ¬(byteIdx ≥ 31) from hge31, ite_false]
      have hle30 : byteIdx ≤ 30 := by omega
      have hbp254 : bitPos ≤ 254 := by omega
      split
      · -- Verity set
        rename_i hsign_nat
        rw [se_verity_ofNat]
        unfold Verity.Core.Uint256.modulus Verity.Core.UINT256_MODULUS
        rw [show 2^256 - 1 - (2 ^ (bitPos + 1) - 1) = 2^256 - 2^(bitPos+1) from by
          have := Nat.one_le_pow (bitPos + 1) 2 (by omega)
          have := Nat.pow_lt_pow_right (show 1 < 2 from by omega)
            (show bitPos + 1 < 256 from by omega)
          omega]
        split
        · -- EVMYulLean set → prove equality
          rename_i hsign_evm
          change _ = (EvmYul.UInt256.lor ⟨⟨value, hvS⟩⟩
            (EvmYul.UInt256.sub EvmYul.UInt256.size.toUInt256 sb)).val.val
          rw [se_lor_val, se_sub_val, se_size_to_uint256_val, hsb_val]
          simp only [show EvmYul.UInt256.size = 2^256 from rfl]
          simp only [Nat.add_zero, hmod_sub]
          unfold evmModulus
          rw [se_set_eq (by omega) hsign_nat]
        · -- EVMYulLean clear → contradiction
          rename_i hsign_evm
          exfalso; exact hsign_evm (se_nat_to_sign value hvS sb bitPos hsb_val hsign_nat)
      · -- Verity clear
        rename_i hsign
        have hsign_nat : value &&& 2^bitPos = 0 := not_not.mp hsign
        rw [se_verity_ofNat]
        split
        · -- EVMYulLean set → contradiction
          rename_i hsign_evm
          exfalso
          have := se_sign_set value hvS sb bitPos hsb_val hsign_evm
          exact hsign this
        · -- EVMYulLean clear → prove equality
          rename_i hsign_evm
          change _ = (EvmYul.UInt256.land ⟨⟨value, hvS⟩⟩
            (EvmYul.UInt256.sub sb ⟨⟨1, by rw [EvmYul.UInt256.size]; omega⟩⟩)).val.val
          rw [se_land_val, se_sub_val, hsb_val]
          simp only [show EvmYul.UInt256.size = 2^256 from rfl]
          rw [show (2:Nat)^256 - 1 + 2^bitPos = (2^bitPos - 1) + 1 * 2^256 from by omega,
              Nat.add_mul_mod_self_right, hmod_mask]
          unfold evmModulus
          rw [se_clear_eq hsign_nat]
  · -- byteIdx > 31: identity for both
    simp only [show ¬(byteIdx ≤ 31) from hle31, ite_false]
    simp only [show byteIdx ≥ 31 from by omega, ite_true]

/-- Universal bridge theorem for `signextend`. -/
@[simp] theorem evalBuiltinCall_signextend_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (byteIdx value : Nat) :
    evalBuiltinCall storage sender selector calldata "signextend" [byteIdx, value] =
      evalPureBuiltinViaEvmYulLean "signextend" [byteIdx, value] := by
  rw [verity_eval_signextend_normalized, bridge_eval_signextend_normalized]
  have hb : byteIdx % evmModulus < evmModulus := Nat.mod_lt byteIdx (by unfold evmModulus; omega)
  have hv : value % evmModulus < evmModulus := Nat.mod_lt value (by unfold evmModulus; omega)
  congr 1
  have hb' : byteIdx % evmModulus < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hb
  have hv' : value % evmModulus < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hv
  rw [show EvmYul.UInt256.ofNat byteIdx = (⟨⟨byteIdx % evmModulus, hb'⟩⟩ : EvmYul.UInt256)
      from by simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  rw [show EvmYul.UInt256.ofNat value = (⟨⟨value % evmModulus, hv'⟩⟩ : EvmYul.UInt256)
      from by simp only [EvmYul.UInt256.ofNat, Id.run]; congr 1]
  have hmod_b : (byteIdx % evmModulus) % Verity.Core.UINT256_MODULUS = byteIdx % evmModulus :=
    Nat.mod_eq_of_lt (by rw [Verity.Core.UINT256_MODULUS]; exact hb)
  have hmod_v : (value % evmModulus) % Verity.Core.UINT256_MODULUS = value % evmModulus :=
    Nat.mod_eq_of_lt (by rw [Verity.Core.UINT256_MODULUS]; exact hv)
  simp only [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, hmod_b, hmod_v]
  exact signextend_uint256_eq (byteIdx % evmModulus) (value % evmModulus) hb hv

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_signextend_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (byteIdx value : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "signextend" [byteIdx, value] =
      evalBuiltinCall storage sender selector calldata "signextend" [byteIdx, value] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean,
    evalBuiltinCall_signextend_bridge]

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

/-- `calldataload` is bridged at the full adapter boundary because it depends
    on the selector/calldata context rather than only on argument words. -/
@[simp] theorem evalBuiltinCall_calldataload_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (offset : Nat) :
    evalBuiltinCall storage sender selector calldata "calldataload" [offset] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "calldataload" [offset] := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext, evalBuiltinCallViaEvmYulLean]

/-- `sload` is bridged at the full adapter boundary: the `.evmYulLean` path
    routes through `abstractLoadStorageOrMapping`, the same helper Verity's
    `evalBuiltinCallWithContext` uses. The EVMYulLean-state correspondence of
    that helper is witnessed by `storageLookup_projectStorage` in
    `EvmYulLeanStateBridge.lean`. -/
@[simp] theorem evalBuiltinCall_sload_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (slot : Nat) :
    evalBuiltinCall storage sender selector calldata "sload" [slot] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "sload" [slot] := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext, evalBuiltinCallViaEvmYulLean]

/-- `mappingSlot` is bridged at the full adapter boundary: the `.evmYulLean`
    path routes through `abstractMappingSlot`, the same keccak-faithful
    Solidity mapping-slot derivation (`keccak256(abi.encode(key, baseSlot))`)
    that Verity's `evalBuiltinCallWithContext` uses. Because both backends
    ultimately invoke the same kernel-computable `KeccakEngine.keccak256`,
    the two sides are definitionally equal. -/
@[simp] theorem evalBuiltinCall_mappingSlot_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (base key : Nat) :
    evalBuiltinCall storage sender selector calldata "mappingSlot" [base, key] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "mappingSlot" [base, key] := by
  simp [evalBuiltinCall, evalBuiltinCallWithContext, evalBuiltinCallViaEvmYulLean]

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

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_exp_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "exp" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "exp" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_exp_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_sdiv_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "sdiv" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "sdiv" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_sdiv_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_smod_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "smod" [a, b] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "smod" [a, b] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_smod_bridge storage sender selector calldata a b]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_sar_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "sar" [shift, value] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "sar" [shift, value] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_sar_bridge storage sender selector calldata shift value]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_signextend_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (byteIdx value : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "signextend" [byteIdx, value] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "signextend" [byteIdx, value] := by
  simp only [evalBuiltinCallWithBackendContext, evalBuiltinCallViaEvmYulLean]
  rw [← evalBuiltinCall_signextend_bridge storage sender selector calldata byteIdx value]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

/-! ## Context-Aware Backend Routing Surface

For `.evmYulLean`, `evalBuiltinCallWithBackendContext` now has two behaviors:

1. It directly bridges the environment-only builtins whose results are just
   context views at this boundary (`caller`, `address`, `callvalue`,
   `timestamp`, `number`, `chainid`, `blobbasefee`).
2. It also bridges selector/calldata-only builtins whose full semantics are
   already available at this boundary (`calldatasize`, `calldataload`).
3. It bridges the state-dependent storage-read builtin (`sload`) via the
   shared `abstractLoadStorageOrMapping` helper.
4. It bridges the Verity-specific mapping-slot helper (`mappingSlot`) via
   the shared keccak-faithful `abstractMappingSlot` derivation.

These lemmas define the exact Phase-3 boundary that later retargeting proofs
can rewrite against. -/

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_sload_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (slot : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "sload" [slot] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "sload" [slot] := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallWithContext, evalBuiltinCallViaEvmYulLean]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_caller_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "caller" [] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "caller" [] := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_address_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "address" [] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "address" [] := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_callvalue_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "callvalue" [] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "callvalue" [] := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_timestamp_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "timestamp" [] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "timestamp" [] := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_number_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "number" [] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "number" [] := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_blobbasefee_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "blobbasefee" [] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "blobbasefee" [] := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_chainid_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "chainid" [] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "chainid" [] := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_calldataload_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (offset : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "calldataload" [offset] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "calldataload" [offset] := by
  simp only [evalBuiltinCallWithBackendContext]
  rw [← evalBuiltinCall_calldataload_bridge storage sender selector calldata offset]
  simp [evalBuiltinCall, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_calldatasize_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "calldatasize" [] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "calldatasize" [] := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallWithContext]

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_mappingSlot_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (base key : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "mappingSlot" [base, key] =
    evalBuiltinCallWithContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "mappingSlot" [base, key] := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallWithContext, evalBuiltinCallViaEvmYulLean]

/-! ## Composite Backend Equivalence Theorem

This is the key Phase 4 composition lemma. For any pure builtin `func` in the
set of 25 universally-bridged builtins (23 fully proven, 2 with sorry-dependent
core equivalences), all with context-lifted bridge theorems, the EVMYulLean
backend agrees with the Verity backend
(represented by `evalBuiltinCallWithContext`).

The theorem is structured as a disjunction: either `func` matches one of the
25 bridged pure builtins (and the backends agree), or `func` is a state-dependent
builtin (and `.evmYulLean` returns `none`), or `func` is unknown.

We provide `evalBuiltinCallWithBackendContext_evmYulLean_pure_bridge` as the
backend-routing simplification theorem for the non-environment fragment: when
`func` is not one of the directly bridged context/env builtins (`caller`,
`address`, `callvalue`, `timestamp`, `number`, `chainid`, `blobbasefee`) and not
`calldatasize`, the `.evmYulLean` backend reduces to `evalBuiltinCallViaEvmYulLean`
with arbitrary context. Callers can then apply the per-builtin bridge lemmas
separately when the builtin is known to be in the bridged pure fragment. -/

/-- Simplify the `.evmYulLean` backend branch of
    `evalBuiltinCallWithBackendContext` to `evalBuiltinCallViaEvmYulLean`.
    This theorem applies away from the directly handled context/env builtins;
    per-builtin bridge lemmas are applied after this routing rewrite when the
    builtin is known to lie in the bridged pure fragment. -/
theorem evalBuiltinCallWithBackendContext_evmYulLean_pure_bridge
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (func : String) (argVals : List Nat)
    (hCaller : func ≠ "caller")
    (hAddress : func ≠ "address")
    (hCallvalue : func ≠ "callvalue")
    (hTimestamp : func ≠ "timestamp")
    (hNumber : func ≠ "number")
    (hChainid : func ≠ "chainid")
    (hBlobbasefee : func ≠ "blobbasefee")
    (hCalldatasize : func ≠ "calldatasize") :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata func argVals =
    evalBuiltinCallViaEvmYulLean storage sender selector calldata func argVals := by
  simp [evalBuiltinCallWithBackendContext, hCaller, hAddress, hCallvalue, hTimestamp, hNumber,
    hChainid, hBlobbasefee, hCalldatasize]

/-! ## Phase 4 Backend Equivalence Surface

The following definitions and theorems establish the Phase 4 retargeting surface.
They define which builtins are fully bridged between backends and provide
the master equivalence theorem that Phase 4's `Preservation.lean` retargeting
will invoke.

### Bridged builtin inventory

| Category | Count | Status |
|---|---|---|
| Pure arithmetic (add, sub, mul, div, mod) | 5 | Fully proven |
| Pure comparison (lt, gt, eq, iszero) | 4 | Fully proven |
| Pure bitwise (and, or, xor, not, shl, shr) | 6 | Fully proven |
| Pure extended (addmod, mulmod, byte) | 3 | Fully proven |
| Pure signed (slt, sgt) | 2 | Fully proven |
| Pure signed arith (exp, sdiv) | 2 | Fully proven |
| Pure signed arith (smod, sar) | 2 | Sorry-dependent core equivalences |
| Pure signed arith (signextend) | 1 | Fully proven |
| Context/env (caller, address, callvalue, timestamp, number, chainid, blobbasefee) | 7 | Fully proven |
| Calldata (calldataload, calldatasize) | 2 | Fully proven |
| State (sload, mappingSlot) | 2 | Fully proven (Phase 3 keccak-semantic bridge) |
| **Total bridged** | **36** | **34 proven, 2 sorry** |
-/

/-- The set of builtins for which the `.evmYulLean` and `.verity` backends
    produce identical results. This now covers all 36 builtins handled by
    `evalBuiltinCallWithContext`, including `mappingSlot` which is bridged
    via the shared keccak-faithful `abstractMappingSlot` derivation.

    Phase 4's `Preservation.lean` retargeting uses this set to determine
    which builtin invocations can be transparently switched from `.verity`
    to `.evmYulLean` backend without affecting the proof. -/
def bridgedBuiltins : List String :=
  ["add", "sub", "mul", "div", "mod",
   "lt", "gt", "eq", "iszero",
   "and", "or", "xor", "not", "shl", "shr",
   "addmod", "mulmod", "byte",
   "slt", "sgt",
   "exp", "sdiv", "smod", "sar", "signextend",
   "caller", "address", "callvalue", "timestamp",
   "number", "chainid", "blobbasefee",
   "calldataload", "calldatasize",
   "sload", "mappingSlot"]

/-- The set of builtins that the `.evmYulLean` backend cannot handle is
    now empty: every builtin in `evalBuiltinCallWithContext` has a bridge
    lemma and appears in `bridgedBuiltins`. -/
def unbridgedBuiltins : List String := []

/-! ## Remaining Core Equivalence Proofs — Status

All 25 pure builtins now have universal bridge theorems
(`evalBuiltinCall_*_bridge`). Two core equivalence lemmas still use
`sorry` pending fundamentally different proof strategies:

- `smod_int256_eq_uint256Smod` — Int sign-magnitude remainder ↔ UInt256 sgn/abs
- `sar_int256_eq_uint256Sar` — Int.fdiv ↔ complement-shift-complement

The `exp` bridge was fully proved by strong induction on the exponent after
making `powAux` public in the EVMYulLean fork (commit `ed9215e9`).
The `sdiv` bridge was proved by 5-way case analysis (b=0, PP, PN, NP, NN)
with `fin_val_mul_neg1` handling EVMYulLean's negation-via-Fin-multiplication.
The `signextend` bridge was proved by 4-case byte-index analysis.

These are validated by concrete `native_decide` bridge tests in
`EvmYulLeanBridgeTest.lean` covering critical boundary values.

**State-dependent builtin notes**:
- `chainid`: the context-aware backend boundary now bridges the Verity
  `chainId` context parameter directly. Full interpreter-level execution
  still depends on EVMYulLean exposing chain id through its execution
  environment rather than a fixed wheel constant. -/

end Compiler.Proofs.YulGeneration.Backends
