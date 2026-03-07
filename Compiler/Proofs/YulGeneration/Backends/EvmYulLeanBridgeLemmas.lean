import Compiler.Proofs.YulGeneration.Builtins
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter
import Mathlib.Data.Nat.Bitwise

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Proofs.YulGeneration

private theorem word_lt_uint256_size (x : Nat) :
    x % EvmYul.UInt256.size < 2 ^ 256 := by
  simpa [EvmYul.UInt256.size] using Nat.mod_lt x (by decide : 0 < EvmYul.UInt256.size)

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

private theorem verity_eval_mod_normalized
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "mod" [a, b] =
      (if b % evmModulus = 0 then some 0 else some ((a % evmModulus) % (b % evmModulus))) := by
  simp [evalBuiltinCall]

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
      some (a % evmModulus &&& b % evmModulus) by simp [evalBuiltinCall]]
  rw [bridge_eval_and_normalized]
  simp [EvmYul.UInt256.size, evmModulus]

/-- Universal bridge theorem for `or`: Verity builtin semantics agree with
EVMYulLean UInt256 semantics on all inputs. -/
@[simp] theorem evalBuiltinCall_or_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "or" [a, b] =
      evalPureBuiltinViaEvmYulLean "or" [a, b] := by
  rw [show evalBuiltinCall storage sender selector calldata "or" [a, b] =
      some (a % evmModulus ||| b % evmModulus) by simp [evalBuiltinCall]]
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
        some 0) by simp [evalBuiltinCall]]
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
        some 0) by simp [evalBuiltinCall]]
  rw [bridge_eval_shr_normalized]
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

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_mod_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "mod" [a, b] =
      evalBuiltinCall storage sender selector calldata "mod" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallViaEvmYulLean, evalBuiltinCall_mod_bridge]

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

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_and_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "and" [a, b] =
      evalBuiltinCall storage sender selector calldata "and" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallViaEvmYulLean, evalBuiltinCall_and_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_or_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "or" [a, b] =
      evalBuiltinCall storage sender selector calldata "or" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallViaEvmYulLean, evalBuiltinCall_or_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_xor_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "xor" [a, b] =
      evalBuiltinCall storage sender selector calldata "xor" [a, b] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallViaEvmYulLean, evalBuiltinCall_xor_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_not_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "not" [a] =
      evalBuiltinCall storage sender selector calldata "not" [a] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallViaEvmYulLean, evalBuiltinCall_not_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_shl_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "shl" [shift, value] =
      evalBuiltinCall storage sender selector calldata "shl" [shift, value] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallViaEvmYulLean, evalBuiltinCall_shl_bridge]

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_shr_bridge
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "shr" [shift, value] =
      evalBuiltinCall storage sender selector calldata "shr" [shift, value] := by
  simp [evalBuiltinCallWithBackend, evalBuiltinCallViaEvmYulLean, evalBuiltinCall_shr_bridge]

end Compiler.Proofs.YulGeneration.Backends
