import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter
import Mathlib.Data.Nat.Bitwise

namespace Compiler.Proofs.YulGeneration.Backends

private theorem uint256_size_eq_evmModulus :
    EvmYul.UInt256.size = Compiler.Constants.evmModulus := by
  decide

private theorem word_lt_uint256_size (x : Nat) :
    x % EvmYul.UInt256.size < 2 ^ 256 := by
  simpa [EvmYul.UInt256.size] using Nat.mod_lt x (by decide : 0 < EvmYul.UInt256.size)

@[simp] theorem evalPureBuiltinViaEvmYulLean_add_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "add" [a, b] =
      some ((a + b) % Compiler.Constants.evmModulus) := by
  rw [← uint256_size_eq_evmModulus]
  change some ((Fin.ofNat EvmYul.UInt256.size a + Fin.ofNat EvmYul.UInt256.size b).val) =
      some ((a + b) % EvmYul.UInt256.size)
  simp [Fin.val_add, Nat.add_mod]

@[simp] theorem evalPureBuiltinViaEvmYulLean_sub_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "sub" [a, b] =
      some ((Compiler.Constants.evmModulus + (a % Compiler.Constants.evmModulus) -
        (b % Compiler.Constants.evmModulus)) % Compiler.Constants.evmModulus) := by
  rw [← uint256_size_eq_evmModulus]
  change some ((Fin.ofNat EvmYul.UInt256.size a - Fin.ofNat EvmYul.UInt256.size b).val) =
      some ((EvmYul.UInt256.size + a % EvmYul.UInt256.size - b % EvmYul.UInt256.size) %
        EvmYul.UInt256.size)
  have hsub :
      EvmYul.UInt256.size + a % EvmYul.UInt256.size - b % EvmYul.UInt256.size =
        EvmYul.UInt256.size - b % EvmYul.UInt256.size + a % EvmYul.UInt256.size := by
    have hb : b % EvmYul.UInt256.size ≤ EvmYul.UInt256.size := by
      exact Nat.le_of_lt (Nat.mod_lt _ (by simp [EvmYul.UInt256.size]))
    omega
  simp [Fin.sub_def, Nat.add_mod, hsub]

@[simp] theorem evalPureBuiltinViaEvmYulLean_mul_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "mul" [a, b] =
      some ((a * b) % Compiler.Constants.evmModulus) := by
  rw [← uint256_size_eq_evmModulus]
  change some ((Fin.ofNat EvmYul.UInt256.size a * Fin.ofNat EvmYul.UInt256.size b).val) =
      some ((a * b) % EvmYul.UInt256.size)
  simp [Fin.mul_def, Nat.mul_mod]

@[simp] theorem evalPureBuiltinViaEvmYulLean_div_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "div" [a, b] =
      some (if b % Compiler.Constants.evmModulus = 0 then 0 else
        (a % Compiler.Constants.evmModulus) / (b % Compiler.Constants.evmModulus)) := by
  rw [← uint256_size_eq_evmModulus]
  change some ((Fin.ofNat EvmYul.UInt256.size a / Fin.ofNat EvmYul.UInt256.size b).val) =
      some (if b % EvmYul.UInt256.size = 0 then 0 else
        (a % EvmYul.UInt256.size) / (b % EvmYul.UInt256.size))
  by_cases hb : b % EvmYul.UInt256.size = 0 <;> simp [hb]

@[simp] theorem evalPureBuiltinViaEvmYulLean_mod_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "mod" [a, b] =
      some (if b % Compiler.Constants.evmModulus = 0 then 0 else
        (a % Compiler.Constants.evmModulus) % (b % Compiler.Constants.evmModulus)) := by
  rw [← uint256_size_eq_evmModulus]
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.mod (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b))) =
    some (if b % EvmYul.UInt256.size = 0 then 0 else
      (a % EvmYul.UInt256.size) % (b % EvmYul.UInt256.size))
  by_cases hb : b % EvmYul.UInt256.size = 0
  · have hb0val : ((EvmYul.UInt256.ofNat b).val).val = 0 := by
      change b % EvmYul.UInt256.size = 0
      exact hb
    have hb0 : (EvmYul.UInt256.ofNat b).val = 0 := Fin.ext hb0val
    simp [EvmYul.UInt256.mod, EvmYul.UInt256.toNat, hb, hb0]
  · have hb0 : ¬ (EvmYul.UInt256.ofNat b).val = 0 := by
      intro h
      exact hb (congrArg Fin.val h)
    rw [show EvmYul.UInt256.mod (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b) =
          ⟨(EvmYul.UInt256.ofNat a).val % (EvmYul.UInt256.ofNat b).val⟩ by
            simp [EvmYul.UInt256.mod, hb0]]
    simp [hb, EvmYul.UInt256.toNat]
    rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_eq_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "eq" [a, b] =
      some (if a % Compiler.Constants.evmModulus = b % Compiler.Constants.evmModulus then 1 else 0) := by
  rw [← uint256_size_eq_evmModulus]
  rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_iszero_native (a : Nat) :
    evalPureBuiltinViaEvmYulLean "iszero" [a] =
      some (if a % Compiler.Constants.evmModulus = 0 then 1 else 0) := by
  rw [← uint256_size_eq_evmModulus]
  rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_lt_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "lt" [a, b] =
      some (if a % Compiler.Constants.evmModulus < b % Compiler.Constants.evmModulus then 1 else 0) := by
  rw [← uint256_size_eq_evmModulus]
  rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_gt_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "gt" [a, b] =
      some (if b % Compiler.Constants.evmModulus < a % Compiler.Constants.evmModulus then 1 else 0) := by
  rw [← uint256_size_eq_evmModulus]
  rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_and_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "and" [a, b] =
      some ((a % Compiler.Constants.evmModulus) &&& (b % Compiler.Constants.evmModulus)) := by
  rw [← uint256_size_eq_evmModulus]
  change some (((Nat.bitwise Bool.and (a % EvmYul.UInt256.size) (b % EvmYul.UInt256.size)) %
      EvmYul.UInt256.size)) =
    some (Nat.bitwise Bool.and (a % EvmYul.UInt256.size) (b % EvmYul.UInt256.size))
  congr 1
  rw [Nat.mod_eq_of_lt]
  exact Nat.bitwise_lt_two_pow (f := Bool.and) (n := 256)
    (by simpa [EvmYul.UInt256.size] using Nat.mod_lt a (by decide : 0 < EvmYul.UInt256.size))
    (by simpa [EvmYul.UInt256.size] using Nat.mod_lt b (by decide : 0 < EvmYul.UInt256.size))

@[simp] theorem evalPureBuiltinViaEvmYulLean_or_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "or" [a, b] =
      some ((a % Compiler.Constants.evmModulus) ||| (b % Compiler.Constants.evmModulus)) := by
  rw [← uint256_size_eq_evmModulus]
  change some (((Nat.bitwise Bool.or (a % EvmYul.UInt256.size) (b % EvmYul.UInt256.size)) %
      EvmYul.UInt256.size)) =
    some (Nat.bitwise Bool.or (a % EvmYul.UInt256.size) (b % EvmYul.UInt256.size))
  congr 1
  rw [Nat.mod_eq_of_lt]
  exact Nat.bitwise_lt_two_pow (f := Bool.or) (n := 256)
    (word_lt_uint256_size a) (word_lt_uint256_size b)

@[simp] theorem evalPureBuiltinViaEvmYulLean_xor_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "xor" [a, b] =
      some (Nat.xor (a % Compiler.Constants.evmModulus) (b % Compiler.Constants.evmModulus)) := by
  rw [← uint256_size_eq_evmModulus]
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

@[simp] theorem evalPureBuiltinViaEvmYulLean_not_native (a : Nat) :
    evalPureBuiltinViaEvmYulLean "not" [a] =
      some (Nat.xor (a % Compiler.Constants.evmModulus)
        (Compiler.Constants.evmModulus - 1)) := by
  rw [← uint256_size_eq_evmModulus]
  change evalPureBuiltinViaEvmYulLean "not" [a] =
    some ((a % EvmYul.UInt256.size) ^^^ (EvmYul.UInt256.size - 1))
  have hsub : evalPureBuiltinViaEvmYulLean "not" [a] =
      some (EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size)) := by
    change evalPureBuiltinViaEvmYulLean "sub" [EvmYul.UInt256.size - 1, a] =
      some (EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size))
    rw [evalPureBuiltinViaEvmYulLean_sub_native]
    rw [← uint256_size_eq_evmModulus]
    have hs : 0 < EvmYul.UInt256.size := by simp [EvmYul.UInt256.size]
    have ha : a % EvmYul.UInt256.size < EvmYul.UInt256.size := Nat.mod_lt _ hs
    have hlt : EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size) < EvmYul.UInt256.size := by
      omega
    have hmod :
        ((EvmYul.UInt256.size + (EvmYul.UInt256.size - 1) % EvmYul.UInt256.size -
            a % EvmYul.UInt256.size) % EvmYul.UInt256.size) =
          EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size) := by
      have hsizeMinusOneMod :
          (EvmYul.UInt256.size - 1) % EvmYul.UInt256.size = EvmYul.UInt256.size - 1 := by
        exact Nat.mod_eq_of_lt (by omega)
      rw [hsizeMinusOneMod]
      have harr :
          EvmYul.UInt256.size + (EvmYul.UInt256.size - 1) - a % EvmYul.UInt256.size =
            EvmYul.UInt256.size +
              (EvmYul.UInt256.size - 1 - (a % EvmYul.UInt256.size)) := by
        omega
      rw [harr, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]
    exact congrArg some hmod
  rw [hsub]
  simp [xor_all_ones_uint256_word]

@[simp] theorem evalPureBuiltinViaEvmYulLean_shl_native (shift value : Nat) :
    evalPureBuiltinViaEvmYulLean "shl" [shift, value] =
      some (if shift % Compiler.Constants.evmModulus < 256 then
        ((value % Compiler.Constants.evmModulus) *
          2 ^ (shift % Compiler.Constants.evmModulus)) % Compiler.Constants.evmModulus
      else
        0) := by
  rw [← uint256_size_eq_evmModulus]
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftLeft (EvmYul.UInt256.ofNat value) (EvmYul.UInt256.ofNat shift))) =
    some (if shift % EvmYul.UInt256.size < 256 then
      ((value % EvmYul.UInt256.size) * 2 ^ (shift % EvmYul.UInt256.size)) %
        EvmYul.UInt256.size
    else
      0)
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

@[simp] theorem evalPureBuiltinViaEvmYulLean_shr_native (shift value : Nat) :
    evalPureBuiltinViaEvmYulLean "shr" [shift, value] =
      some (if shift % Compiler.Constants.evmModulus < 256 then
        (value % Compiler.Constants.evmModulus) /
          2 ^ (shift % Compiler.Constants.evmModulus)
      else
        0) := by
  rw [← uint256_size_eq_evmModulus]
  change some (EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftRight (EvmYul.UInt256.ofNat value) (EvmYul.UInt256.ofNat shift))) =
    some (if shift % EvmYul.UInt256.size < 256 then
      (value % EvmYul.UInt256.size) / 2 ^ (shift % EvmYul.UInt256.size)
    else
      0)
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

end Compiler.Proofs.YulGeneration.Backends
