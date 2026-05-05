import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter
import Verity.Core.Int256
import Verity.Core.Uint256

namespace Compiler.Proofs.YulGeneration.Backends

private theorem fin_val_mul_neg1 (n x : Nat) (hn : 0 < n) (hx : x < n) (hxpos : 0 < x) :
    (x * (n - 1)) % n = n - x := by
  have h1le : 1 ≤ n := hn
  have hadd : x * (n - 1) + x = x * n := by
    have : x * (n - 1) + x * 1 = x * n := by
      rw [← Nat.left_distrib, Nat.sub_add_cancel h1le]
    rwa [Nat.mul_one] at this
  have h1lex : 1 ≤ x := hxpos
  have hadd2 : (x - 1) * n + n = x * n := by
    have : (x - 1) * n + 1 * n = x * n := by
      rw [← Nat.right_distrib, Nat.sub_add_cancel h1lex]
    rwa [Nat.one_mul] at this
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
theorem int256_div_toUint256_val_eq_uint256_sdiv (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus) (hb : b < Compiler.Constants.evmModulus) :
    (Verity.Core.Int256.div
      (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
      (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)).toUint256.val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.sdiv ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
                                               ⟨⟨b, by rw [EvmYul.UInt256.size]; exact hb⟩⟩) := by
  unfold Compiler.Constants.evmModulus at ha hb
  by_cases hb0 : b = 0
  · subst hb0
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
  · by_cases haS : a < 2 ^ 255 <;> by_cases hbS : b < 2 ^ 255
    · simp only [Verity.Core.Int256.div, Verity.Core.Int256.toInt, Verity.Core.Int256.ofUint256,
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
    · have hb' : (Int.ofNat b : Int) < Int.ofNat (2^256) := Int.ofNat_lt.mpr hb
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
    · have ha' : (Int.ofNat a : Int) < Int.ofNat (2^256) := Int.ofNat_lt.mpr ha
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
    · have ha' : (Int.ofNat a : Int) < Int.ofNat (2^256) := Int.ofNat_lt.mpr ha
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

end Compiler.Proofs.YulGeneration.Backends
