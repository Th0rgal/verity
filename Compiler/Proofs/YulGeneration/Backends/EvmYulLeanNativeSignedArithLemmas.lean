import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanSignedArithSpec
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

private theorem eq0_true_of_val_eq_zero (x : EvmYul.UInt256) (h : x.val = 0) :
    EvmYul.UInt256.eq0 x = true := by
  have hx : x = ⟨0⟩ := by cases x; exact congrArg EvmYul.UInt256.mk h
  subst hx; decide

private theorem eq0_false_of_val_ne_zero (x : EvmYul.UInt256) (h : x.val ≠ 0) :
    EvmYul.UInt256.eq0 x = false := by
  cases hb : EvmYul.UInt256.eq0 x with
  | false => rfl
  | true =>
    exfalso; apply h
    cases x with | mk v =>
    simp only [EvmYul.UInt256.eq0] at hb
    change (v == (0 : Fin EvmYul.UInt256.size)) = true at hb
    have hv : v = (0 : Fin EvmYul.UInt256.size) := of_decide_eq_true hb
    simp [hv]

private theorem int256_ofInt_nat_toUint256_val (r : Nat) (hr : r < Compiler.Constants.evmModulus) :
    (Verity.Core.Int256.ofInt (Int.ofNat r)).toUint256.val = r := by
  simp [Verity.Core.Int256.ofInt, Verity.Core.Int256.toUint256,
    Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
  exact Nat.mod_eq_of_lt (by simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using hr)

/-- Negative-wrapper counterpart to `int256_ofInt_nat_toUint256_val` used by
    the NP/NN sign cases of the `smod` core equivalence:
    `(Verity.Core.Int256.ofInt (-Int.ofNat r)).toUint256.val =
       if r = 0 then 0 else Compiler.Constants.evmModulus - r`. -/
private theorem int256_ofInt_neg_nat_toUint256_val (r : Nat) (hr : r < Compiler.Constants.evmModulus) :
    (Verity.Core.Int256.ofInt (-Int.ofNat r)).toUint256.val =
      if r = 0 then 0 else Compiler.Constants.evmModulus - r := by
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
    have hmod_eq : Verity.Core.Int256.modulus = Compiler.Constants.evmModulus := by
      simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
            Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus]
    have hr_lt_mod : r < Verity.Core.Int256.modulus := by rw [hmod_eq]; exact hr
    have hmod_r : r % Verity.Core.Int256.modulus = r := Nat.mod_eq_of_lt hr_lt_mod
    have hsub_lt : Verity.Core.Int256.modulus - r < Verity.Core.Int256.modulus := by
      have : 0 < Verity.Core.Int256.modulus := by rw [hmod_eq]; unfold Compiler.Constants.evmModulus; omega
      omega
    rw [if_neg hr0]
    simp only [Verity.Core.Int256.ofInt, if_pos hneg,
      Verity.Core.Int256.toUint256, Verity.Core.Int256.ofUint256,
      Verity.Core.Uint256.ofNat, hnatAbs, hmod_r]
    show (Verity.Core.Int256.modulus - r) % Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus - r
    have hmod_eq' : Verity.Core.Int256.modulus = Verity.Core.Uint256.modulus := rfl
    rw [hmod_eq', Nat.mod_eq_of_lt (by rw [← hmod_eq']; exact hsub_lt)]
    show Verity.Core.Uint256.modulus - r = Compiler.Constants.evmModulus - r
    rw [hmod_eq.symm.trans hmod_eq']

/-! ### Verity-side reduction for A2

The next three lemmas reduce Verity's `Int256.signedAbsNat ∘ toInt` on a
word to the Nat-level `SignedArithSpec.specAbs`, and reduce the sign
tests on `(ofUint256 ⟨n, _⟩ : Int)` to comparisons on `n`. They compose
into `int256_mod_toUint256_val_eq_smodSpec`, which is the Verity-side
half of the `smod` core equivalence (A2). -/

private theorem int256_ofUint256_coe_eq (a : Nat) (ha : a < Compiler.Constants.evmModulus) :
    ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) =
      if a < SignedArithSpec.specSignBit then Int.ofNat a
      else Int.ofNat a - Int.ofNat Verity.Core.Int256.modulus := by
  show Verity.Core.Int256.toInt _ = _
  unfold Verity.Core.Int256.toInt
  have hword : (Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256).word.val = a := rfl
  have hSB : SignedArithSpec.specSignBit = Verity.Core.Int256.signBit := rfl
  rw [hword, hSB]

private theorem evmModulus_eq_specModulus : Compiler.Constants.evmModulus = SignedArithSpec.specModulus := rfl

private theorem int256_modulus_eq_specModulus :
    Verity.Core.Int256.modulus = SignedArithSpec.specModulus := by
  simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
        Verity.Core.UINT256_MODULUS, SignedArithSpec.specModulus]

private theorem signedAbsNat_of_ofUint256 (a : Nat) (ha : a < Compiler.Constants.evmModulus) :
    Verity.Core.Int256.signedAbsNat
      ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) =
    SignedArithSpec.specAbs a := by
  unfold Verity.Core.Int256.signedAbsNat SignedArithSpec.specAbs
  rw [int256_ofUint256_coe_eq a ha]
  have hMod : Verity.Core.Int256.modulus = Compiler.Constants.evmModulus := by
    simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
          Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus]
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

private theorem int256_coe_lt_zero_iff (a : Nat) (ha : a < Compiler.Constants.evmModulus) :
    ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) < 0 ↔
    SignedArithSpec.specSignBit ≤ a := by
  rw [int256_ofUint256_coe_eq a ha]
  have hMod : Verity.Core.Int256.modulus = Compiler.Constants.evmModulus := by
    simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
          Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus]
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

private theorem int256_coe_eq_zero_iff (a : Nat) (ha : a < Compiler.Constants.evmModulus) :
    ((Verity.Core.Int256.ofUint256 ⟨a, ha⟩ : Verity.Core.Int256) : Int) = 0 ↔
    a = 0 := by
  rw [int256_ofUint256_coe_eq a ha]
  have hMod : Verity.Core.Int256.modulus = Compiler.Constants.evmModulus := by
    simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
          Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus]
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
    (ha : a < Compiler.Constants.evmModulus) (hb : b < Compiler.Constants.evmModulus) :
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
    have hr_lt_mod : SignedArithSpec.specAbs a % SignedArithSpec.specAbs b < Compiler.Constants.evmModulus := by
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
private theorem uint256_abs_toNat_eq_specAbs (a : Nat) (ha : a < Compiler.Constants.evmModulus) :
    EvmYul.UInt256.toNat
      (EvmYul.UInt256.abs ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩) =
    SignedArithSpec.specAbs a := by
  unfold Compiler.Constants.evmModulus at ha
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

/-! ### EVMYulLean toSigned characterizations (A2b scaffolds)

Splits `toNat ∘ toSigned` by the `Int` constructor. `toSigned` is defined on
the Verity side as
```
match i with
  | .ofNat n     => ofNat n
  | .negSucc n   => ofNat (UInt256.size - 1 - n)
```
so `toNat` reduces to `n % size` and `(size - 1 - n) % size` respectively.
Bounded inputs remove the modulus, which is what A2b's case split needs. -/
private theorem uint256_toSigned_ofNat_toNat_of_lt
    (n : Nat) (hn : n < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat (EvmYul.UInt256.toSigned (Int.ofNat n)) = n := by
  show EvmYul.UInt256.toNat (EvmYul.UInt256.ofNat n) = n
  unfold EvmYul.UInt256.ofNat EvmYul.UInt256.toNat
  simp only [Id.run]
  show (Fin.ofNat EvmYul.UInt256.size n).val = n
  unfold Fin.ofNat
  exact Nat.mod_eq_of_lt hn

private theorem uint256_toSigned_negSucc_toNat_of_lt
    (n : Nat) (hn : n + 1 < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat (EvmYul.UInt256.toSigned (Int.negSucc n)) =
      EvmYul.UInt256.size - 1 - n := by
  show EvmYul.UInt256.toNat (EvmYul.UInt256.ofNat (EvmYul.UInt256.size - 1 - n)) = _
  unfold EvmYul.UInt256.ofNat EvmYul.UInt256.toNat
  simp only [Id.run]
  show (Fin.ofNat EvmYul.UInt256.size (EvmYul.UInt256.size - 1 - n)).val =
       EvmYul.UInt256.size - 1 - n
  unfold Fin.ofNat
  have h : EvmYul.UInt256.size - 1 - n < EvmYul.UInt256.size := by
    have hpos : 0 < EvmYul.UInt256.size := by
      unfold EvmYul.UInt256.size; decide
    omega
  exact Nat.mod_eq_of_lt h

/-! ### EVMYulLean-side smod reduction to smodSpec (A2c)

Symmetric to `int256_mod_toUint256_val_eq_smodSpec`: reduces
`toNat (UInt256.smod a b)` to `SignedArithSpec.smodSpec a.toNat b.toNat`.

The EVMYulLean definition is
```
smod a b = if b.toNat == 0 then ⟨0⟩
           else toSigned (sgn a * (abs a % abs b).toNat)
```
Each branch is discharged by composing the previously-landed scaffolds:

* Zero-divisor: direct from `smodSpec_b_zero`.
* Non-negative `a` (`a < specSignBit`), `a = 0`: `sgn = 0`, product `= 0 = Int.ofNat 0`, `toSigned` gives `0`; `smodSpec_a_zero` gives `0`.
* Non-negative `a`, `a ≠ 0`: `sgn = 1`, product `= Int.ofNat r` with `r < specSignBit < size`; `toSigned` collapses via `uint256_toSigned_ofNat_toNat_of_lt`; RHS matches `smodSpec_of_nonneg`.
* Negative `a` (`specSignBit ≤ a`), `r = 0`: `sgn * 0 = 0`; `toSigned 0 = 0`; RHS matches `smodSpec_of_neg` at its `r = 0` branch.
* Negative `a`, `r > 0`: `sgn * r = -r = Int.negSucc (r-1)`; `toSigned` collapses via `uint256_toSigned_negSucc_toNat_of_lt` to `size - r = specModulus - r`; RHS matches `smodSpec_of_neg`.
-/
private theorem uint256_smod_toNat_eq_smodSpec (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus) (hb : b < Compiler.Constants.evmModulus) :
    EvmYul.UInt256.toNat
      (EvmYul.UInt256.smod ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
                           ⟨⟨b, by rw [EvmYul.UInt256.size]; exact hb⟩⟩) =
    SignedArithSpec.smodSpec a b := by
  -- Size bounds
  have hsize_a : a < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact ha
  have hsize_b : b < EvmYul.UInt256.size := by rw [EvmYul.UInt256.size]; exact hb
  -- Working abbreviations
  let ua : EvmYul.UInt256 := ⟨⟨a, hsize_a⟩⟩
  let ub : EvmYul.UInt256 := ⟨⟨b, hsize_b⟩⟩
  have hua_toNat : EvmYul.UInt256.toNat ua = a := rfl
  have hub_toNat : EvmYul.UInt256.toNat ub = b := rfl
  -- Zero-divisor split
  by_cases hb0 : b = 0
  · subst hb0
    rw [SignedArithSpec.smodSpec_b_zero]
    show EvmYul.UInt256.toNat (EvmYul.UInt256.smod ua ub) = 0
    unfold EvmYul.UInt256.smod
    have h_beq : (EvmYul.UInt256.toNat ub == 0) = true := by
      rw [hub_toNat]; rfl
    rw [h_beq]
    rfl
  · -- b ≠ 0
    show EvmYul.UInt256.toNat (EvmYul.UInt256.smod ua ub) = SignedArithSpec.smodSpec a b
    unfold EvmYul.UInt256.smod
    have h_beq : (EvmYul.UInt256.toNat ub == 0) = false := by
      rw [hub_toNat]
      simp [hb0]
    rw [h_beq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    -- Goal: toNat (toSigned (sgn ua * ↑(toNat (abs ua % abs ub)))) = smodSpec a b
    -- Reduce abs operations
    have habs_ua_toNat : EvmYul.UInt256.toNat (EvmYul.UInt256.abs ua) = SignedArithSpec.specAbs a :=
      uint256_abs_toNat_eq_specAbs a ha
    have habs_ub_toNat : EvmYul.UInt256.toNat (EvmYul.UInt256.abs ub) = SignedArithSpec.specAbs b :=
      uint256_abs_toNat_eq_specAbs b hb
    -- specAbs b is nonzero
    have habs_b_ne : SignedArithSpec.specAbs b ≠ 0 := by
      unfold SignedArithSpec.specAbs
      by_cases hbs : b < SignedArithSpec.specSignBit
      · simp [hbs]; exact hb0
      · simp [hbs]
        have hbmod : b < SignedArithSpec.specModulus := by
          show b < 2^256
          exact hb
        omega
    have habs_b_pos : 0 < SignedArithSpec.specAbs b := Nat.pos_of_ne_zero habs_b_ne
    have habs_ub_ne : EvmYul.UInt256.toNat (EvmYul.UInt256.abs ub) ≠ 0 := by
      rw [habs_ub_toNat]; exact habs_b_ne
    -- Reduce abs % abs via uint256_mod_toNat_of_nonzero
    have hmod_toNat :
        EvmYul.UInt256.toNat (EvmYul.UInt256.abs ua % EvmYul.UInt256.abs ub) =
        SignedArithSpec.specAbs a % SignedArithSpec.specAbs b := by
      rw [uint256_mod_toNat_of_nonzero _ _ habs_ub_ne, habs_ua_toNat, habs_ub_toNat]
    -- Let r := specAbs a % specAbs b
    set r : Nat := SignedArithSpec.specAbs a % SignedArithSpec.specAbs b with hr_def
    -- r bounds
    have hr_lt_absB : r < SignedArithSpec.specAbs b := Nat.mod_lt _ habs_b_pos
    have habs_b_le : SignedArithSpec.specAbs b ≤ SignedArithSpec.specSignBit :=
      SignedArithSpec.specAbs_le_specSignBit b
    have hSB_lt_size : SignedArithSpec.specSignBit < EvmYul.UInt256.size := by
      show (2:Nat)^255 < 2^256; decide
    have hr_lt_size : r < EvmYul.UInt256.size := by
      have hr_le_SB : r < SignedArithSpec.specSignBit := by omega
      omega
    have hr_lt_SB : r < SignedArithSpec.specSignBit := by omega
    -- Case split on sgn a (non-negative vs negative)
    unfold EvmYul.UInt256.sgn
    by_cases haS : a < SignedArithSpec.specSignBit
    · -- Non-negative a: 2^255 ≤ a is false
      have h_not_neg : ¬ (2:Nat)^255 ≤ EvmYul.UInt256.toNat ua := by
        rw [hua_toNat]
        have : a < (2:Nat)^255 := haS
        omega
      simp only [h_not_neg, ↓reduceIte]
      by_cases ha0 : a = 0
      · -- a = 0: eq0 ua = true, sgn = 0
        have hua_val : ua.val = 0 := by
          show (⟨a, hsize_a⟩ : Fin EvmYul.UInt256.size) = 0
          apply Fin.ext
          show a = 0
          exact ha0
        have h_eq0 : EvmYul.UInt256.eq0 ua = true := eq0_true_of_val_eq_zero ua hua_val
        simp only [h_eq0]
        -- sgn = 0 → 0 * _ = 0 = Int.ofNat 0
        show EvmYul.UInt256.toNat
            (EvmYul.UInt256.toSigned
              ((0 : Int) * ((EvmYul.UInt256.toNat
                  (EvmYul.UInt256.abs ua % EvmYul.UInt256.abs ub)) : Int))) =
            SignedArithSpec.smodSpec a b
        rw [zero_mul]
        rw [show (0 : Int) = Int.ofNat 0 from rfl]
        rw [uint256_toSigned_ofNat_toNat_of_lt 0
              (by unfold EvmYul.UInt256.size; decide)]
        -- RHS: smodSpec 0 b = 0
        subst ha0
        rw [SignedArithSpec.smodSpec_a_zero]
      · -- a ≠ 0: eq0 ua = false, sgn = 1
        have hua_val_ne : ua.val ≠ 0 := by
          intro h
          apply ha0
          show a = 0
          exact congrArg Fin.val h
        have h_eq0 : EvmYul.UInt256.eq0 ua = false := eq0_false_of_val_ne_zero ua hua_val_ne
        simp only [h_eq0]
        -- sgn = 1 → 1 * ↑r = ↑r = Int.ofNat r
        show EvmYul.UInt256.toNat
            (EvmYul.UInt256.toSigned
              ((1 : Int) * ((EvmYul.UInt256.toNat
                  (EvmYul.UInt256.abs ua % EvmYul.UInt256.abs ub)) : Int))) =
            SignedArithSpec.smodSpec a b
        rw [one_mul, hmod_toNat]
        rw [show ((r : Int)) = Int.ofNat r from rfl]
        rw [uint256_toSigned_ofNat_toNat_of_lt r hr_lt_size]
        rw [SignedArithSpec.smodSpec_of_nonneg a b haS hb0]
    · -- Negative a: 2^255 ≤ a
      have hge : SignedArithSpec.specSignBit ≤ a := Nat.le_of_not_lt haS
      have h_is_neg : (2:Nat)^255 ≤ EvmYul.UInt256.toNat ua := by
        rw [hua_toNat]
        exact hge
      simp only [h_is_neg, ↓reduceIte]
      -- sgn = -1 → -1 * ↑r
      show EvmYul.UInt256.toNat
          (EvmYul.UInt256.toSigned
            ((-1 : Int) * ((EvmYul.UInt256.toNat
                (EvmYul.UInt256.abs ua % EvmYul.UInt256.abs ub)) : Int))) =
          SignedArithSpec.smodSpec a b
      rw [hmod_toNat]
      rw [SignedArithSpec.smodSpec_of_neg a b hge hb0]
      by_cases hr0 : r = 0
      · -- r = 0
        rw [hr0]
        simp only [Int.natCast_zero, mul_zero]
        rw [show (0 : Int) = Int.ofNat 0 from rfl]
        rw [uint256_toSigned_ofNat_toNat_of_lt 0 (by unfold EvmYul.UInt256.size; decide)]
        have hr0spec : SignedArithSpec.specAbs a % SignedArithSpec.specAbs b = 0 := by
          rw [← hr_def]
          exact hr0
        rw [if_pos hr0spec]
      · -- r > 0
        have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
        -- -1 * ↑r = Int.negSucc (r - 1)
        have hprod : (-1 : Int) * (r : Int) = Int.negSucc (r - 1) := by
          cases h : r with
          | zero => exact False.elim (hr0 h)
          | succ k =>
            simp [Int.negSucc_eq]
        rw [hprod]
        have hr_bound : (r - 1) + 1 < EvmYul.UInt256.size := by omega
        rw [uint256_toSigned_negSucc_toNat_of_lt (r - 1) hr_bound]
        -- Goal: size - 1 - (r-1) = if r = 0 then 0 else specModulus - r
        rw [if_neg hr0]
        show EvmYul.UInt256.size - 1 - (r - 1) = SignedArithSpec.specModulus - r
        have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
        have h_eq : EvmYul.UInt256.size = SignedArithSpec.specModulus := rfl
        rw [h_eq]
        omega

/-- Core smod equivalence: Verity's `Int256.mod` agrees with EVMYulLean's `UInt256.smod`.

**Closed via A2a + A2c**: Verity-side reduction
`int256_mod_toUint256_val_eq_smodSpec` and EVMYulLean-side reduction
`uint256_smod_toNat_eq_smodSpec` both go through the shared
`SignedArithSpec.smodSpec`, and the composition discharges the wrapper. -/
theorem int256_mod_toUint256_val_eq_uint256_smod (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus) (hb : b < Compiler.Constants.evmModulus) :
    (Verity.Core.Int256.mod
      (Verity.Core.Int256.ofUint256 ⟨a, ha⟩)
      (Verity.Core.Int256.ofUint256 ⟨b, hb⟩)).toUint256.val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.smod ⟨⟨a, by rw [EvmYul.UInt256.size]; exact ha⟩⟩
                                               ⟨⟨b, by rw [EvmYul.UInt256.size]; exact hb⟩⟩) := by
  rw [int256_mod_toUint256_val_eq_smodSpec a b ha hb]
  rw [uint256_smod_toNat_eq_smodSpec a b ha hb]

private theorem uint256_lt_zero_false (value : Nat) (hv : value < EvmYul.UInt256.size) :
    ¬ ((⟨⟨value, hv⟩⟩ : EvmYul.UInt256) < ⟨0⟩) := by
  intro h
  change (⟨value, hv⟩ : Fin EvmYul.UInt256.size) < (0 : Fin EvmYul.UInt256.size) at h
  exact Nat.not_lt_zero _ h

private theorem uint256_complement_val (value : Nat) (hv : value < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat (EvmYul.UInt256.complement ⟨⟨value, hv⟩⟩) =
      EvmYul.UInt256.size - 1 - value := by
  simp [EvmYul.UInt256.complement, EvmYul.UInt256.toNat, Fin.add_def, Fin.neg_def]
  have hle : value + 1 ≤ EvmYul.UInt256.size := by omega
  by_cases hlast : value + 1 = EvmYul.UInt256.size
  · rw [hlast]
    simp
    omega
  · have hlt : value + 1 < EvmYul.UInt256.size := Nat.lt_of_le_of_ne hle hlast
    rw [Nat.mod_eq_of_lt hlt]
    have hsub_lt : EvmYul.UInt256.size - (value + 1) < EvmYul.UInt256.size := by
      unfold EvmYul.UInt256.size
      omega
    rw [Nat.mod_eq_of_lt hsub_lt]
    omega

private theorem uint256_complement_eq (value : Nat) (hv : value < EvmYul.UInt256.size) (hout) :
    EvmYul.UInt256.complement ⟨⟨value, hv⟩⟩ =
      ⟨⟨EvmYul.UInt256.size - 1 - value, hout⟩⟩ := by
  rw [EvmYul.UInt256.mk.injEq]
  apply Fin.ext
  exact uint256_complement_val value hv

private theorem uint256_shiftRight_val (value shift : Nat)
    (hv : value < EvmYul.UInt256.size) (hs : shift < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat (EvmYul.UInt256.shiftRight ⟨⟨value, hv⟩⟩ ⟨⟨shift, hs⟩⟩) =
      if shift < 256 then value / 2 ^ shift else 0 := by
  by_cases hshift : shift < 256
  · have hg : ¬ 256 ≤ (⟨⟨shift, hs⟩⟩ : EvmYul.UInt256).val := by
      change ¬ 256 ≤ shift
      exact Nat.not_le_of_lt hshift
    simp [EvmYul.UInt256.shiftRight, EvmYul.UInt256.toNat, hg, hshift,
      Nat.shiftRight_eq_div_pow]
  · have hg : 256 ≤ (⟨⟨shift, hs⟩⟩ : EvmYul.UInt256).val := by
      change 256 ≤ shift
      exact Nat.not_lt.mp hshift
    simp [EvmYul.UInt256.shiftRight, EvmYul.UInt256.toNat, hg, hshift]

/-- EVMYulLean-side `sar` reduction through the shared Nat-level spec. -/
private theorem uint256_sar_toNat_eq_sarSpec (shift value : Nat)
    (hs : shift < EvmYul.UInt256.size) (hv : value < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat (EvmYul.UInt256.sar ⟨⟨shift, hs⟩⟩ ⟨⟨value, hv⟩⟩) =
      SignedArithSpec.sarSpec shift value := by
  unfold EvmYul.UInt256.sar
  by_cases hvalue : value < SignedArithSpec.specSignBit
  · have hslFalse : EvmYul.UInt256.sltBool
        (⟨⟨value, hv⟩⟩ : EvmYul.UInt256) ⟨0⟩ = false := by
      unfold EvmYul.UInt256.sltBool
      have hnotSign : ¬ 2 ^ 255 ≤ (⟨⟨value, hv⟩⟩ : EvmYul.UInt256).toNat := by
        change ¬ 2 ^ 255 ≤ value
        exact Nat.not_le_of_lt (by simpa [SignedArithSpec.specSignBit] using hvalue)
      rw [if_neg hnotSign]
      have hzeroNotSign : ¬ 2 ^ 255 ≤ (⟨0⟩ : EvmYul.UInt256).toNat := by decide
      rw [if_neg hzeroNotSign]
      simp [uint256_lt_zero_false value hv]
    rw [hslFalse]
    simp
    show EvmYul.UInt256.toNat
        (EvmYul.UInt256.shiftRight ⟨⟨value, hv⟩⟩ ⟨⟨shift, hs⟩⟩) =
      SignedArithSpec.sarSpec shift value
    rw [uint256_shiftRight_val value shift hv hs]
    by_cases hshift : shift < 256
    · rw [SignedArithSpec.sarSpec_of_nonneg shift value hshift hvalue]
      simp [hshift]
    · have hge : 256 ≤ shift := Nat.not_lt.mp hshift
      rw [SignedArithSpec.sarSpec_of_shift_ge_nonneg shift value hge hvalue]
      simp [hshift]
  · have hgeValue : SignedArithSpec.specSignBit ≤ value := Nat.le_of_not_lt hvalue
    have hslTrue : EvmYul.UInt256.sltBool
        (⟨⟨value, hv⟩⟩ : EvmYul.UInt256) ⟨0⟩ = true := by
      unfold EvmYul.UInt256.sltBool
      have hsign : 2 ^ 255 ≤ (⟨⟨value, hv⟩⟩ : EvmYul.UInt256).toNat := by
        change 2 ^ 255 ≤ value
        simpa [SignedArithSpec.specSignBit] using hgeValue
      rw [if_pos hsign]
      have hzeroNotSign : ¬ 2 ^ 255 ≤ (⟨0⟩ : EvmYul.UInt256).toNat := by decide
      rw [if_neg hzeroNotSign]
    rw [hslTrue]
    simp
    have hc_lt : EvmYul.UInt256.size - 1 - value < EvmYul.UInt256.size := by
      unfold EvmYul.UInt256.size
      omega
    rw [uint256_complement_eq value hv hc_lt]
    by_cases hshift : shift < 256
    · rw [SignedArithSpec.sarSpec_of_neg shift value hshift hgeValue]
      have hdiv_lt :
          (EvmYul.UInt256.size - 1 - value) / 2 ^ shift < EvmYul.UInt256.size :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hc_lt
      have hshiftEq :
          EvmYul.UInt256.shiftRight
            ⟨⟨EvmYul.UInt256.size - 1 - value, hc_lt⟩⟩ ⟨⟨shift, hs⟩⟩ =
          ⟨⟨(EvmYul.UInt256.size - 1 - value) / 2 ^ shift, hdiv_lt⟩⟩ := by
        rw [EvmYul.UInt256.mk.injEq]
        apply Fin.ext
        change EvmYul.UInt256.toNat
            (EvmYul.UInt256.shiftRight
              ⟨⟨EvmYul.UInt256.size - 1 - value, hc_lt⟩⟩ ⟨⟨shift, hs⟩⟩) =
          (EvmYul.UInt256.size - 1 - value) / 2 ^ shift
        rw [uint256_shiftRight_val (EvmYul.UInt256.size - 1 - value) shift hc_lt hs]
        simp [hshift]
      show EvmYul.UInt256.toNat
          (EvmYul.UInt256.complement
            (EvmYul.UInt256.shiftRight
              ⟨⟨EvmYul.UInt256.size - 1 - value, hc_lt⟩⟩ ⟨⟨shift, hs⟩⟩)) =
        SignedArithSpec.specModulus - 1 -
          (SignedArithSpec.specModulus - 1 - value) / 2 ^ shift
      rw [hshiftEq]
      rw [uint256_complement_val ((EvmYul.UInt256.size - 1 - value) / 2 ^ shift) hdiv_lt]
      simp [EvmYul.UInt256.size, SignedArithSpec.specModulus]
    · have hge : 256 ≤ shift := Nat.not_lt.mp hshift
      rw [SignedArithSpec.sarSpec_of_shift_ge_neg shift value hge hgeValue]
      have hzeroLt : 0 < EvmYul.UInt256.size := by
        unfold EvmYul.UInt256.size
        omega
      have hshiftEq :
          EvmYul.UInt256.shiftRight
            ⟨⟨EvmYul.UInt256.size - 1 - value, hc_lt⟩⟩ ⟨⟨shift, hs⟩⟩ =
          ⟨⟨0, hzeroLt⟩⟩ := by
        rw [EvmYul.UInt256.mk.injEq]
        apply Fin.ext
        change EvmYul.UInt256.toNat
            (EvmYul.UInt256.shiftRight
              ⟨⟨EvmYul.UInt256.size - 1 - value, hc_lt⟩⟩ ⟨⟨shift, hs⟩⟩) = 0
        rw [uint256_shiftRight_val (EvmYul.UInt256.size - 1 - value) shift hc_lt hs]
        simp [hshift]
      show EvmYul.UInt256.toNat
          (EvmYul.UInt256.complement
            (EvmYul.UInt256.shiftRight
              ⟨⟨EvmYul.UInt256.size - 1 - value, hc_lt⟩⟩ ⟨⟨shift, hs⟩⟩)) =
        SignedArithSpec.specModulus - 1
      rw [hshiftEq]
      rw [uint256_complement_val 0 hzeroLt]
      simp [EvmYul.UInt256.size, SignedArithSpec.specModulus]

private theorem int_two_pow_eq_nat (shift : Nat) :
    ((2 : Int) ^ shift) = Int.ofNat (2 ^ shift) := by
  induction shift with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, ih]
      norm_num

private theorem int_fdiv_ofNat_two_pow (value shift : Nat) :
    (Int.ofNat value).fdiv ((2 : Int) ^ shift) =
      Int.ofNat (value / 2 ^ shift) := by
  rw [int_two_pow_eq_nat]
  have hpos : 0 < 2 ^ shift := Nat.pow_pos (by decide : 0 < 2)
  cases hp : 2 ^ shift with
  | zero => omega
  | succ n =>
      cases value with
      | zero => simp [Int.fdiv]
      | succ m => simp [Int.fdiv]

private theorem int_sub_modulus_eq_negSucc (value : Nat)
    (_hge : SignedArithSpec.specSignBit ≤ value) (hv : value < Compiler.Constants.evmModulus) :
    Int.ofNat value - Int.ofNat Compiler.Constants.evmModulus =
      Int.negSucc (Compiler.Constants.evmModulus - 1 - value) := by
  unfold Compiler.Constants.evmModulus at hv ⊢
  rw [Int.negSucc_eq]
  have hdiff : 2 ^ 256 - 1 - value + 1 = 2 ^ 256 - value := by omega
  change Int.ofNat value - Int.ofNat (2 ^ 256) =
    -Int.ofNat ((2 ^ 256 - 1 - value) + 1)
  rw [hdiff]
  have hcast : Int.ofNat (2 ^ 256 - value) =
      Int.ofNat (2 ^ 256) - Int.ofNat value := by
    exact Int.ofNat_sub (Nat.le_of_lt hv)
  rw [hcast]
  omega

private theorem int_fdiv_neg_raw_two_pow (shift value : Nat)
    (hge : SignedArithSpec.specSignBit ≤ value) (hv : value < Compiler.Constants.evmModulus) :
    (Int.ofNat value - Int.ofNat Compiler.Constants.evmModulus).fdiv ((2 : Int) ^ shift) =
      Int.negSucc ((Compiler.Constants.evmModulus - 1 - value) / 2 ^ shift) := by
  rw [int_sub_modulus_eq_negSucc value hge hv]
  rw [int_two_pow_eq_nat]
  have hpos : 0 < 2 ^ shift := Nat.pow_pos (by decide : 0 < 2)
  cases hp : 2 ^ shift with
  | zero => omega
  | succ n =>
      simp [Int.fdiv]

private theorem int256_ofInt_negSucc_toUint256_val (n : Nat)
    (hn : n + 1 < Compiler.Constants.evmModulus) :
    (Verity.Core.Int256.ofInt (Int.negSucc n)).toUint256.val =
      Compiler.Constants.evmModulus - (n + 1) := by
  have hneg : (Int.negSucc n) < 0 := by simp
  have hnatAbs : (Int.negSucc n).natAbs = n + 1 := by
    have hnegSucc : Int.negSucc n = -Int.ofNat (n + 1) := by
      rw [Int.negSucc_eq]
      simp
    rw [hnegSucc, Int.natAbs_neg]
    exact Int.natAbs_natCast (n + 1)
  have hmod_eq : Verity.Core.Int256.modulus = Compiler.Constants.evmModulus := by
    simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
          Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus]
  have hn_lt_mod : n + 1 < Verity.Core.Int256.modulus := by
    rw [hmod_eq]
    exact hn
  have hmod_n : (n + 1) % Verity.Core.Int256.modulus = n + 1 :=
    Nat.mod_eq_of_lt hn_lt_mod
  have hsub_lt : Verity.Core.Int256.modulus - (n + 1) <
      Verity.Core.Int256.modulus := by
    have hpos_mod : 0 < Verity.Core.Int256.modulus := by
      rw [hmod_eq]
      unfold Compiler.Constants.evmModulus
      omega
    omega
  simp only [Verity.Core.Int256.ofInt, if_pos hneg,
    Verity.Core.Int256.toUint256, Verity.Core.Int256.ofUint256,
    Verity.Core.Uint256.ofNat, hnatAbs, hmod_n]
  show (Verity.Core.Int256.modulus - (n + 1)) %
      Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus - (n + 1)
  have hmod_eq' : Verity.Core.Int256.modulus = Verity.Core.Uint256.modulus := rfl
  rw [hmod_eq', Nat.mod_eq_of_lt (by rw [← hmod_eq']; exact hsub_lt)]
  show Verity.Core.Uint256.modulus - (n + 1) = Compiler.Constants.evmModulus - (n + 1)
  rw [← hmod_eq', hmod_eq]

private theorem int256_sar_toUint256_val_eq_sarSpec (shift value : Nat)
    (hs : shift < Compiler.Constants.evmModulus) (hv : value < Compiler.Constants.evmModulus) :
    (Verity.Core.Int256.sar
      (Verity.Core.Int256.ofUint256 ⟨shift, hs⟩)
      (Verity.Core.Int256.ofUint256 ⟨value, hv⟩)).toUint256.val =
      SignedArithSpec.sarSpec shift value := by
  simp [Verity.Core.Int256.sar, Verity.Core.Int256.ofUint256,
    Verity.Core.Int256.toUint256]
  have hsMod : shift % Verity.Core.Int256.modulus = shift := by
    rw [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
      Verity.Core.UINT256_MODULUS]
    exact Nat.mod_eq_of_lt hs
  rw [hsMod]
  by_cases hshift : shift < 256
  · have hnot : ¬ 256 ≤ shift := Nat.not_le_of_lt hshift
    rw [if_neg hnot]
    by_cases hval : value < SignedArithSpec.specSignBit
    · have hto :
          ({ word := { val := value, isLt := hv } } : Verity.Core.Int256).toInt =
            Int.ofNat value := by
        rw [Verity.Core.Int256.toInt_of_lt_signBit]
        simpa [Verity.Core.Int256.signBit, SignedArithSpec.specSignBit] using hval
      rw [hto]
      rw [SignedArithSpec.sarSpec_of_nonneg shift value hshift hval]
      rw [int_fdiv_ofNat_two_pow]
      have hbound : value / 2 ^ shift < Compiler.Constants.evmModulus :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv
      exact int256_ofInt_nat_toUint256_val (value / 2 ^ shift) hbound
    · have hge : SignedArithSpec.specSignBit ≤ value := Nat.le_of_not_lt hval
      have hto :
          ({ word := { val := value, isLt := hv } } : Verity.Core.Int256).toInt =
            Int.ofNat value - Int.ofNat Compiler.Constants.evmModulus := by
        rw [Verity.Core.Int256.toInt_of_ge_signBit]
        · simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
            Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus]
        · simpa [Verity.Core.Int256.signBit, SignedArithSpec.specSignBit] using hge
      rw [hto]
      rw [SignedArithSpec.sarSpec_of_neg shift value hshift hge]
      rw [int_fdiv_neg_raw_two_pow shift value hge hv]
      have hn_bound : (Compiler.Constants.evmModulus - 1 - value) / 2 ^ shift + 1 < Compiler.Constants.evmModulus := by
        unfold Compiler.Constants.evmModulus at hv ⊢
        unfold SignedArithSpec.specSignBit at hge
        have hle : (2 ^ 256 - 1 - value) / 2 ^ shift ≤
            2 ^ 256 - 1 - value := Nat.div_le_self _ _
        omega
      have hwrap :=
        int256_ofInt_negSucc_toUint256_val
          ((Compiler.Constants.evmModulus - 1 - value) / 2 ^ shift) hn_bound
      change
        (Verity.Core.Int256.ofInt
          (Int.negSucc ((Compiler.Constants.evmModulus - 1 - value) / 2 ^ shift))).toUint256.val =
        SignedArithSpec.specModulus - 1 -
          (SignedArithSpec.specModulus - 1 - value) / 2 ^ shift
      rw [hwrap]
      unfold SignedArithSpec.specModulus Compiler.Constants.evmModulus
      omega
  · have hgeShift : 256 ≤ shift := Nat.not_lt.mp hshift
    rw [if_pos hgeShift]
    by_cases hval : value < SignedArithSpec.specSignBit
    · have hto :
          ¬ ({ word := { val := value, isLt := hv } } : Verity.Core.Int256).toInt < 0 := by
        rw [Verity.Core.Int256.toInt_of_lt_signBit]
        · exact not_lt.mpr (Int.natCast_nonneg _)
        · simpa [Verity.Core.Int256.signBit, SignedArithSpec.specSignBit] using hval
      rw [if_neg hto]
      rw [SignedArithSpec.sarSpec_of_shift_ge_nonneg shift value hgeShift hval]
      change (Verity.Core.Uint256.ofNat 0).val = 0
      rfl
    · have hge : SignedArithSpec.specSignBit ≤ value := Nat.le_of_not_lt hval
      have hto :
          ({ word := { val := value, isLt := hv } } : Verity.Core.Int256).toInt < 0 := by
        rw [Verity.Core.Int256.toInt_of_ge_signBit]
        · unfold Compiler.Constants.evmModulus at hv
          unfold SignedArithSpec.specSignBit at hge
          simp [Verity.Core.Int256.modulus, Verity.Core.Uint256.modulus,
            Verity.Core.UINT256_MODULUS]
          omega
        · simpa [Verity.Core.Int256.signBit, SignedArithSpec.specSignBit] using hge
      rw [if_pos hto]
      rw [SignedArithSpec.sarSpec_of_shift_ge_neg shift value hgeShift hge]
      have hnegOne := int256_ofInt_negSucc_toUint256_val 0 (by
        unfold Compiler.Constants.evmModulus
        omega)
      simpa [Int.negSucc_eq, Verity.Core.Int256.toUint256,
        SignedArithSpec.specModulus] using hnegOne

/-- Core sar equivalence: Verity's `Int256.sar` agrees with EVMYulLean's `UInt256.sar`.

Both sides reduce through `SignedArithSpec.sarSpec`: the EVMYulLean side
uses complement-shift-complement for negative words, while the Verity side
uses `Int.fdiv`; the helpers above identify the negative `fdiv` branch with
the same two's-complement raw-word result. -/
theorem int256_sar_toUint256_val_eq_uint256_sar (shift value : Nat)
    (hs : shift < Compiler.Constants.evmModulus) (hv : value < Compiler.Constants.evmModulus) :
    (Verity.Core.Int256.sar
      (Verity.Core.Int256.ofUint256 ⟨shift, hs⟩)
      (Verity.Core.Int256.ofUint256 ⟨value, hv⟩)).toUint256.val =
    EvmYul.UInt256.toNat (EvmYul.UInt256.sar ⟨⟨shift, by rw [EvmYul.UInt256.size]; exact hs⟩⟩
                                               ⟨⟨value, by rw [EvmYul.UInt256.size]; exact hv⟩⟩) := by
  rw [uint256_sar_toNat_eq_sarSpec]
  exact int256_sar_toUint256_val_eq_sarSpec shift value hs hv
end Compiler.Proofs.YulGeneration.Backends
