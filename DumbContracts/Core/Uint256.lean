/-
  Core Uint256 Operations

  This module provides arithmetic operations with EVM semantics:
  - All operations wrap at 2^256 (modular arithmetic)
  - Division and modulo by zero return 0 (matches EVM)
  - Provides overflow/underflow detection predicates

  These operations ensure semantic equivalence between EDSL
  verification and compiled EVM execution.
-/

namespace DumbContracts.Core

-- EVM maximum value for uint256
def MAX_UINT256 : Nat := 2^256 - 1

-- 256-bit modulus
def UINT256_MODULUS : Nat := 2^256

structure Uint256 where
  val : Nat
  isLt : val < UINT256_MODULUS
  deriving DecidableEq

namespace Uint256

def modulus : Nat := UINT256_MODULUS

theorem modulus_pos : 0 < modulus := by
  have h2 : (0 : Nat) < (2 : Nat) := by decide
  have h : 0 < (2 : Nat) ^ 256 := Nat.pow_pos h2
  simp [modulus]
  exact h

theorem max_uint256_succ_eq_modulus : MAX_UINT256 + 1 = modulus := by
  have h2 : (0 : Nat) < (2 : Nat) := by decide
  have hle : 1 ≤ (2 ^ 256) := by
    exact Nat.succ_le_of_lt (Nat.pow_pos (a := 2) (n := 256) h2)
  simpa [MAX_UINT256, modulus, UINT256_MODULUS] using (Nat.sub_add_cancel hle)

theorem val_le_max (a : Uint256) : a.val ≤ MAX_UINT256 := by
  have hlt : a.val < modulus := a.isLt
  have hlt' : a.val < MAX_UINT256 + 1 := by
    simpa [max_uint256_succ_eq_modulus] using hlt
  exact Nat.lt_succ_iff.mp hlt'

def ofNat (n : Nat) : Uint256 :=
  ⟨n % modulus, Nat.mod_lt _ modulus_pos⟩

instance : OfNat Uint256 n := ⟨ofNat n⟩
instance : Inhabited Uint256 := ⟨ofNat 0⟩
instance : Repr Uint256 := ⟨fun u _ => repr u.val⟩
instance : Coe Uint256 Nat := ⟨Uint256.val⟩
instance : Coe Nat Uint256 := ⟨ofNat⟩

@[simp] theorem val_ofNat (n : Nat) : (ofNat n).val = n % modulus := rfl
@[simp] theorem coe_ofNat (n : Nat) : ((ofNat n : Uint256) : Nat) = n % modulus := rfl

@[simp] theorem val_zero : (0 : Uint256).val = 0 := by
  change (ofNat 0).val = 0
  simp [ofNat]

@[simp] theorem val_one : (1 : Uint256).val = 1 := by
  change (ofNat 1).val = 1
  have hlt : (1 : Nat) < modulus := by
    dsimp [modulus, UINT256_MODULUS]
    decide
  simp [ofNat, Nat.mod_eq_of_lt hlt]
@[simp] theorem val_ite {c : Prop} [Decidable c] (t e : Uint256) :
  (ite c t e).val = ite c t.val e.val := by
  by_cases c <;> simp [*]

-- Order instances
instance : LT Uint256 := ⟨fun a b => a.val < b.val⟩
instance : LE Uint256 := ⟨fun a b => a.val ≤ b.val⟩
instance (a b : Uint256) : Decidable (a < b) := by
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      change Decidable (a < b)
      exact inferInstance
instance (a b : Uint256) : Decidable (a ≤ b) := by
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      change Decidable (a ≤ b)
      exact inferInstance

@[simp] theorem le_def (a b : Uint256) : (a ≤ b) = (a.val ≤ b.val) := rfl
@[simp] theorem lt_def (a b : Uint256) : (a < b) = (a.val < b.val) := rfl

-- Modular addition (wraps at 2^256)
def add (a b : Uint256) : Uint256 := ofNat (a.val + b.val)

-- Modular subtraction (two's complement wrapping)
def sub (a b : Uint256) : Uint256 :=
  if b.val ≤ a.val then
    ofNat (a.val - b.val)
  else
    ofNat (modulus - (b.val - a.val))

-- Modular multiplication (wraps at 2^256)
def mul (a b : Uint256) : Uint256 := ofNat (a.val * b.val)

-- Division (returns 0 on division by zero, matching EVM)
def div (a b : Uint256) : Uint256 :=
  if b.val = 0 then ofNat 0 else ofNat (a.val / b.val)

-- Modulo (returns 0 on mod by zero, matching EVM)
def mod (a b : Uint256) : Uint256 :=
  if b.val = 0 then ofNat 0 else ofNat (a.val % b.val)

-- Bitwise operations (EVM semantics)
def and (a b : Uint256) : Uint256 := ofNat (Nat.land a.val b.val)
def or (a b : Uint256) : Uint256 := ofNat (Nat.lor a.val b.val)
def xor (a b : Uint256) : Uint256 := ofNat (Nat.xor a.val b.val)
def not (a : Uint256) : Uint256 := ofNat (MAX_UINT256 - a.val)

-- Shifts (EVM semantics)
def shl (a n : Uint256) : Uint256 := ofNat (a.val <<< n.val)
def shr (a n : Uint256) : Uint256 := ofNat (a.val >>> n.val)

-- Overflow detection predicates for safety proofs (on raw Nat values)
def willAddOverflow (a b : Uint256) : Bool :=
  a.val + b.val ≥ modulus

def willSubUnderflow (a b : Uint256) : Bool :=
  b.val > a.val

def willMulOverflow (a b : Uint256) : Bool :=
  a.val * b.val ≥ modulus

-- Instances for infix operators
instance : HAdd Uint256 Uint256 Uint256 := ⟨add⟩
instance : HSub Uint256 Uint256 Uint256 := ⟨sub⟩
instance : HMul Uint256 Uint256 Uint256 := ⟨mul⟩
instance : HDiv Uint256 Uint256 Uint256 := ⟨div⟩
instance : HMod Uint256 Uint256 Uint256 := ⟨mod⟩
instance : Add Uint256 := ⟨add⟩
instance : Sub Uint256 := ⟨sub⟩
instance : Mul Uint256 := ⟨mul⟩
instance : Div Uint256 := ⟨div⟩
instance : Mod Uint256 := ⟨mod⟩

-- Lemmas for modular arithmetic reasoning when no overflow/underflow occurs.

theorem add_eq_of_lt {a b : Uint256} (h : a.val + b.val < modulus) :
  ((a + b : Uint256) : Nat) = a.val + b.val := by
  simpa [HAdd.hAdd, add, ofNat] using (Nat.mod_eq_of_lt h)

theorem mul_eq_of_lt {a b : Uint256} (h : a.val * b.val < modulus) :
  ((a * b : Uint256) : Nat) = a.val * b.val := by
  simpa [HMul.hMul, mul, ofNat] using (Nat.mod_eq_of_lt h)

theorem sub_eq_of_le {a b : Uint256} (h : b.val ≤ a.val) :
  ((a - b : Uint256) : Nat) = a.val - b.val := by
  have hlt : a.val - b.val < modulus := by
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
  simpa [HSub.hSub, sub, h, ofNat] using (Nat.mod_eq_of_lt hlt)

theorem sub_val_of_gt {a b : Uint256} (h : b.val > a.val) :
  (sub a b).val = (modulus - (b.val - a.val)) % modulus := by
  have h' : ¬ b.val ≤ a.val := Nat.not_le_of_gt h
  simp [sub, h', ofNat]

@[ext] theorem ext {a b : Uint256} (h : a.val = b.val) : a = b := by
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      cases h
      have : ha = hb := by
        apply Subsingleton.elim
      cases this
      rfl

@[simp] theorem zero_add (a : Uint256) : (0 : Uint256) + a = a := by
  apply ext
  have hlt : a.val < modulus := a.isLt
  have hlt' : 0 + a.val < modulus := by simpa using hlt
  calc
    ((0 : Uint256) + a).val = (0 + a.val) % modulus := by
      simp [HAdd.hAdd, add, ofNat]
    _ = 0 + a.val := by
      exact Nat.mod_eq_of_lt hlt'
    _ = a.val := by simp

@[simp] theorem add_zero (a : Uint256) : a + (0 : Uint256) = a := by
  apply ext
  have hlt : a.val < modulus := a.isLt
  have hlt' : a.val + 0 < modulus := by simpa using hlt
  calc
    (a + (0 : Uint256)).val = (a.val + 0) % modulus := by
      simp [HAdd.hAdd, add, ofNat]
    _ = a.val + 0 := by
      exact Nat.mod_eq_of_lt hlt'
    _ = a.val := by simp

@[simp] theorem add_comm (a b : Uint256) : a + b = b + a := by
  apply ext
  calc
    (a + b).val = (a.val + b.val) % modulus := by
      simp [HAdd.hAdd, add, ofNat]
    _ = (b.val + a.val) % modulus := by
      simp [Nat.add_comm]
    _ = (b + a).val := by
      simp [HAdd.hAdd, add, ofNat]

@[simp] theorem sub_zero (a : Uint256) : a - (0 : Uint256) = a := by
  apply ext
  have hlt : a.val < modulus := a.isLt
  have hlt' : a.val - 0 < modulus := by simpa using hlt
  calc
    (a - (0 : Uint256)).val = (a.val - 0) % modulus := by
      simp [HSub.hSub, sub]
    _ = a.val - 0 := by
      exact Nat.mod_eq_of_lt hlt'
    _ = a.val := by simp

@[simp] theorem sub_self (a : Uint256) : a - a = 0 := by
  apply ext
  calc
    (a - a).val = (a.val - a.val) % modulus := by
      simp [HSub.hSub, sub]
    _ = 0 := by simp

@[simp] theorem zero_mul (a : Uint256) : (0 : Uint256) * a = 0 := by
  apply ext
  calc
    ((0 : Uint256) * a).val = (0 * a.val) % modulus := by
      simp [HMul.hMul, mul, ofNat]
    _ = 0 := by simp

@[simp] theorem mul_zero (a : Uint256) : a * (0 : Uint256) = 0 := by
  apply ext
  calc
    (a * (0 : Uint256)).val = (a.val * 0) % modulus := by
      simp [HMul.hMul, mul, ofNat]
    _ = 0 := by simp

@[simp] theorem one_mul (a : Uint256) : (1 : Uint256) * a = a := by
  apply ext
  have hlt : a.val < modulus := a.isLt
  have hlt' : 1 * a.val < modulus := by simpa using hlt
  calc
    ((1 : Uint256) * a).val = (1 * a.val) % modulus := by
      simp [HMul.hMul, mul, ofNat]
    _ = 1 * a.val := by
      exact Nat.mod_eq_of_lt hlt'
    _ = a.val := by simp

@[simp] theorem mul_one (a : Uint256) : a * (1 : Uint256) = a := by
  apply ext
  have hlt : a.val < modulus := a.isLt
  have hlt' : a.val * 1 < modulus := by simpa using hlt
  calc
    (a * (1 : Uint256)).val = (a.val * 1) % modulus := by
      simp [HMul.hMul, mul, ofNat]
    _ = a.val * 1 := by
      exact Nat.mod_eq_of_lt hlt'
    _ = a.val := by simp

@[simp] theorem mul_comm (a b : Uint256) : a * b = b * a := by
  apply ext
  calc
    (a * b).val = (a.val * b.val) % modulus := by
      simp [HMul.hMul, mul, ofNat]
    _ = (b.val * a.val) % modulus := by
      simp [Nat.mul_comm]
    _ = (b * a).val := by
      simp [HMul.hMul, mul, ofNat]

@[simp] theorem div_one (a : Uint256) : a / (1 : Uint256) = a := by
  apply ext
  have hlt : a.val < modulus := a.isLt
  have hlt' : a.val / 1 < modulus := by simpa using hlt
  calc
    (a / (1 : Uint256)).val = (a.val / 1) % modulus := by
      simp [HDiv.hDiv, div, ofNat]
    _ = a.val / 1 := by
      exact Nat.mod_eq_of_lt hlt'
    _ = a.val := by simp

@[simp] theorem zero_div (a : Uint256) : (0 : Uint256) / a = 0 := by
  apply ext
  by_cases h : a.val = 0
  · simp [HDiv.hDiv, div, h]
  · calc
      ((0 : Uint256) / a).val = (0 / a.val) % modulus := by
        simp [HDiv.hDiv, div, h, ofNat]
      _ = 0 := by simp

theorem sub_add_cancel_of_lt {a b : Uint256} (ha : a.val < modulus) (hb : b.val < modulus) :
  (a + b - b) = a := by
  cases a with
  | mk a ha' =>
    cases b with
    | mk b hb' =>
      apply ext
      let m : Nat := modulus
      have ha'' : a < m := by simpa [m] using ha
      have hb'' : b < m := by simpa [m] using hb
      by_cases h : a + b < m
      · have hb_le : b ≤ a + b := Nat.le_add_left _ _
        have hmod : (a + b) % m = a + b := Nat.mod_eq_of_lt h
        have hb_le' : b ≤ (a + b) % m := by
          calc b
            _ ≤ a + b := hb_le
            _ = (a + b) % m := hmod.symm
        -- No overflow: direct cancellation.
        show (sub (add ⟨a, ha'⟩ ⟨b, hb'⟩) ⟨b, hb'⟩).val = a
        simp only [add, sub, ofNat, val_ofNat, if_pos hb_le']
        calc ((a + b) % m - b) % m
          _ = (a + b - b) % m := by rw [hmod]
          _ = a % m := by rw [Nat.add_sub_cancel]
          _ = a := Nat.mod_eq_of_lt ha''
      · have h_ge : m ≤ a + b := Nat.le_of_not_gt h
        have hlt_sum : a + b < m + m := Nat.add_lt_add ha'' hb''
        have hlt : a + b - m < m := Nat.sub_lt_left_of_lt_add h_ge hlt_sum
        have hmod : (a + b) % m = a + b - m := by
          have hmod' : (a + b) % m = (a + b - m) % m := Nat.mod_eq_sub_mod h_ge
          have hmod'' : (a + b - m) % m = a + b - m := Nat.mod_eq_of_lt hlt
          simp [hmod', hmod'']
        have hlt' : a + b < b + m := by
          have h' : a + b < m + b := Nat.add_lt_add_right ha'' b
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'
        have hbgt : b > a + b - m := by
          exact Nat.sub_lt_right_of_lt_add h_ge hlt'
        have hbnot : ¬ b ≤ a + b - m := Nat.not_le_of_gt hbgt
        have hle : a + b - m ≤ b := Nat.le_of_lt hbgt
        have hsum : (m - a) + (a + b - m) = b := by
          have hma : a ≤ m := Nat.le_of_lt ha''
          calc
            (m - a) + (a + b - m)
                = (m - a) + (a + b) - m := by
                    symm
                    exact Nat.add_sub_assoc h_ge (m - a)
            _ = ((m - a) + a) + b - m := by
                    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            _ = m + b - m := by
                    simp [Nat.sub_add_cancel hma, Nat.add_assoc]
            _ = b := by
                    simpa using (Nat.add_sub_cancel_left m b)
        have hdiff : b - (a + b - m) = m - a := by
          exact (Nat.sub_eq_iff_eq_add hle).2 hsum.symm
        have hbnot' : ¬ b ≤ (a + b) % m := by
          intro hc
          have : b ≤ a + b - m := by calc b
            _ ≤ (a + b) % m := hc
            _ = a + b - m := hmod
          exact hbnot this
        -- Overflow: wrap-around branch.
        let aU : Uint256 := ⟨a, ha'⟩
        let bU : Uint256 := ⟨b, hb'⟩
        have hma : a ≤ m := Nat.le_of_lt ha''
        have hsub : m - (m - a) = a := by
          have hle' : m - a ≤ m := Nat.sub_le _ _
          exact (Nat.sub_eq_iff_eq_add hle').2 (by
            have h1 : m - a + a = m := Nat.sub_add_cancel hma
            simpa [Nat.add_comm] using h1.symm)
        have hval' : (aU + bU - bU).val = (m - (b - (a + b) % m)) % m := by
          have hgt : b > (a + b) % m := by
            exact Nat.lt_of_not_ge hbnot'
          have hgt' : bU.val > (add aU bU).val := by
            simpa [aU, bU, add, ofNat] using hgt
          calc
            (aU + bU - bU).val = (sub (add aU bU) bU).val := rfl
            _ = (m - (bU.val - (add aU bU).val)) % m := by
                simp [sub_val_of_gt, hgt']
            _ = (m - (b - (a + b) % m)) % m := by
                simp [aU, bU, add, ofNat]
        calc
          (aU + bU - bU).val = (m - (b - (a + b) % m)) % m := hval'
          _ = (m - (b - (a + b - m))) % m := by
                  simp [hmod]
          _ = (m - (m - a)) % m := by
                  simp [hdiff]
          _ = a % m := by
                  simp [hsub]
          _ = a := by
                  exact Nat.mod_eq_of_lt ha''

theorem sub_add_cancel (a b : Uint256) : (a + b - b) = a :=
  sub_add_cancel_of_lt a.isLt b.isLt

end Uint256

end DumbContracts.Core
