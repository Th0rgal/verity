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
  dsimp [modulus, UINT256_MODULUS]
  have h2 : (0 : Nat) < (2 : Nat) := by decide
  exact Nat.pow_pos (a := 2) (n := 256) h2

def ofNat (n : Nat) : Uint256 :=
  ⟨n % modulus, Nat.mod_lt _ modulus_pos⟩

instance : OfNat Uint256 n := ⟨ofNat n⟩
instance : Inhabited Uint256 := ⟨ofNat 0⟩
instance : Repr Uint256 := ⟨fun u _ => repr u.val⟩
instance : Coe Uint256 Nat := ⟨Uint256.val⟩
instance : Coe Nat Uint256 := ⟨ofNat⟩

@[simp] theorem val_ofNat (n : Nat) : (ofNat n).val = n % modulus := rfl
@[simp] theorem coe_ofNat (n : Nat) : ((ofNat n : Uint256) : Nat) = n % modulus := rfl
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

@[simp] theorem sub_val_of_le {a b : Uint256} (h : b.val ≤ a.val) :
  (sub a b).val = (a.val - b.val) % modulus := by
  simp [sub, h]

@[simp] theorem sub_val_of_gt {a b : Uint256} (h : b.val > a.val) :
  (sub a b).val = (modulus - (b.val - a.val)) % modulus := by
  have h' : ¬ b.val ≤ a.val := Nat.not_le_of_gt h
  simp [sub, h', h]

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
instance : HPow Uint256 Nat Uint256 := ⟨fun a n => ofNat (a.val ^ n)⟩

-- Lemmas for modular arithmetic reasoning when no overflow/underflow occurs.

theorem add_eq_of_lt {a b : Uint256} (h : a.val + b.val < modulus) :
  ((a + b : Uint256) : Nat) = a.val + b.val := by
  simpa [HAdd.hAdd, add, ofNat] using (Nat.mod_eq_of_lt h)

theorem sub_eq_of_le {a b : Uint256} (h : b.val ≤ a.val) :
  ((a - b : Uint256) : Nat) = a.val - b.val := by
  have hlt : a.val - b.val < modulus := by
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
  simpa [HSub.hSub, sub, h, ofNat] using (Nat.mod_eq_of_lt hlt)

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

theorem sub_add_cancel_of_lt {a b : Uint256} (ha : a.val < modulus) (hb : b.val < modulus) :
  (a + b - b) = a := by
  cases a with
  | mk a ha' =>
    cases b with
    | mk b hb' =>
      let aU : Uint256 := ⟨a, ha'⟩
      let bU : Uint256 := ⟨b, hb'⟩
      apply ext
      have ha'' : a < modulus := by simpa using ha
      have hb'' : b < modulus := by simpa using hb
      by_cases h : a + b < modulus
      · have hb_le : b ≤ a + b := Nat.le_add_left _ _
        have hmod : (a + b) % modulus = a + b := Nat.mod_eq_of_lt h
        have hb_le' : b ≤ (a + b) % modulus := by
          simpa [hmod] using hb_le
        have hval' : (aU + bU - bU).val = ((a + b) % modulus - b) % modulus := by
          have hle' : bU.val ≤ (add aU bU).val := by
            simpa [aU, bU, add, ofNat] using hb_le'
          calc
            (aU + bU - bU).val = (sub (add aU bU) bU).val := rfl
            _ = ((add aU bU).val - bU.val) % modulus := by
                simp [sub_val_of_le, hle']
            _ = ((a + b) % modulus - b) % modulus := by
                simp [aU, bU, add, ofNat]
        -- No overflow: direct cancellation.
        calc
          (aU + bU - bU).val = ((a + b) % modulus - b) % modulus := hval'
          _ = (a + b - b) % modulus := by
                  simp [hmod]
          _ = a % modulus := by
                  simp [Nat.add_sub_cancel]
          _ = a := by
                  exact Nat.mod_eq_of_lt ha''
      · have h_ge : modulus ≤ a + b := Nat.le_of_not_gt h
        have hlt_sum : a + b < modulus + modulus := Nat.add_lt_add ha'' hb''
        have hlt : a + b - modulus < modulus := Nat.sub_lt_left_of_lt_add h_ge hlt_sum
        have hmod : (a + b) % modulus = a + b - modulus := by
          have hmod' : (a + b) % modulus = (a + b - modulus) % modulus :=
            Nat.mod_eq_sub_mod h_ge
          have hmod'' : (a + b - modulus) % modulus = a + b - modulus := Nat.mod_eq_of_lt hlt
          simp [hmod', hmod'']
        have hlt' : a + b < b + modulus := by
          have h' : a + b < modulus + b := Nat.add_lt_add_right ha'' b
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'
        have hbgt : b > a + b - modulus := by
          exact Nat.sub_lt_right_of_lt_add h_ge hlt'
        have hle : a + b - modulus ≤ b := Nat.le_of_lt hbgt
        have hsum : (modulus - a) + (a + b - modulus) = b := by
          have hma : a ≤ modulus := Nat.le_of_lt ha''
          calc
            (modulus - a) + (a + b - modulus)
                = (modulus - a) + (a + b) - modulus := by
                    symm
                    exact Nat.add_sub_assoc h_ge (modulus - a)
            _ = ((modulus - a) + a) + b - modulus := by
                    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            _ = modulus + b - modulus := by
                    simp [Nat.sub_add_cancel hma, Nat.add_assoc]
            _ = b := by
                    simpa using (Nat.add_sub_cancel_left modulus b)
        have hdiff : b - (a + b - modulus) = modulus - a := by
          exact (Nat.sub_eq_iff_eq_add hle).2 hsum.symm
        have hbnot' : ¬ b ≤ (a + b) % modulus := by
          have hbnot : ¬ b ≤ a + b - modulus := Nat.not_le_of_gt hbgt
          simpa [hmod] using hbnot
        -- Overflow: wrap-around branch.
        have hma : a ≤ modulus := Nat.le_of_lt ha''
        have hsub : modulus - (modulus - a) = a := by
          have hle' : modulus - a ≤ modulus := Nat.sub_le _ _
          exact (Nat.sub_eq_iff_eq_add hle').2 (by
            have h1 : modulus - a + a = modulus := Nat.sub_add_cancel hma
            simpa [Nat.add_comm] using h1.symm)
        have hval' : (aU + bU - bU).val = (modulus - (b - (a + b) % modulus)) % modulus := by
          by_cases hcase : b ≤ (a + b) % modulus
          · exact (False.elim (hbnot' hcase))
          · simp [aU, bU, HAdd.hAdd, HSub.hSub, add, sub, ofNat, hcase]
        calc
          (aU + bU - bU).val = (modulus - (b - (a + b) % modulus)) % modulus := hval'
          _ = (modulus - (b - (a + b - modulus))) % modulus := by
                  simp [hmod]
          _ = (modulus - (modulus - a)) % modulus := by
                  simp [hdiff]
          _ = a % modulus := by
                  simp [hsub]
          _ = a := by
                  exact Nat.mod_eq_of_lt ha''

theorem sub_add_cancel (a b : Uint256) : (a + b - b) = a :=
  sub_add_cancel_of_lt a.isLt b.isLt

end Uint256

end DumbContracts.Core
