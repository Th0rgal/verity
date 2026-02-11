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
  have h2 : (0 : Nat) < 2 := by decide
  simpa [modulus] using (Nat.pow_pos h2 256)

def ofNat (n : Nat) : Uint256 :=
  ⟨n % modulus, Nat.mod_lt _ modulus_pos⟩

instance : OfNat Uint256 n := ⟨ofNat n⟩
instance : Inhabited Uint256 := ⟨ofNat 0⟩
instance : Repr Uint256 := ⟨fun u => repr u.val⟩
instance : Coe Uint256 Nat := ⟨Uint256.val⟩
instance : Coe Nat Uint256 := ⟨ofNat⟩

@[simp] theorem val_ofNat (n : Nat) : (ofNat n).val = n % modulus := rfl
@[simp] theorem coe_ofNat (n : Nat) : ((ofNat n : Uint256) : Nat) = n % modulus := rfl

-- Order instances
instance : LT Uint256 := ⟨fun a b => a.val < b.val⟩
instance : LE Uint256 := ⟨fun a b => a.val ≤ b.val⟩
instance (a b : Uint256) : Decidable (a < b) := by
  cases a; cases b; dsimp [LT.lt]; infer_instance
instance (a b : Uint256) : Decidable (a ≤ b) := by
  cases a; cases b; dsimp [LE.le]; infer_instance

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

-- Lemmas for modular arithmetic reasoning when no overflow/underflow occurs.

theorem add_eq_of_lt {a b : Uint256} (h : a.val + b.val < modulus) :
  ((a + b : Uint256) : Nat) = a.val + b.val := by
  simp [HAdd.hAdd, add, ofNat, Nat.mod_eq_of_lt h]

theorem sub_eq_of_le {a b : Uint256} (h : b.val ≤ a.val) :
  ((a - b : Uint256) : Nat) = a.val - b.val := by
  have hlt : a.val - b.val < modulus := by
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
  simp [HSub.hSub, sub, h, ofNat, Nat.mod_eq_of_lt hlt]

theorem sub_add_cancel (a b : Uint256) : (a + b - b) = a := by
  -- Since all values are reduced modulo 2^256, add/sub cancel as expected.
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      -- Expand definitions and reduce using Nat modular arithmetic.
      simp [HAdd.hAdd, HSub.hSub, add, sub, ofNat] at *

end Uint256

end DumbContracts.Core
