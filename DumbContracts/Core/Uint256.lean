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

namespace Uint256

-- 256-bit modulus
def modulus : Nat := 2^256

-- Modular addition (wraps at 2^256)
def add (a b : Nat) : Nat := (a + b) % modulus

-- Modular subtraction (two's complement wrapping)
def sub (a b : Nat) : Nat :=
  if b ≤ a then a - b
  else modulus - (b - a)

-- Modular multiplication (wraps at 2^256)
def mul (a b : Nat) : Nat := (a * b) % modulus

-- Division (returns 0 on division by zero, matching EVM)
def div (a b : Nat) : Nat :=
  if b = 0 then 0 else a / b

-- Modulo (returns 0 on mod by zero, matching EVM)
def mod (a b : Nat) : Nat :=
  if b = 0 then 0 else a % b

-- Bitwise operations (EVM semantics)
def and (a b : Nat) : Nat := Nat.land (a % modulus) (b % modulus)
def or (a b : Nat) : Nat := Nat.lor (a % modulus) (b % modulus)
def xor (a b : Nat) : Nat := Nat.xor (a % modulus) (b % modulus)
def not (a : Nat) : Nat := MAX_UINT256 - (a % modulus)

-- Shifts (EVM semantics)
def shl (a n : Nat) : Nat := ((a % modulus) <<< n) % modulus
def shr (a n : Nat) : Nat := (a % modulus) >>> n

-- Overflow detection predicates for safety proofs

def willAddOverflow (a b : Nat) : Bool :=
  a + b ≥ modulus

def willSubUnderflow (a b : Nat) : Bool :=
  b > a

def willMulOverflow (a b : Nat) : Bool :=
  a * b ≥ modulus

-- Lemmas for modular arithmetic reasoning when no overflow/underflow occurs.

theorem add_eq_of_lt {a b : Nat} (h : a + b < modulus) : add a b = a + b := by
  simp [add, Nat.mod_eq_of_lt h]

theorem sub_eq_of_le {a b : Nat} (h : b ≤ a) : sub a b = a - b := by
  simp [sub, h]

/-- Cancellation for modular addition/subtraction on valid uint256 inputs. -/
theorem sub_add_cancel_of_lt {a b : Nat} (ha : a < modulus) (hb : b < modulus) :
  sub (add a b) b = a := by
  let m : Nat := modulus
  have ha' : a < m := by simpa [m] using ha
  have hb' : b < m := by simpa [m] using hb
  by_cases h : a + b < m
  · have hb_le : b ≤ a + b := Nat.le_add_left _ _
    have hmod : (a + b) % m = a + b := Nat.mod_eq_of_lt h
    simp [add, sub, hmod, hb_le, Nat.add_sub_cancel]
  · have h_ge : m ≤ a + b := Nat.le_of_not_gt h
    have hlt_sum : a + b < m + m := Nat.add_lt_add ha' hb'
    have hlt : a + b - m < m := Nat.sub_lt_left_of_lt_add h_ge hlt_sum
    have hmod : (a + b) % m = a + b - m := by
      have hmod' : (a + b) % m = (a + b - m) % m := Nat.mod_eq_sub_mod h_ge
      have hmod'' : (a + b - m) % m = a + b - m := Nat.mod_eq_of_lt hlt
      simp [hmod', hmod'']
    have hlt' : a + b < b + m := by
      have h' : a + b < m + b := Nat.add_lt_add_right ha' b
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'
    have hbgt : b > a + b - m := by
      exact Nat.sub_lt_right_of_lt_add h_ge hlt'
    have hbnot : ¬ b ≤ a + b - m := Nat.not_le_of_gt hbgt
    have hle : a + b - m ≤ b := Nat.le_of_lt hbgt
    have hsum : (m - a) + (a + b - m) = b := by
      have hma : a ≤ m := Nat.le_of_lt ha'
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
    -- Use the wrap-around branch to cancel.
    simp [add, sub, hmod, hbnot, hdiff, Nat.sub_sub_self (Nat.le_of_lt ha')]

end Uint256

end DumbContracts.Core
