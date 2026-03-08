/-
  Math Safety Library

  This module provides checked arithmetic operations that prevent
  overflow and underflow issues. Operations return Option types
  to signal when bounds are exceeded.

  Philosophy: Optional safety - examples can choose between fast
  unchecked arithmetic (+ and -) or safe checked operations.
-/

import Verity.Core

namespace Verity.Stdlib.Math

open Verity

-- Maximum value for Uint256 (2^256 - 1)
-- Alias of Verity.Core.MAX_UINT256 for backwards compatibility.
abbrev MAX_UINT256 : Nat := Core.MAX_UINT256

-- Safe addition: returns None on overflow
def safeAdd (a b : Uint256) : Option Uint256 :=
  let sum := (a : Nat) + (b : Nat)
  if sum > MAX_UINT256 then
    none
  else
    some (a + b)

-- Safe subtraction: returns None on underflow
def safeSub (a b : Uint256) : Option Uint256 :=
  if (b : Nat) > (a : Nat) then
    none
  else
    some (a - b)

-- Safe multiplication: returns None on overflow
def safeMul (a b : Uint256) : Option Uint256 :=
  let prod := (a : Nat) * (b : Nat)
  if prod > MAX_UINT256 then
    none
  else
    some (a * b)

-- Safe division: returns None if divisor is zero
def safeDiv (a b : Uint256) : Option Uint256 :=
  if b.val = 0 then
    none
  else
    some (a / b)

/-- Fixed-point scaling factor used by `wMulDown` and `wDivUp`. -/
def WAD : Uint256 := 1000000000000000000

/-- `mulDivDown(a, b, c)` = `floor(a * b / c)` under the EVM's `div` semantics. -/
def mulDivDown (a b c : Uint256) : Uint256 :=
  (a * b) / c

/-- `mulDivUp(a, b, c)` = `ceil(a * b / c)` when the numerator fits without wrapping. -/
def mulDivUp (a b c : Uint256) : Uint256 :=
  ((a * b) + (c - 1)) / c

/-- Multiply two wad-scaled values and round down. -/
def wMulDown (a b : Uint256) : Uint256 :=
  mulDivDown a b WAD

/-- Divide two wad-scaled values and round up. -/
def wDivUp (a b : Uint256) : Uint256 :=
  mulDivUp a WAD b

-- Helper: Require with Option - fails if None
-- For Uint256 specifically (can be generalized later if needed)
def requireSomeUint (opt : Option Uint256) (message : String) : Contract Uint256 := do
  match opt with
  | some value => return value
  | none => do
    require false message
    -- This line is unreachable in real execution (require would revert)
    -- Return 0 as a fallback for type checking
    return 0

-- Full-result simp lemmas for requireSomeUint
@[simp] theorem requireSomeUint_some (v : Uint256) (msg : String) (s : ContractState) :
  (requireSomeUint (some v) msg).run s = ContractResult.success v s := rfl

@[simp] theorem requireSomeUint_none (msg : String) (s : ContractState) :
  (requireSomeUint none msg).run s = ContractResult.revert msg s := rfl

@[simp] theorem WAD_val : (WAD : Nat) = 1000000000000000000 := by
  rfl

theorem WAD_ne_zero : WAD ≠ 0 := by
  intro h
  have : ((WAD : Uint256) : Nat) = 0 := by
    simpa using congrArg (fun x : Uint256 => (x : Nat)) h
  have hPos : 0 < (1000000000000000000 : Nat) := by decide
  simp [WAD] at this
  exact (Nat.ne_of_gt hPos) this

@[simp] theorem mulDivDown_def (a b c : Uint256) :
  mulDivDown a b c = (a * b) / c := rfl

@[simp] theorem mulDivUp_def (a b c : Uint256) :
  mulDivUp a b c = ((a * b) + (c - 1)) / c := rfl

@[simp] theorem wMulDown_def (a b : Uint256) :
  wMulDown a b = mulDivDown a b WAD := rfl

@[simp] theorem wDivUp_def (a b : Uint256) :
  wDivUp a b = mulDivUp a WAD b := rfl

end Verity.Stdlib.Math
