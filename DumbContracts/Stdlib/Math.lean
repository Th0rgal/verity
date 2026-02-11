/-
  Math Safety Library

  This module provides checked arithmetic operations that prevent
  overflow and underflow issues. Operations return Option types
  to signal when bounds are exceeded.

  Philosophy: Optional safety - examples can choose between fast
  unchecked arithmetic (+ and -) or safe checked operations.
-/

import DumbContracts.Core

namespace DumbContracts.Stdlib.Math

open DumbContracts

-- Maximum value for Uint256 (2^256 - 1)
-- For Lean's Nat, we define a practical upper bound
def MAX_UINT256 : Nat := 2^256 - 1

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

end DumbContracts.Stdlib.Math
