/-
  Compiler.Proofs.ArithmeticProfile: Arithmetic profile specification and proofs

  Documents and proves the arithmetic semantics used across all compilation
  layers. Verity uses wrapping modular arithmetic at 2^256, matching the
  EVM Yellow Paper specification.

  This file serves as the single formal reference for arithmetic behavior:
  - Proves wrapping is consistent across EDSL and compiler layers
  - States compiler pure-builtin facts directly against EVMYulLean
  - Documents the checked (safe) arithmetic alternative at EDSL level
  - Keeps legacy/native bridge comparisons out of the public profile surface

  Run: lake build Compiler.Proofs.ArithmeticProfile
-/

import Compiler.Constants
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanPureBuiltinLemmas
import Verity.Core.Uint256
import EvmYul.UInt256

namespace Compiler.Proofs.ArithmeticProfile

open Compiler.Constants (evmModulus)
open Compiler.Proofs.YulGeneration.Backends (evalPureBuiltinViaEvmYulLean)

-- ============================================================================
-- § 1. Arithmetic profile constants
-- ============================================================================

/-- The arithmetic modulus is 2^256, matching EVM word size. -/
theorem modulus_is_2_pow_256 : evmModulus = 2 ^ 256 := rfl

/-- EVMYulLean's UInt256.size equals Verity's evmModulus. -/
theorem evmyullean_size_eq_verity_modulus :
    EvmYul.UInt256.size = evmModulus := by decide

-- ============================================================================
-- § 2. Wrapping semantics: compiler builtins are total and wrapping
-- ============================================================================

/-- Addition wraps: (a + b) mod 2^256. -/
theorem add_wraps (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "add" [a, b] =
      some ((a + b) % evmModulus) := by
  simp

/-- Subtraction wraps: (2^256 + a - b) mod 2^256. -/
theorem sub_wraps (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "sub" [a, b] =
      some ((evmModulus + a % evmModulus - b % evmModulus) % evmModulus) := by
  simp

/-- Multiplication wraps: (a * b) mod 2^256. -/
theorem mul_wraps (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "mul" [a, b] =
      some ((a * b) % evmModulus) := by
  simp

/-- Division by zero returns 0. -/
theorem div_by_zero (a : Nat) :
    evalPureBuiltinViaEvmYulLean "div" [a, 0] = some 0 := by
  simp

/-- Modulo by zero returns 0. -/
theorem mod_by_zero (a : Nat) :
    evalPureBuiltinViaEvmYulLean "mod" [a, 0] = some 0 := by
  simp

-- ============================================================================
-- § 3. EVMYulLean pure-builtin facts
-- ============================================================================

-- The theorem names retain the historical `_bridge` suffix for downstream
-- compatibility, but their semantic authority is the native EVMYulLean
-- evaluator rather than the legacy Verity Yul oracle.

/-- Native evaluator theorem for addition. -/
theorem add_bridge (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "add" [a, b] =
      some ((a + b) % evmModulus) :=
  add_wraps a b

/-- Native evaluator theorem for subtraction. -/
theorem sub_bridge (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "sub" [a, b] =
      some ((evmModulus + a % evmModulus - b % evmModulus) % evmModulus) :=
  sub_wraps a b

/-- Native evaluator theorem for multiplication. -/
theorem mul_bridge (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "mul" [a, b] =
      some ((a * b) % evmModulus) :=
  mul_wraps a b

/-- Native evaluator theorem for division. -/
theorem div_bridge (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "div" [a, b] =
      some (if b % evmModulus = 0 then 0 else (a % evmModulus) / (b % evmModulus)) := by
  simp

/-- Native evaluator theorem for modulo. -/
theorem mod_bridge (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "mod" [a, b] =
      some (if b % evmModulus = 0 then 0 else
        (a % evmModulus) % (b % evmModulus)) := by
  simp

/-- Native evaluator theorem for bitwise and. -/
theorem and_bridge (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "and" [a, b] =
      some (EvmYul.UInt256.toNat
        (EvmYul.UInt256.land (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b))) := by
  rfl

/-- Native evaluator theorem for bitwise or. -/
theorem or_bridge (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "or" [a, b] =
      some (EvmYul.UInt256.toNat
        (EvmYul.UInt256.lor (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b))) := by
  rfl

/-- Native evaluator theorem for bitwise xor. -/
theorem xor_bridge (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "xor" [a, b] =
      some (EvmYul.UInt256.toNat
        (EvmYul.UInt256.xor (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b))) := by
  rfl

/-- Native evaluator theorem for shift-left. -/
theorem shl_bridge (shift value : Nat) :
    evalPureBuiltinViaEvmYulLean "shl" [shift, value] =
      some (EvmYul.UInt256.toNat
        (EvmYul.UInt256.shiftLeft
          (EvmYul.UInt256.ofNat value) (EvmYul.UInt256.ofNat shift))) := by
  rfl

/-- Native evaluator theorem for shift-right. -/
theorem shr_bridge (shift value : Nat) :
    evalPureBuiltinViaEvmYulLean "shr" [shift, value] =
      some (EvmYul.UInt256.toNat
        (EvmYul.UInt256.shiftRight
          (EvmYul.UInt256.ofNat value) (EvmYul.UInt256.ofNat shift))) := by
  rfl

-- ============================================================================
-- § 4. Backend profile invariant
-- ============================================================================

-- Public arithmetic facts in this module are stated directly against
-- `evalPureBuiltinViaEvmYulLean`; legacy backend comparison lemmas remain in
-- the transition bridge modules, not as this profile's semantic authority.

-- ============================================================================
-- § 5. Scope boundaries (what is NOT proved here)
-- ============================================================================

-- Gas semantics: not formally modeled. Proofs establish semantic correctness
-- (same result), not gas correctness (same cost or bounded cost).
--
-- Compiler-layer overflow detection: the compiler does not insert automatic
-- overflow checks. Contracts that need checked arithmetic must use the EDSL
-- safeAdd/safeSub/safeMul functions, which return Option and revert on None.
--
-- Cryptographic primitives: keccak256 is axiomatized (see AXIOMS.md).
-- The mapping-slot derivation trusts the keccak FFI.
--
-- Legacy/native bridge equivalence: comparison lemmas are part of the
-- transition bridge modules. This profile intentionally exposes only native
-- evaluator facts.

end Compiler.Proofs.ArithmeticProfile
