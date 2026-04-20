/-! # Nat-level Spec for Signed EVM Arithmetic

This module introduces Nat-level specification functions that will mediate
between Verity's `Int256`-based signed operations and EVMYulLean's
`UInt256`-based signed operations in the two remaining admitted bridge
lemmas (`smod_int256_eq_uint256Smod`, `sar_int256_eq_uint256Sar`).

The goal of this scaffolding step (plan #1722 A1a) is to **land only the
spec definitions and their elementary characterizations**. The actual
discharge of the admitted bridge lemmas — rewriting the Verity and
EVMYulLean wrappers to both call into these specs — is deferred to plan
#1722 A2 (smod) and A3 (sar).

Layout:

* `smodSpec a b` encodes the EVM `smod` opcode at the Nat level. The
  spec performs a sign-magnitude decomposition on the raw 256-bit
  words (so the top bit at `2^255` is the sign), then takes
  `|a| % |b|` as Nat arithmetic, and finally re-applies the sign of
  `a` through two's-complement negation when `a` is negative. The
  zero-divisor case reduces to `0`, matching both Verity's
  `Int256.mod b = 0` early return and EVMYulLean's `b.toNat == 0`
  guard in `EvmYul.UInt256.smod`.

* Future (A1b): `sarSpec shift value` — this file will gain a `sar`
  spec once the S1/S2 strategy decision for `sar` lands (see plan
  Bucket A fallback note: `sar` may drop to a `BitVec 256` round-trip
  rather than Nat-level sign extension).

No code here is `sorry`-dependent. No declaration is marked `@[simp]`.
None of the existing bridge artifacts reference these specs yet; that
wiring is part of A2.
-/

namespace Compiler.Proofs.YulGeneration.Backends

namespace SignedArithSpec

/-- The 256-bit modulus used by the EVM, materialized as a Nat so the
spec can live at the Nat level without dragging in `UInt256`/`Int256`
imports. Kept local to this module to avoid colliding with
`Compiler.Proofs.YulGeneration.Builtins.evmModulus`; a later A2 commit
will prove they are propositionally equal. -/
def specModulus : Nat := 2 ^ 256

/-- The 256-bit sign bit boundary: the smallest Nat whose top word-bit
is set. Values `≥ specSignBit` are interpreted as negative in the
two's-complement sense used by both Verity and EVMYulLean. -/
def specSignBit : Nat := 2 ^ 255

theorem specSignBit_lt_specModulus : specSignBit < specModulus := by
  unfold specSignBit specModulus; decide

theorem specModulus_pos : 0 < specModulus := by
  unfold specModulus; decide

theorem specSignBit_pos : 0 < specSignBit := by
  unfold specSignBit; decide

/-- Unsigned magnitude of a raw 256-bit word, interpreted as a signed
Int256 value. For `a < specSignBit` (non-negative), the magnitude is
`a` itself; for `a ≥ specSignBit` (negative), the magnitude is
`specModulus - a` (two's-complement negation). For `a = 0` the
magnitude is `0`; for `a = specSignBit` (the smallest negative value)
the magnitude is `specSignBit` (the absolute value is NOT
representable as a non-negative signed value, but its magnitude as
a Nat is well-defined). -/
def specAbs (a : Nat) : Nat :=
  if a < specSignBit then a else specModulus - a

/-- Signed modulus / remainder at the Nat level.

* If `b = 0`, returns `0` (EVM convention: divide by zero yields zero,
  not an undefined trap).
* Otherwise, decomposes `a` and `b` into sign + magnitude via
  `specAbs`, computes the Nat remainder `|a| % |b|`, and re-applies the
  sign of `a` by two's-complement negation when `a` was negative.
  The sign of `b` does not affect the result, matching both Verity's
  `Int256.mod` (which negates only when `lhs < 0`) and EVMYulLean's
  `EvmYul.UInt256.smod` (`toSigned (sgn a * (|a| % |b|).toNat)`). -/
def smodSpec (a b : Nat) : Nat :=
  if b = 0 then 0
  else
    let absA := specAbs a
    let absB := specAbs b
    let r := absA % absB
    if a < specSignBit then r
    else if r = 0 then 0 else specModulus - r

/-! ### Elementary characterizations of `smodSpec`

These lemmas are the pieces A2 will need when rewriting both wrappers
to call `smodSpec`. They stand on their own and are proven without
any `sorry`. -/

@[simp] theorem smodSpec_b_zero (a : Nat) : smodSpec a 0 = 0 := by
  unfold smodSpec; simp

@[simp] theorem smodSpec_a_zero (b : Nat) : smodSpec 0 b = 0 := by
  unfold smodSpec
  by_cases hb : b = 0
  · simp [hb]
  · have hsign : (0 : Nat) < specSignBit := specSignBit_pos
    simp [hb, specAbs, hsign]

/-- Concrete algebraic fact: `2^256 = 2 * 2^255`. Proven via core
`Nat.pow_succ` + `Nat.mul_comm` rather than `ring` or `native_decide`
to keep this file free of Mathlib tactic imports and to satisfy
`check_lean_hygiene.py`'s kernel-proof requirement. -/
private theorem specModulus_eq_two_mul_specSignBit :
    specModulus = 2 * specSignBit := by
  show (2 : Nat) ^ 256 = 2 * 2 ^ 255
  rw [show (256 : Nat) = 255 + 1 from rfl, Nat.pow_succ, Nat.mul_comm]

/-- `specAbs` never exceeds `specSignBit`: for `a < specSignBit` it
equals `a < specSignBit`; for `a ≥ specSignBit` it equals
`specModulus - a ≤ specModulus - specSignBit = specSignBit`.
Holds unconditionally on `a` because truncated `Nat` subtraction
clamps to `0` when `a ≥ specModulus`. -/
theorem specAbs_le_specSignBit (a : Nat) :
    specAbs a ≤ specSignBit := by
  unfold specAbs
  by_cases h : a < specSignBit
  · simp [h]; exact Nat.le_of_lt h
  · simp [h]
    have hmod := specModulus_eq_two_mul_specSignBit
    omega

/-- Non-negative-`a` closed form for `smodSpec`. When `a < specSignBit`
(the non-negative half of the two's-complement range) and `b ≠ 0`,
`smodSpec` reduces to a plain `specAbs a % specAbs b`. This is the
clean handle A2 will cite for the non-negative `a` sign cases,
avoiding having to re-unfold `smodSpec` mid-proof. -/
theorem smodSpec_of_nonneg (a b : Nat)
    (ha : a < specSignBit) (hb : b ≠ 0) :
    smodSpec a b = specAbs a % specAbs b := by
  unfold smodSpec
  simp [hb, ha]

/-- Negative-`a` closed form for `smodSpec`. When `specSignBit ≤ a`
(the negative half of the two's-complement range) and `b ≠ 0`,
`smodSpec` applies a two's-complement negation to the Nat remainder,
with a guard for `r = 0` that keeps the result in `[0, specModulus)`.
This is the companion to `smodSpec_of_nonneg` for the NP/NN sign
cases of A2. -/
theorem smodSpec_of_neg (a b : Nat)
    (ha : specSignBit ≤ a) (hb : b ≠ 0) :
    smodSpec a b =
      (let r := specAbs a % specAbs b
       if r = 0 then 0 else specModulus - r) := by
  unfold smodSpec
  simp [hb, Nat.not_lt.mpr ha]

/-- `smodSpec` always produces a value in `[0, specModulus)`. This is
the load-bearing boundedness lemma A2 will cite when closing the
`%` reduction on the EVMYulLean wrapper side. -/
theorem smodSpec_lt_specModulus (a b : Nat) (hb : b < specModulus) :
    smodSpec a b < specModulus := by
  unfold smodSpec
  by_cases hb0 : b = 0
  · simp [hb0]; exact specModulus_pos
  simp only [hb0, ↓reduceIte]
  by_cases hasign : a < specSignBit
  · -- Non-negative `a`: result is `specAbs a % specAbs b`, bounded by
    -- `specAbs b ≤ specSignBit < specModulus`.
    simp only [hasign, ↓reduceIte]
    have habs_b_pos : 0 < specAbs b := by
      unfold specAbs
      by_cases hbs : b < specSignBit
      · simp [hbs]; exact Nat.pos_of_ne_zero hb0
      · simp [hbs]
        have hb_ge : specSignBit ≤ b := Nat.le_of_not_lt hbs
        have hmod := specModulus_eq_two_mul_specSignBit
        omega
    have hlt : specAbs a % specAbs b < specAbs b := Nat.mod_lt _ habs_b_pos
    have hbound : specAbs b ≤ specSignBit := specAbs_le_specSignBit b
    have hsign_lt : specSignBit < specModulus := specSignBit_lt_specModulus
    omega
  · -- Negative `a`: result is either `0` or `specModulus - r`, both `< specModulus`.
    simp only [hasign, ↓reduceIte]
    by_cases hr0 : specAbs a % specAbs b = 0
    · simp [hr0]; exact specModulus_pos
    · simp [hr0]
      have hpos : 0 < specAbs a % specAbs b := Nat.pos_of_ne_zero hr0
      omega

end SignedArithSpec

end Compiler.Proofs.YulGeneration.Backends
