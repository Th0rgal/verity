# Arithmetic Profile

Verity uses **wrapping modular arithmetic at 2^256** across all compilation layers, matching the EVM Yellow Paper specification.

This document is the authoritative reference for arithmetic semantics. For formal proofs, see [`Compiler/Proofs/ArithmeticProfile.lean`](../Compiler/Proofs/ArithmeticProfile.lean).

## Wrapping Semantics

All arithmetic in the compilation path (`EDSL -> CompilationModel -> IR -> Yul`) wraps modulo 2^256. There are **no implicit overflow checks** — values silently wrap.

| Operation | Semantics | Div/Mod-by-zero |
|-----------|-----------|-----------------|
| `add(a, b)` | `(a + b) % 2^256` | — |
| `sub(a, b)` | `(2^256 + a - b) % 2^256` | — |
| `mul(a, b)` | `(a * b) % 2^256` | — |
| `div(a, b)` | `a / b` (truncating) | returns 0 |
| `mod(a, b)` | `a % b` | returns 0 |
| `and(a, b)` | bitwise AND | — |
| `or(a, b)` | bitwise OR | — |
| `xor(a, b)` | bitwise XOR | — |
| `not(a)` | `(2^256 - 1) - a` | — |
| `shl(s, v)` | `(v * 2^s) % 2^256` | — |
| `shr(s, v)` | `v / 2^s` | — |
| `lt(a, b)` | `1` if `a < b`, else `0` | — |
| `gt(a, b)` | `1` if `a > b`, else `0` | — |
| `eq(a, b)` | `1` if `a = b`, else `0` | — |
| `iszero(a)` | `1` if `a = 0`, else `0` | — |

## Proof Coverage

Wrapping semantics are **proven** (not assumed) across all three verification layers:

| Layer | Proof location | What is proved |
|-------|---------------|----------------|
| Layer 1 (EDSL) | `Verity/Core/Uint256.lean` | `Uint256.add`, `sub`, `mul`, `div`, `mod` are wrapping modular |
| Layer 1 (EDSL) | `Verity/Proofs/Stdlib/Math.lean` | `safeAdd`, `safeSub`, `safeMul` correctness |
| Compiler | `Compiler/Proofs/YulGeneration/Builtins.lean` | `evalBuiltinCall` implements wrapping for all 15 pure builtins |
| Compiler | `Compiler/Proofs/ArithmeticProfile.lean` | `add_wraps`, `sub_wraps`, `mul_wraps`, `div_by_zero`, `mod_by_zero` |
| EVMYulLean bridge | `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean` | Universal bridge lemmas for all 15 pure builtins: `add`/`sub`/`mul`/`div`/`mod`, `lt`/`gt`/`eq`/`iszero`, `and`/`or`/`xor`/`not`, and `shl`/`shr` |
| EVMYulLean bridge tests | `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeTest.lean` | Regression vectors for the universal pure-builtin bridge lemmas |

The EVMYulLean bridge validates that Verity's `Nat`-modular arithmetic agrees with EVMYulLean's `Fin`-based `UInt256` operations. Current coverage is fully symbolic:
- universal bridge lemmas for 15 pure builtins: `add`, `sub`, `mul`, `div`, `mod`, `lt`, `gt`, `eq`, `iszero`, `and`, `or`, `xor`, `not`, `shl`, and `shr`
- concrete bridge smoke tests are no longer needed for any pure builtin

## Checked (Safe) Arithmetic

For contracts that require overflow protection, the EDSL provides checked operations:

| Operation | Type | Behavior |
|-----------|------|----------|
| `safeAdd a b` | `Option Uint256` | `none` if `a + b > 2^256 - 1` |
| `safeSub a b` | `Option Uint256` | `none` if `b > a` |
| `safeMul a b` | `Option Uint256` | `none` if `a * b > 2^256 - 1` |
| `safeDiv a b` | `Option Uint256` | `none` if `b = 0` |

Checked operations are **EDSL-level constructs**. They are not compiler-enforced — the compiler always uses wrapping arithmetic. Contracts that need checked behavior must explicitly use `safeAdd`/`safeSub`/`safeMul` and handle the `Option` result (e.g., via `requireSomeUint` to revert on `none`).

**Correctness proofs**: `Verity/Proofs/Stdlib/Math.lean` proves that checked operations return the correct result within bounds and `none` otherwise (e.g., `safeAdd_some`, `safeAdd_none`).

`Stdlib.Math` also exposes fixed-point helpers `mulDivDown`, `mulDivUp`, `wMulDown`, and `wDivUp` (the `w` variants fix the divisor/multiplier to `WAD = 10^18`). All lemmas are in `Verity/Proofs/Stdlib/Math.lean` and are intentionally **preconditioned**: they assume the widened numerator stays within `MAX_UINT256`.

| Lemma family | Generic helpers | Wad-specialized helpers |
|--------------|----------------|------------------------|
| Monotonicity (numerator) | `mulDivDown_monotone_left/right`, `mulDivUp_monotone_left/right` | `wMulDown_monotone_left/right`, `wDivUp_monotone_left` |
| Commutativity | `mulDivDown_comm`, `mulDivUp_comm` | `wMulDown_comm` |
| Positivity | `mulDivDown_pos`, `mulDivUp_pos` | `wMulDown_pos`, `wDivUp_pos` |
| Zero collapse | `mulDivDown_zero_left/right`, `mulDivUp_zero_left/right` | `wMulDown_zero_left/right`, `wDivUp_zero` |
| Cancellation / identity | `mulDivDown_cancel_right/left`, `mulDivUp_cancel_right/left` | `wMulDown_one_left/right`, `wDivUp_by_wad` |
| Antitonicity (divisor) | `mulDivDown_antitone_divisor`, `mulDivUp_antitone_divisor` | `wDivUp_antitone_right` |
| Rounding gap (ceil vs floor) | `mulDivUp_le_mulDivDown_add_one`, `mulDivUp_eq_mulDivDown_or_succ` | — |
| Divisibility exactness | `mulDivUp_eq_mulDivDown_of_dvd`, `mulDivUp_eq_mulDivDown_add_one_of_not_dvd` | — |
| Floor sandwich bounds | `mulDivDown_mul_le`, `mulDivDown_mul_lt_add` | `wMulDown_mul_le`, `wMulDown_mul_lt_add` |
| Ceil sandwich bounds | `mulDivUp_mul_ge`, `mulDivUp_mul_lt_add` | `wDivUp_mul_ge`, `wDivUp_mul_lt_add` |

The sandwich bounds are especially useful for AMM reserve/share proofs.

**Example**: See `Contracts/SafeCounter/SafeCounter.lean` and `Contracts/SafeCounter/Proofs/Basic.lean` for a contract using checked arithmetic with proven overflow/underflow behavior.

## Backend Profiles and Arithmetic

All backend profiles (`--backend-profile semantic`, `solidity-parity-ordering`, `solidity-parity`) use **identical wrapping arithmetic semantics**. Profiles differ only in Yul output-shape normalization:

- **`semantic`** (default): canonical output order
- **`solidity-parity-ordering`**: dispatch `case` blocks sorted by selector
- **`solidity-parity`**: selector sorting + deterministic patch pass

The arithmetic model is invariant across profiles. See [`docs/SOLIDITY_PARITY_PROFILE.md`](SOLIDITY_PARITY_PROFILE.md) for profile details.

## What Is NOT Proved

- **Gas semantics**: proofs establish result correctness, not gas cost or bounded liveness.
- **Compiler-layer overflow detection**: the compiler does not insert overflow checks. Use EDSL `safeAdd`/`safeSub`/`safeMul` for checked behavior.
- **Cryptographic primitives**: keccak256 is axiomatized (see [`AXIOMS.md`](../AXIOMS.md)).
- **Universal bridge equivalence**: 15/15 pure EVMYulLean-backed builtins have universal bridge lemmas.

## Auditor Checklist

1. Confirm that the contract's arithmetic assumptions match wrapping semantics.
2. If overflow protection is required, verify the contract uses `safeAdd`/`safeSub`/`safeMul`.
3. Check that `requireSomeUint` is used to revert on overflow/underflow.
4. Review `Compiler/Proofs/ArithmeticProfile.lean` for the formal wrapping proofs.
5. Confirm the backend profile does not affect arithmetic behavior (it doesn't).

## Related Documents

- [`TRUST_ASSUMPTIONS.md`](../TRUST_ASSUMPTIONS.md) — trust boundaries and semantic caveats
- [`AXIOMS.md`](../AXIOMS.md) — documented axioms (arithmetic is NOT an axiom)
- [`docs/SOLIDITY_PARITY_PROFILE.md`](SOLIDITY_PARITY_PROFILE.md) — backend profile specification
- [`Compiler/Proofs/ArithmeticProfile.lean`](../Compiler/Proofs/ArithmeticProfile.lean) — formal proofs
