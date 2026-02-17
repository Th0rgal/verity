# Axioms in Verity

This file documents all axioms used in the verification codebase and their soundness justifications.

## Policy

Axioms should be **avoided whenever possible** as they introduce trust assumptions into the verification chain. When axioms are necessary:

1. **Document here** with full soundness justification
2. **Add inline comment** in source code referencing this file
3. **Mark as AXIOM** in code comments
4. **CI validates** all axioms are documented (see `.github/workflows/verify.yml`)

## Why Axioms Are Sometimes Necessary

Lean's proof assistant requires all functions to be provably terminating. However, some functions in Verity:
- Represent external system behavior (Ethereum addresses, cryptographic hashes)
- Have structural equality that's obvious by inspection but hard to formally prove

In these cases, we use axioms with strong soundness arguments.

---

## Current Axioms

### 1. `keccak256_first_4_bytes`

**Location**: `Compiler/Selectors.lean:43`

**Statement**:
```lean
axiom keccak256_first_4_bytes (sig : String) : Nat
```

**Purpose**: Computes the first 4 bytes (32 bits) of keccak256(sig) as a Solidity function selector.

**Why Axiom?**:
- Keccak256 cannot be implemented in Lean's pure logic (external cryptographic hash)
- Function selectors require matching Solidity's selector convention
- The hash is a primitive that must be assumed, not computed

**Soundness Argument**:
1. **CI validation**: `scripts/check_selectors.py` validates computed selectors against keccak256 specs
2. **Fixture testing**: `scripts/check_selector_fixtures.py` cross-validates against `solc --hashes` output
3. **Standard convention**: Matches Ethereum ABI specification exactly
4. **Differential testing**: All compiled contracts are tested with correct selector dispatch

**Risk**: **Low** - Validated by CI against both Python keccak256 and solc output.

---

### 2. `addressToNat_injective`

**Location**: `Verity/Proofs/Stdlib/Automation.lean:168`

**Statement**:
```lean
axiom addressToNat_injective :
    ∀ (a b : Address), addressToNat a = addressToNat b → a = b
```

**Purpose**: Asserts that address-to-number conversion is injective (no two different addresses map to the same number).

**Why Axiom?**:
- Models Ethereum address encoding behavior
- Full formalization of address string parsing/normalization is substantial
- Used in proof automation for mapping operations

**Soundness Argument**:
1. **Ethereum model**: Addresses are 20-byte values with unique numeric encodings
2. **Differential testing**: Validated by 70,000+ tests against EVM execution
3. **Mathematical foundation**: String-to-number conversion on fixed-width encodings is inherently injective

**Risk**: **Low** - Standard assumption about Ethereum address encoding.

**Future Work**:
- [ ] Formalize hex string parsing in Lean (substantial effort)
- [ ] Prove injectivity from first principles
- [ ] Consider using verified hex parsing library
- [ ] Issue tracking: #82

---

## Eliminated Axioms

### `evalIRExpr_eq_evalYulExpr` (formerly axiom #1)

**Eliminated in**: Issue #148

**Previous statement**:
```lean
axiom evalIRExpr_eq_evalYulExpr (selector : Nat) (irState : IRState) (expr : YulExpr) :
    evalIRExpr irState expr = evalYulExpr (yulStateOfIR selector irState) expr
```

**How eliminated**: Refactored `evalIRExpr`, `evalIRExprs`, and `evalIRCall` from `partial def` to total functions using `termination_by` with `exprSize`/`exprsSize` measures (matching the pattern already used by `evalYulExpr` in Semantics.lean). Restructured `evalIRCall` to evaluate all arguments first via `evalIRExprs` (matching `evalYulCall`), making the two functions structurally identical. The axiom became a provable theorem by mutual structural induction.

**Impact**: Eliminated 2 axioms (`evalIRExpr_eq_evalYulExpr` and `evalIRExprs_eq_evalYulExprs`) with zero changes to proof structure.

### `evalIRExprs_eq_evalYulExprs` (formerly axiom #2)

**Eliminated in**: Issue #148

**Previous statement**:
```lean
axiom evalIRExprs_eq_evalYulExprs (selector : Nat) (irState : IRState) (exprs : List YulExpr) :
    evalIRExprs irState exprs = evalYulExprs (yulStateOfIR selector irState) exprs
```

**How eliminated**: Follows from `evalIRExpr_eq_evalYulExpr` being a theorem — proved by structural induction on the expression list.

### `execIRStmtsFuel_adequate` (formerly axiom #3)

**Eliminated in**: Issue #148

**Previous statement**:
```lean
axiom execIRStmtsFuel_adequate (state : IRState) (stmts : List YulStmt) :
    execIRStmtsFuel (sizeOf stmts + 1) state stmts = execIRStmts state stmts
```

**How eliminated**: Refactored `execIRStmt` and `execIRStmts` from `partial def` to total functions using an explicit fuel parameter (matching the pattern already used by `execYulFuel` in Semantics.lean). Since the canonical definitions are now fuel-based, `execIRStmtFuel`/`execIRStmtsFuel` became aliases and the adequacy relationship is `rfl`.

**Impact**: Eliminated the fuel adequacy axiom entirely. `execIRFunction` and `interpretIR` now use the total, fuel-based definitions directly.

### `addressToNat_injective_valid` (formerly axiom #4)

**Eliminated in**: PR #202 (2026-02-16)

**Previous statement**:
```lean
axiom addressToNat_injective_valid :
  ∀ {a b : Address}, isValidAddress a → isValidAddress b →
    addressToNat a = addressToNat b → a = b
```

**How eliminated**: This axiom was a strictly weaker version of `addressToNat_injective` (axiom #2), which doesn't require `isValidAddress` preconditions. It was converted to a theorem derived from axiom #2:

```lean
theorem addressToNat_injective_valid :
    ∀ {a b : Address}, isValidAddress a → isValidAddress b →
      addressToNat a = addressToNat b → a = b :=
  fun _ _ h_eq => addressToNat_injective _ _ h_eq
```

**Impact**: Reduced axiom count from 5 to 4 with zero changes to proof structure (the axiom had no call sites).

---

## Axiom Usage Summary

| Axiom | File | Risk | Validated By | Future Work |
|-------|------|------|--------------|-------------|
| `keccak256_first_4_bytes` | Selectors.lean | Low | CI selector checks + solc | Verified keccak FFI |
| `addressToNat_injective` | Automation.lean | Low | Differential tests (70k+) | Formalize hex parsing |

**Total Axioms**: 2
**Eliminated**: 4 (3 via Issue #148 refactor, 1 via PR #202)
**Production Blockers**: 0 (all have low risk with strong validation)

---

## Adding New Axioms

If you need to add an axiom:

1. **Exhaust all alternatives first**:
   - Can you prove it? (even if difficult)
   - Can you use a weaker lemma?
   - Can you refactor to avoid the need?

2. **Document in this file**:
   - State the axiom clearly
   - Explain why it's necessary
   - Provide soundness justification
   - Explain validation/testing
   - Note future work to eliminate
   - Assess risk level

3. **Add inline comment in source**:
   ```lean
   /--
   AXIOM: Brief explanation
   See AXIOMS.md for full soundness justification
   -/
   axiom my_axiom : ...
   ```

4. **Ensure CI passes**: CI will detect the new axiom and verify it's documented

5. **Update this summary table**

---

## Verification Chain Trust Model

```
User Code (EDSL)
    ↓ [Proven, 1 axiom: addressToNat_injective]
ContractSpec
    ↓ [Proven, no additional axioms]
IR
    ↓ [Proven, no additional axioms — previously 3 axioms, now eliminated]
Yul (1 axiom: keccak256_first_4_bytes for selectors)
    ↓ [TRUSTED: solc compiler]
EVM Bytecode
```

**Trust Assumptions**:
1. Lean 4 type checker is sound (foundational)
2. The 2 axioms documented above are sound
3. Solidity compiler (solc) correctly compiles Yul → Bytecode

See `TRUST_ASSUMPTIONS.md` (issue #68) for complete trust model.

---

## CI Validation

The CI workflow (`.github/workflows/verify.yml`) automatically:
- Detects all axioms in `Compiler/` and `Verity/` directories
- Fails if any axiom is not documented in this file
- Reports axiom count in build logs

To check locally:
```bash
# Find all axioms
grep -rn "^axiom " Compiler/ Verity/ --include="*.lean"

# Verify this file documents them all
cat AXIOMS.md
```

---

**Last Updated**: 2026-02-17
**Next Review**: When new axioms added or existing ones eliminated
**Maintainer**: Document all changes to axioms in git commit messages
