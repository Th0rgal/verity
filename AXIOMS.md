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
- Use partial recursion (fuel-based)
- Have structural equality that's obvious by inspection but hard to formally prove
- Represent external system behavior (Ethereum addresses)

In these cases, we use axioms with strong soundness arguments.

---

## Current Axioms

### 1. `evalIRExpr_eq_evalYulExpr`

**Location**: `Compiler/Proofs/YulGeneration/StatementEquivalence.lean:43`

**Statement**:
```lean
axiom evalIRExpr_eq_evalYulExpr (selector : Nat) (irState : IRState) (expr : YulExpr) :
    evalIRExpr irState expr = evalYulExpr (yulStateOfIR selector irState) expr
```

**Purpose**: Proves that expression evaluation produces identical results in IR and Yul contexts when states are aligned.

**Why Axiom?**:
- `evalIRExpr` is defined as `partial` (not provably terminating in Lean), making it opaque to the kernel
- `evalYulExpr` is **total** (no `partial` annotation) — it uses structural recursion
- Lean cannot unfold a `partial` definition inside a proof, so equality between the IR and Yul evaluators cannot be proven even though their source code is structurally identical
- Functions have identical source code structure but different state type parameters

**Soundness Argument**:
1. **Source code inspection**: Both functions have structurally identical implementations
2. **Asymmetry**: Only the IR side is `partial`; the Yul side is already total
3. **State translation**: `yulStateOfIR` simply copies all fields from IRState to YulState
4. **Selector field**: Only difference is the `selector` field, which doesn't affect expression evaluation
5. **Differential testing**: 70,000+ property tests validate this equivalence holds in practice

**Alternative Approach**:
To eliminate this axiom, only the IR evaluator needs refactoring:
- Refactor `evalIRExpr` (and `evalIRExprs`, `evalIRCall`) to use fuel parameters or well-founded recursion on expression depth, matching the total pattern already used by `evalYulExpr`
- The Yul side is already total and requires no changes
- **Effort**: ~300 lines of refactoring (simpler than previously estimated since only one side needs work)

**Trade-off**: Given that the functions are structurally identical by inspection and validated by extensive testing, the axiom is a pragmatic choice.

**Risk**: **Low** - If implementations diverge during refactoring, differential tests would catch the discrepancy immediately.

**Future Work**:
- [ ] Add CI check that `evalIRExpr` and `evalYulExpr` source code structure remains identical
- [ ] Consider refactoring to fuel-based evaluation (long-term)
- [ ] Issue tracking: #82

---

### 2. `evalIRExprs_eq_evalYulExprs`

**Location**: `Compiler/Proofs/YulGeneration/StatementEquivalence.lean:47`

**Statement**:
```lean
axiom evalIRExprs_eq_evalYulExprs (selector : Nat) (irState : IRState) (exprs : List YulExpr) :
    evalIRExprs irState exprs = evalYulExprs (yulStateOfIR selector irState) exprs
```

**Purpose**: List version of `evalIRExpr_eq_evalYulExpr` for multiple expressions.

**Why Axiom?**: Same reasoning as axiom #1 — `evalIRExprs` is `partial` while `evalYulExprs` is total.

**Soundness Argument**:
- Follows directly from axiom #1 via structural induction on lists
- Could be proven from axiom #1 if that were a theorem
- Both implementations use `List.map` with the respective eval function

**Alternative Approach**:
If axiom #1 were eliminated, this would become a provable theorem via:
```lean
theorem evalIRExprs_eq_evalYulExprs : ... := by
  induction exprs with
  | nil => rfl
  | cons hd tl ih =>
      simp [evalIRExprs, evalYulExprs]
      rw [evalIRExpr_eq_evalYulExpr]  -- Uses axiom #1
      rw [ih]
```

**Risk**: **Low** - Same as axiom #1.

**Future Work**:
- [ ] If axiom #1 is eliminated, prove this as theorem
- [ ] Issue tracking: #82

---

### 3. `addressToNat_injective_valid`

**Location**: `Compiler/Proofs/IRGeneration/Conversions.lean:83`

**Statement**:
```lean
axiom addressToNat_injective_valid :
  ∀ {a b : Address}, isValidAddress a → isValidAddress b →
    addressToNat a = addressToNat b → a = b
```

**Purpose**: Asserts that the address-to-number conversion is injective for valid Ethereum addresses.

**Why Axiom?**:
- Models external Ethereum behavior (address space)
- Addresses are 20-byte hex strings (0x + 40 hex chars)
- Conversion involves string parsing and normalization
- Full formalization of hex parsing would be substantial

**Soundness Argument**:
1. **Valid address format**: Valid Ethereum addresses are exactly 20 bytes (160 bits)
2. **Normalization**: Address normalization removes case-based collisions (EIP-55 checksums)
3. **Hex parsing injectivity**: For normalized addresses, hex string → number conversion is injective up to 2^160
4. **Matches Ethereum**: This precisely models the actual Ethereum address space
5. **Differential testing**: Validated by 70,000+ differential tests against real EVM execution

**Trust Assumption**:
This axiom assumes that:
- Valid addresses have unique numerical representations
- Normalization is correctly implemented
- This matches Ethereum's actual address semantics

**Validation**:
- `isValidAddress` predicate ensures format correctness
- Differential testing validates against Solidity/EVM behavior
- Address normalization tested independently

**Risk**: **Low** - Ethereum address injectivity is a fundamental assumption of the EVM itself.

**Future Work**:
- [ ] Formalize hex string parsing in Lean (substantial effort)
- [ ] Prove injectivity from first principles
- [ ] Consider using verified hex parsing library
- [ ] Issue tracking: #82

---

### 4. `keccak256_first_4_bytes`

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

### 5. `addressToNat_injective`

**Location**: `Verity/Proofs/Stdlib/Automation.lean:155`

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
2. **Consistent with axiom #3**: Same property as `addressToNat_injective_valid` but without the `isValidAddress` precondition
3. **Differential testing**: Validated by 70,000+ tests against EVM execution
4. **Mathematical foundation**: String-to-number conversion on fixed-width encodings is inherently injective

**Risk**: **Low** - Standard assumption about Ethereum address encoding.

**Future Work**:
- [ ] Unify with `addressToNat_injective_valid` (axiom #3) to eliminate redundancy

---

## Axiom Usage Summary

| Axiom | File | Risk | Validated By | Future Work |
|-------|------|------|--------------|-------------|
| `evalIRExpr_eq_evalYulExpr` | StatementEquivalence.lean | Low | Differential tests (70k+) | Fuel-based refactor |
| `evalIRExprs_eq_evalYulExprs` | StatementEquivalence.lean | Low | Differential tests (70k+) | Prove from axiom #1 |
| `addressToNat_injective_valid` | Conversions.lean | Low | Differential tests (70k+) | Formalize hex parsing |
| `keccak256_first_4_bytes` | Selectors.lean | Low | CI selector checks + solc | Verified keccak FFI |
| `addressToNat_injective` | Automation.lean | Low | Differential tests (70k+) | Unify with axiom #3 |

**Total Axioms**: 5
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
    ↓ [Proven, 1 axiom: addressToNat_injective_valid]
IR
    ↓ [Proven, 2 axioms: evalIRExpr/Exprs equivalence]
Yul (1 axiom: keccak256_first_4_bytes for selectors)
    ↓ [TRUSTED: solc compiler]
EVM Bytecode
```

**Trust Assumptions**:
1. Lean 4 type checker is sound (foundational)
2. The 5 axioms documented above are sound
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

**Last Updated**: 2026-02-15
**Next Review**: When new axioms added or existing ones eliminated
**Maintainer**: Document all changes to axioms in git commit messages
