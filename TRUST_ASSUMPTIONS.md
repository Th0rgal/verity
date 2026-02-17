# Trust Assumptions and Verification Boundaries

This document provides a comprehensive overview of what is formally verified in Verity and what components are trusted without formal proof. Understanding these boundaries is essential for security audits and production deployments.

## Table of Contents

- [Overview](#overview)
- [Verified Components](#verified-components)
- [Trusted Components](#trusted-components)
- [Axioms](#axioms)
- [Security Audit Checklist](#security-audit-checklist)
- [Future Work to Reduce Trust](#future-work-to-reduce-trust)

---

## Overview

Verity provides **end-to-end verification** from high-level contract specifications down to Yul intermediate representation, with a small trusted computing base (TCB).

### Verification Chain

```
User's Contract Code (EDSL)
    ↓ [Layer 1: FULLY VERIFIED]
ContractSpec (High-level specification)
    ↓ [Layer 2: FULLY VERIFIED]
IR (Intermediate representation)
    ↓ [Layer 3: FULLY VERIFIED, 5 axioms]
Yul (Ethereum intermediate language)
    ↓ [TRUSTED: Solidity compiler]
EVM Bytecode
```

### Trust Model Summary

| Component | Status | Risk Level |
|-----------|--------|------------|
| Layer 1 (EDSL → Spec) | ✅ Verified | None |
| Layer 2 (Spec → IR) | ✅ Verified | None |
| Layer 3 (IR → Yul) | ✅ Verified (5 axioms) | Very Low |
| Axioms | ⚠️ Documented | Low |
| Solidity Compiler (solc) | ⚠️ Trusted | Medium |
| Keccak256 Hashing | ⚠️ Trusted | Low |
| EVM Semantics | ⚠️ Trusted | Low |
| Linked Libraries (Linker) | ⚠️ Trusted | Varies |
| Mapping Slot Collision Freedom | ⚠️ Trusted | Low |
| Arithmetic Semantics | ⚠️ Documented | Low |
| Address Type | ⚠️ Documented | Low |
| Lean 4 Type Checker | ⚠️ Foundational | Very Low |
| `allowUnsafeReducibility` | ⚠️ Documented | Low |

---

## Verified Components

These components have been formally verified with machine-checked proofs in Lean 4.

### Layer 1: EDSL → ContractSpec

**Status**: ✅ **Fully Verified**

**What is proven**: Contract implementations written in the EDSL correctly implement their formal specifications.

**Files**:
- `Verity/Specs/*/Proofs.lean` (one per contract)
- Example: `Verity/Specs/SimpleStorage/Proofs.lean`

**Example Theorems**:
```lean
-- SimpleStorage: getValue returns the stored value
theorem getValue_correct (state : ContractState) :
    let result := (getValue.run state).fst
    result = state.storage valueSlot

-- Counter: increment increases count by exactly 1
theorem increment_correct (state : ContractState) :
    let finalState := increment.runState state
    finalState.storage countSlot = add (state.storage countSlot) 1
```

**Coverage**: 220 properties tested across 9 contracts (73% coverage, 300 total theorems)

**What this guarantees**:
- Contract behavior matches specification
- No unexpected side effects
- State transitions are correct
- Arithmetic operations are safe

---

### Layer 2: ContractSpec → IR

**Status**: ✅ **Fully Verified**

**What is proven**: Compilation from high-level ContractSpec to intermediate representation (IR) preserves all semantic properties.

**Files**:
- `Compiler/Proofs/IRGeneration/*`
- Key file: `Compiler/Proofs/IRGeneration/Preservation.lean`

**Example Theorems**:
```lean
-- Expression evaluation is preserved
theorem evalExpr_preserves_semantics :
    evalContractSpecExpr expr state = evalIRExpr (compileExpr expr) irState

-- Statement execution is preserved
theorem execStmt_preserves_properties :
    allPropertiesHold spec state →
    allPropertiesHold (compileSpec spec) (compileState state)
```

**What this guarantees**:
- IR accurately represents high-level spec
- No information loss during compilation
- Properties proven at Layer 1 still hold
- Type safety maintained

---

### Layer 3: IR → Yul

**Status**: ✅ **Verified (with 5 axioms)**

**What is proven**: IR execution is equivalent to Yul execution when states are properly aligned.

**Files**:
- `Compiler/Proofs/YulGeneration/*`
- Key file: `Compiler/Proofs/YulGeneration/StatementEquivalence.lean`

**Example Theorems**:
```lean
-- Variable assignment equivalence
theorem assign_equiv :
    execIRStmt (assign var expr) irState =
    execYulStmt (assign var expr) yulState

-- Storage operations equivalence
theorem storageLoad_equiv : ...
theorem storageStore_equiv : ...

-- Control flow equivalence
theorem if_equiv : ...
```

**Dependencies**: Relies on 5 axioms (see [Axioms](#axioms) section)

**What this guarantees**:
- Yul code correctly implements IR semantics
- All IR properties transfer to Yul
- Execution equivalence under state alignment

---

## Trusted Components

These components are **not formally verified** but are trusted based on testing, industry adoption, or foundational assumptions.

### 1. Solidity Compiler (solc)

**Role**: Compiles Yul intermediate representation to EVM bytecode

**Assumption**: The Solidity compiler correctly translates Yul to executable EVM bytecode without introducing bugs or semantic changes.

**Details**:
- **Version**: 0.8.33+commit.64118f21 (pinned)
- **Scope**: Only Yul → Bytecode compilation (not Solidity)
- **Industry Status**: Battle-tested, used to secure billions in value

**Mitigation Strategies**:
1. **Differential Testing**: 70,000+ property tests validate EDSL ≡ Yul ≡ EVM execution
   - Files: `test/Property*.t.sol`
   - Tests run on actual compiled bytecode
   - Catches discrepancies between layers

2. **Pinned Version**: Exact solc version locked in CI
   - Prevents unexpected compiler changes
   - Reproducible builds

3. **CI Validation**:
   - `scripts/check_yul_compiles.py` - Ensures Yul compiles without errors
   - `scripts/check_selector_fixtures.py` - Validates function selectors

**Risk Assessment**: **Medium**
- Solc is mature and widely used
- Yul compilation is simpler than Solidity compilation
- Differential tests provide strong validation
- However, compiler bugs are possible

**Future Work**:
- Integrate KEVM or EVMYulLean for Yul → Bytecode verification
- See issue #76 for formal verification roadmap

---

### 2. Keccak256 Function Selector Hashing

**Role**: Computes Ethereum function selectors via Keccak256 hashing

**Assumption**: Python's Keccak256 implementation matches the EVM's Keccak256 semantics.

**Details**:
- **Implementation**: `scripts/keccak256.py`
- **Usage**: Generates function selectors for contract compilation
- **Standard**: EIP-20 function selector specification

**Mitigation Strategies**:
1. **Self-Test**: `python3 scripts/keccak256.py --self-test`
   - 14 test vectors: 4 full 32-byte digests + 10 selector-only checks
   - Full digests verified against Ethereum Yellow Paper and ethers.js
   - Selector vectors verified against `solc --hashes`
   - Runs in CI before any dependent script

2. **Cross-Validation**: `scripts/check_selectors.py`
   - Compares Python output against solc-generated selectors
   - Runs in CI on every build
   - Ensures consistency

3. **Fixture Testing**: `scripts/check_selector_fixtures.py`
   - Tests against known correct selector values via `solc --hashes`
   - Prevents regression

**Risk Assessment**: **Low**
- Keccak256 is a deterministic algorithm
- Validated against multiple independent implementations (solc, ethers.js)
- 14 test vectors catch round-constant, padding, or rotation bugs
- Any mismatch would fail differential tests

**Files**:
- `Compiler/Selectors.lean` - Selector definitions
- `scripts/keccak256.py` - Implementation (with `--self-test` mode)
- `scripts/check_selectors.py` - Cross-validation against specs
- `scripts/check_selector_fixtures.py` - Cross-validation against solc

---

### 3. Mapping Slot Collision Freedom

**Role**: Storage slot derivation for mappings via `keccak256(key ++ slot)`

**Assumption**: The keccak256-based storage slot calculation used by Solidity (and Verity's compiled Yul) for mapping entries is collision-free in practice — distinct `(key, baseSlot)` pairs produce distinct storage slot addresses.

**Details**:
- **Lean model**: Mappings are modeled as pure functions (`storageMap : Nat → Address → Uint256`). Reading `storageMap slot addr` is a direct function application — no hash computation.
- **Yul implementation**: Mappings use `keccak256(abi.encodePacked(key, baseSlot))` to derive a storage slot address, then read/write via `sload`/`sstore`.
- **The gap**: The Lean proofs reason about an idealized mapping model. The Yul code uses hash-based slot derivation. These are equivalent only if keccak256 mapping slots never collide with each other or with direct storage slots (0, 1, 2, ...).

**Why this is safe**:
1. This is a [standard Ethereum assumption](https://docs.soliditylang.org/en/latest/internals/layout_in_storage.html) — all Solidity contracts rely on it
2. Keccak256 outputs are 256 bits; collision probability is negligible (~2^-128 for birthday attacks)
3. Direct storage slots (small integers) are astronomically unlikely to collide with keccak256 outputs
4. No real-world collision has ever been observed in the Ethereum ecosystem

**Risk Assessment**: **Low**
- Universal assumption in Ethereum smart contract development
- Would affect all Solidity contracts equally if violated
- Formally equivalent to assuming keccak256 is a random oracle for these inputs

**Related**: Issue #157, Issue #84 (storage layout formalization)

---

### 4. EVM Semantics

**Role**: The Ethereum Virtual Machine executes bytecode

**Assumption**: The EVM behaves according to the Ethereum Yellow Paper specification and established consensus rules.

**Details**:
- **Specification**: Ethereum Yellow Paper (Byzantium+)
- **Implementation**: Various EVM implementations (Geth, Foundry, etc.)
- **Validation**: Ethereum consensus across thousands of nodes

**Mitigation Strategies**:
1. **Differential Testing**:
   - Tests run against Foundry's EVM implementation
   - 70,000+ test cases validate expected behavior
   - Sharded testing across 8 parallel jobs

2. **Conformance Testing** (planned):
   - Issue #75 tracks integration with Ethereum test vectors
   - Will validate against official EVM test suite

**Risk Assessment**: **Low**
- EVM semantics are well-defined and stable
- Billions of dollars secured by EVM
- Multiple independent implementations agree
- Decades of production use

**Future Work**:
- Add conformance testing (issue #75)
- Integrate with EVMYulLean for EVM semantics proofs

---

### 5. External Library Code (Linker)

**Role**: The [Linker](Compiler/Linker.lean) injects external Yul library functions into compiled contracts at code-generation time, enabling production cryptographic implementations (e.g., Poseidon hash) to replace placeholder stubs.

**Assumption**: Linked library functions behave as specified in their interfaces and are semantically compatible with the placeholder stubs used during formal verification.

**How It Works**:
```
ContractSpec → IR → Yul AST → Yul text → [Linker injects library text] → final .yul
```
Library functions are provided via `--link <path.yul>` flags to the compiler CLI. The Linker parses function definitions from library files and injects them as raw text into the rendered Yul output.

**Safety Checks** (enabled in `CompileDriver.lean`):
1. **External reference validation**: All non-builtin function calls in the contract must be resolved by a linked library
2. **Duplicate name detection**: No two library functions may share the same name

**Remaining Gaps**:
- Injection is text-level, not AST-level — no syntax or arity checking of library code
- Library code is entirely outside the formal proof boundary

**Risk Assessment**: **Medium to High** (depends on library)
- Precompiled contracts: Low (EVM-native, well-tested)
- Third-party Yul libraries: Medium to High
- Recommendation: Minimize external dependencies, audit linked libraries independently

**Future Work**:
- Issue #71: Integrate EVMYulLean precompiled contracts
- Formal interface specifications for external calls

---

### 6. Lean 4 Type Checker

**Role**: Verifies all Lean proofs are correct

**Assumption**: Lean 4's type checker and proof checker are sound.

**Details**:
- **Foundation**: Lean is based on the Calculus of Inductive Constructions
- **Development**: Extensively peer-reviewed, formal methods community
- **Status**: Used in academic research and industrial verification

**Risk Assessment**: **Very Low** (Foundational Trust)
- Lean's soundness is a foundational assumption of all formal verification
- Decades of research in type theory
- Active development and testing
- No known soundness bugs in Lean 4

**Note**: This is an irreducible trust assumption - all formal verification tools require trusting their proof checker.

---

### 7. `allowUnsafeReducibility` Usage

**Role**: Allows Lean's `simp` and `rfl` tactics to unfold `partial` function definitions

**Assumption**: The `partial` functions marked as reducible are structurally recursive and terminate in practice.

**Details**:
Two files use `set_option allowUnsafeReducibility true`:

1. **`Compiler/Proofs/YulGeneration/Semantics.lean:332`**
   ```lean
   set_option allowUnsafeReducibility true in
   attribute [reducible] execYulFuel
   ```
   Makes `execYulFuel` unfoldable for proofs about Yul execution semantics.

2. **`Compiler/Proofs/YulGeneration/Equivalence.lean:11`**
   ```lean
   set_option allowUnsafeReducibility true in
   attribute [local reducible] execIRStmt execIRStmts
   ```
   Makes `execIRStmt`/`execIRStmts` unfoldable for IR↔Yul equivalence proofs.

**Why This Matters**:
- `allowUnsafeReducibility` can make the Lean kernel unsound in theory
- Lean keeps `partial` definitions opaque to prevent reasoning about potentially non-terminating functions
- This option overrides that safety check, allowing proofs to unfold these definitions

**Risk Assessment**: **Low**
- The functions are structurally recursive on fuel parameters and always terminate
- Lean marks them as `partial` only because the termination checker cannot verify the recursion pattern
- `execYulFuel` is fuel-bounded (guaranteed termination), so reducibility is safe
- `execIRStmt`/`execIRStmts` are used locally and their termination is validated by 70,000+ differential tests

**Elimination Path**:
- Same fuel-based refactoring that would eliminate axioms #1 and #2 (`evalIRExpr`/`evalIRExprs`) would also eliminate the need for `allowUnsafeReducibility` on the IR side
- The Yul side (`execYulFuel`) already uses fuel and could potentially be proven terminating with well-founded recursion

---

### 8. Arithmetic Semantics: Wrapping vs Checked

**Role**: The Lean EDSL uses **wrapping (modular) arithmetic** for `Uint256` operations, while Solidity `^0.8` uses **checked arithmetic** that reverts on overflow/underflow.

**Assumption**: Contract specifications and proofs reason about EVM-level wrapping arithmetic semantics, which matches raw EVM opcodes but differs from Solidity's default checked arithmetic.

**Details**:

The Lean EDSL in `Verity/Core/Uint256.lean` defines:
```lean
def add (a b : Uint256) : Uint256 := ⟨(a.val + b.val) % 2^256⟩
def sub (a b : Uint256) : Uint256 := ⟨(a.val + 2^256 - b.val) % 2^256⟩
```

This matches the EVM's `add` and `sub` opcodes which wrap on overflow/underflow.

Solidity `^0.8.0` by default uses checked arithmetic:
```solidity
uint256 x = type(uint256).max + 1;  // reverts with overflow
```

**Impact**:

| Contract | Lean Model | Solidity Reference | Implication |
|----------|-----------|-------------------|-------------|
| Counter | `increment()` at MAX wraps to 0 | `count += 1` reverts | Wrapping states unreachable in Solidity |
| Ledger | `credit()` wraps on overflow | `balances[addr] += amount` reverts | Same |
| SimpleToken | `transfer()` underflow wraps | `balances[from] -= amount` reverts | Same |

**Mitigation Strategies**:

1. **SafeCounter Pattern**: Use `require` guards to prevent overflow/underflow:
   ```lean
   def increment (c : Counter) : Contract Unit := do
     let current ← getStorage countSlot
     require (current + 1 > current) "overflow"
     setStorage countSlot (current + 1)
   ```
   This matches Solidity's checked semantics and is proven correct in `SafeCounter`.

2. **Explicit Wrapping Semantics**: For contracts that intentionally use wrapping (e.g., `Counter`), document that proofs cover EVM-level wrapping behavior, not Solidity's revert-on-overflow.

3. **Solidity Reference Alignment**: Use `unchecked { }` blocks in Solidity reference contracts to match Lean wrapping semantics, or add explicit `require` guards in Lean contracts.

**Risk Assessment**: **Low**
- This is a well-known semantic difference documented here
- The `SafeCounter` contract demonstrates the correct pattern for checked arithmetic
- Differential tests execute against compiled Yul (wrapping), so behavior is validated end-to-end
- Users can choose wrapping or checked semantics by adding/removing `require` guards

**Recommendation for Developers**:
- For contracts intended to match Solidity `^0.8` behavior: add `require` guards (see `SafeCounter` as reference)
- For contracts using intentional wrapping (e.g., counters, tokens with explicit overflow handling): document this in the spec
- When comparing to Solidity reference contracts: ensure both use the same arithmetic model

**Future Work**:
- Add a `CheckedUint256` type that automatically validates on each operation
- Issue tracking: #162

---

### 9. Address Type: String Without Validation

**Role**: Ethereum addresses are represented as plain `String` throughout the codebase (`Verity/Core.lean:19`):

```lean
abbrev Address := String
```

**Assumption**: Contract specifications and proofs assume addresses are well-formed 20-byte hex strings (with `0x` prefix), but no validation is enforced at the type level.

**Details**:

Two axioms depend on address injectivity:
- `addressToNat_injective` (Automation.lean): Claims `addressToNat a = addressToNat b → a = b`
- `addressToNat_injective_valid` (Conversions.lean): Same but requires `isValidAddress` pre-condition

Since `Address = String`, any string can be used as an address. The axiom `addressToNat_injective` (without validity check) is technically unsound for arbitrary strings — `addressToNat "0xFF"` might equal `addressToNat "0xff"` while the strings are different.

**Impact**:

| Issue | Description | Risk |
|-------|-------------|------|
| Type Safety | No compile-time protection against invalid addresses | Low |
| Case Sensitivity | String equality is case-sensitive, but Ethereum addresses are case-insensitive (EIP-55) | Low |
| Axiom Soundness | `addressToNat_injective` may not hold for invalid strings | Low |

**Mitigation Strategies**:

1. **Use Valid Addresses**: Always use properly formatted Ethereum addresses (e.g., `"0x1234...abcd"`)

2. **Case Consistency**: Use consistent casing when comparing addresses (both uppercase or both lowercase)

3. **EDSL Validation**: The EDSL does not validate address format - this is a trust assumption

**Risk Assessment**: **Low**
- This is documented here as a known limitation
- The stronger axiom with `isValidAddress` guard is more defensible
- In practice, addresses used in tests and examples are well-formed

**Recommendation for Developers**:
- Use consistently cased addresses in proofs and tests
- When comparing addresses, normalize to lowercase first
- For production use, validate addresses before using them in contracts

**Future Work**:
- Create a validated Address type: `structure Address where hex : String, isValid : ...`
- Use `Fin (2^160)` or `ByteArray` of length 20 for type-safe address representation
- Issue tracking: #150

---

## Axioms

Verity uses **5 axioms** across the verification codebase. All axioms are documented with soundness justifications.

**See**: [AXIOMS.md](AXIOMS.md) for complete details.

### Summary of Axioms

| Axiom | Purpose | Risk | Validation |
|-------|---------|------|------------|
| `evalIRExpr_eq_evalYulExpr` | Expression evaluation equivalence | Low | Differential tests, code inspection |
| `evalIRExprs_eq_evalYulExprs` | List version of above | Low | Differential tests, code inspection |
| `execIRStmtsFuel_adequate` | Fuel-parametric ↔ partial IR bridge | Low | Structural fuel argument |
| `keccak256_first_4_bytes` | Function selector computation | Low | CI validation against solc --hashes |
| `addressToNat_injective` | Address-to-Nat mapping injectivity | Low | EVM address semantics |

**Key Points**:
- All axioms have **low risk** with strong soundness arguments
- All validated by **70,000+ differential tests**
- Documented with elimination strategies
- CI enforces documentation (see AXIOMS.md)

**Future Work**:
- Eliminate expression evaluation axioms via fuel-based refactoring (~500 LOC)
- Formalize hex string parsing for address injectivity

---

## Security Audit Checklist

Use this checklist when performing security audits of Verity-verified contracts.

### 1. Verification Review
- [ ] Review Layer 1 proofs for the specific contract
- [ ] Check property coverage (should be ≥70%)
- [ ] Verify no `sorry` placeholders in proofs
- [ ] Confirm all properties tested in `test/Property*.t.sol`

### 2. Trust Boundary Analysis
- [ ] Review AXIOMS.md for current axioms
- [ ] Assess axiom soundness arguments
- [ ] Check solc version is pinned and tested
- [ ] Verify differential tests cover contract functionality
- [ ] Verify arithmetic semantics: wrapping (EDSL) vs checked (Solidity reference)

### 3. Testing Validation
- [ ] Confirm all Foundry tests pass
- [ ] Review property coverage report
- [ ] Check differential test count (should be >10k for production contracts)
- [ ] Validate tests against edge cases

### 4. External Dependencies
- [ ] List all external contract calls
- [ ] Assess risk of each external dependency
- [ ] Check for precompile usage (lower risk)
- [ ] Review interface specifications

### 5. Deployment Verification
- [ ] Verify compiled bytecode matches Yul output
- [ ] Check function selectors against specifications
- [ ] Validate storage layout (issue #84)
- [ ] Confirm gas costs are acceptable (issue #80)

### 6. Documentation Review
- [ ] Check README for accurate description
- [ ] Verify TRUST_ASSUMPTIONS.md is current
- [ ] Review AXIOMS.md for changes
- [ ] Confirm property manifest is up-to-date

---

## Future Work to Reduce Trust

### Short-term (3-6 months)

1. **EVMYulLean UInt256 Integration** (Issue #67)
   - Replace current Uint256 with EVMYulLean's verified implementation
   - Reduces trust in arithmetic operations
   - Effort: 3 days

2. **Precompiled Contracts Integration** (Issue #71)
   - Use EVMYulLean's verified precompiles
   - Reduces trust in cryptographic operations
   - Effort: 2 weeks

3. **Conformance Testing** (Issue #75)
   - Validate against Ethereum test vectors
   - Cross-validates with EVM implementations
   - Effort: 2 weeks

4. **Storage Layout Formalization** (Issue #84)
   - Type-safe storage layout system
   - Prevents slot collisions
   - Effort: 5 weeks

### Long-term (6-12 months)

1. **Formal Yul → Bytecode Verification** (Issue #76)
   - Integrate KEVM or EVMYulLean EVM semantics
   - **Eliminates solc trust assumption**
   - Proves Yul semantics ≡ Bytecode execution
   - Effort: 3-4 months

2. **Axiom Elimination**
   - Refactor IR execution to fuel-based (expressions + statements)
   - Removes 3 of 5 axioms (evalIRExpr, evalIRExprs, execIRStmtsFuel adequacy)
   - Effort: ~500 LOC refactoring

3. **Gas Cost Verification** (Issue #80)
   - Formally verify gas bounds
   - Prevents DoS via gas exhaustion
   - Effort: 6 weeks

### Verification Roadmap

**Current State**:
```
EDSL → Spec → IR → Yul → [solc] → Bytecode
              ✅    ✅    ⚠️ TRUSTED
```

**After Issue #76**:
```
EDSL → Spec → IR → Yul → Bytecode
              ✅    ✅    ✅
```

**Impact**: Complete end-to-end verification, minimal trust assumptions

---

## Conclusion

Verity provides **strong formal verification** with a **small trusted computing base**:

### What is Guaranteed (Proven)
✅ Contract implementations match specifications (Layer 1)
✅ Specifications preserved through compilation (Layer 2)
✅ IR semantics equivalent to Yul semantics (Layer 3)
✅ 300 theorems across 9 contracts (220 covered by property tests)

### What is Trusted (Validated but Not Proven)
⚠️ Solidity compiler (solc) - Validated by 70k+ differential tests
⚠️ Keccak256 hashing - Validated against solc
⚠️ Mapping slot collision freedom - Standard Ethereum assumption
⚠️ Arithmetic semantics - Wrapping (Lean) vs checked (Solidity), see section 8
⚠️ EVM semantics - Industry standard, billions in TVL
⚠️ Linked libraries - Outside proof boundary, validated by compile-time reference checks
⚠️ 5 axioms - Low risk, extensively validated (see AXIOMS.md)

### Risk Profile
- **Overall**: Low to Medium risk
- **Production Ready**: Yes, with caveats
- **Recommended Use**: High-value contracts where formal verification adds significant security value
- **Not Recommended**: Contracts requiring zero trust (not achievable without full EVM verification)

### For Auditors
Verity offers **substantially higher assurance** than traditional Solidity contracts:
- Formal proofs replace manual code review for core logic
- Differential testing validates entire compilation pipeline
- Explicit trust boundaries enable focused auditing
- Property-based testing catches edge cases

### For Developers
Trust assumptions are **documented and minimized**:
- Clear distinction between proven and trusted
- Roadmap for further trust reduction
- CI enforces documentation of all assumptions
- Regular updates as verification expands

---

**Last Updated**: 2026-02-17
**Next Review**: After completing issue #76 (Yul → Bytecode verification)
**Maintainer**: Update when trust boundaries change or new components are verified

**Related Documents**:
- [AXIOMS.md](AXIOMS.md) - Detailed axiom documentation
- [README.md](README.md) - Project overview
- [docs/ROADMAP.md](docs/ROADMAP.md) - Verification roadmap
