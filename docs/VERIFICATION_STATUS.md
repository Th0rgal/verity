# Verification Status

This document provides a comprehensive overview of the Verity verification architecture, current status, and remaining work.

## Overview

Verity implements a **three-layer verification stack** that proves smart contracts correct from specification to EVM bytecode:

```
User Contracts (EDSL)
    ↓ Layer 1: EDSL ≡ ContractSpec
ContractSpec (Human-Readable Specs)
    ↓ Layer 2: ContractSpec → IR
Intermediate Representation (IR)
    ↓ Layer 3: IR → Yul
Yul (EVM Assembly)
    ↓ (Trusted: solc compiler)
EVM Bytecode
```

## Unified AST (Issue #364) ✅ **COMPLETE** (all 7 contracts)

**Status**: All 7 compilable contracts migrated with equivalence proofs (27 theorems, zero `sorry`)

**What This Achieves**: A single deep embedding (`Verity.AST`) maps 1:1 to EDSL primitives. The denotation function (`Verity.Denote`) interprets AST → Contract monad such that `denote ast = edsl_fn` holds by `rfl` (definitional equality). For contracts with helper composition (e.g., `onlyOwner`), `bind_assoc` flattens nested binds before `rfl` closes the goal.

### Migrated Contracts

| Contract | Functions | Theorems | Proof Strategy | Location |
|----------|-----------|----------|----------------|----------|
| SimpleStorage | store, retrieve | 2 | `rfl` | `Verity/AST/SimpleStorage.lean` |
| Counter | increment, decrement, getCount | 3 | `rfl` | `Verity/AST/Counter.lean` |
| SafeCounter | increment, decrement, getCount | 3 | `rfl` | `Verity/AST/SafeCounter.lean` |
| Ledger | deposit, withdraw, transfer, getBalance | 4 | `rfl` | `Verity/AST/Ledger.lean` |
| Owned | constructor, transferOwnership, getOwner | 3 | `rfl` + `bind_assoc` | `Verity/AST/Owned.lean` |
| OwnedCounter | constructor, increment, decrement, getCount, getOwner, transferOwnership | 6 | `rfl` + `bind_assoc` | `Verity/AST/OwnedCounter.lean` |
| SimpleToken | constructor, mint, transfer, balanceOf, getTotalSupply, getOwner | 6 | `rfl` + `bind_assoc` | `Verity/AST/SimpleToken.lean` |

### Key Files

- `Verity/AST.lean` — Unified `Expr` / `Stmt` inductive types
- `Verity/Denote.lean` — AST → Contract monad denotation (monad laws in `Verity/Core.lean`)
- `Verity/AST/*.lean` — Per-contract AST definitions and equivalence proofs

## Layer 1: EDSL ≡ ContractSpec ✅ **COMPLETE**

**Status**: 8 contracts verified (7 with full spec proofs, 1 with inline proofs); CryptoHash is an unverified linker demo (0 specs)

**What This Layer Proves**: User-facing EDSL contracts satisfy their human-readable specifications.

### Verified Contracts

| Contract | Properties | Status | Location |
|----------|------------|--------|----------|
| SimpleStorage | 20 | ✅ Complete | `Verity/Proofs/SimpleStorage/` |
| Counter | 28 | ✅ Complete | `Verity/Proofs/Counter/` |
| SafeCounter | 25 | ✅ Complete | `Verity/Proofs/SafeCounter/` |
| Owned | 23 | ✅ Complete | `Verity/Proofs/Owned/` |
| OwnedCounter | 48 | ✅ Complete | `Verity/Proofs/OwnedCounter/` |
| Ledger | 33 | ✅ Complete | `Verity/Proofs/Ledger/` |
| SimpleToken | 61 | ✅ Complete | `Verity/Proofs/SimpleToken/` |
| CryptoHash | 0 | ⬜ No specs | `Verity/Examples/CryptoHash.lean` |
| ReentrancyExample | 4 | ✅ Complete | `Verity/Examples/ReentrancyExample.lean` |
| **Total** | **242** | **✅ 100%** | — |

> **Note**: Stdlib (136 internal proof-automation properties) is excluded from the Layer 1 contracts table above but included in overall coverage statistics (378 total properties).

### Example Property

```lean
-- Theorem: increment increases count by 1
theorem increment_adds_one (state : ContractState) :
    let finalState := (increment.run state).snd
    finalState.storage countSlot = state.storage countSlot + 1 := by
  unfold increment
  simp [getStorage, setStorage]
```

### Infrastructure

- **SpecInterpreter**: Executable semantics for ContractSpec language
- **Automation Library**: Proven helper lemmas (safe arithmetic, storage operations)
- **Proof Patterns**: Documented patterns for common verification tasks

## Layer 2: ContractSpec → IR ✅ **COMPLETE**

**Status**: All 7 compiled contracts have IR generation with preservation proofs

**What This Layer Proves**: Intermediate representation (IR) generation preserves ContractSpec semantics.

### IR Generation Proofs

| Contract | IR Functions | Preservation Theorems | Status |
|----------|--------------|----------------------|--------|
| SimpleStorage | 2 | ✅ Proven | Complete |
| Counter | 3 | ✅ Proven | Complete |
| SafeCounter | 3 | ✅ Proven | Complete |
| Owned | 3 | ✅ Proven | Complete |
| OwnedCounter | 5 | ✅ Proven | Complete |
| Ledger | 4 | ✅ Proven | Complete |
| SimpleToken | 6 | ✅ Proven | Complete |

### Example Preservation Theorem

```lean
theorem counter_ir_preserves_spec :
    ∀ contract tx state,
      interpretSpec counterSpec (stateToSpecStorage state) tx ≈
      interpretIR counterIR (txToIRTransaction tx) state
```

### Infrastructure

- **IRInterpreter**: Executable semantics for IR language
- **IR Codegen**: Automatic IR generation from ContractSpec
- **Preservation Proofs**: Automated tactics for spec → IR equivalence

## Layer 3: IR → Yul ✅ **COMPLETE**

**Status**: All statement-level equivalence proofs complete!

**What This Layer Proves**: Yul code generation preserves IR semantics.

### Current State

#### ✅ Complete Components

1. **Yul Semantics** (`Compiler/Proofs/YulGeneration/Semantics.lean`)
   - Executable semantics for Yul execution
   - State model: variables, storage, mappings, memory, calldata
   - Expression evaluation: arithmetic, selectors, storage access
   - Statement execution: assignments, conditionals, storage operations

2. **Preservation Theorem Structure** (`Compiler/Proofs/YulGeneration/Preservation.lean`)
   ```lean
   theorem yulCodegen_preserves_semantics
       (contract : IRContract) (tx : IRTransaction) (initialState : IRState)
       (hselector : tx.functionSelector < selectorModulus)
       (hbody : ∀ fn, fn ∈ contract.functions →
         resultsMatch
           (execIRFunction fn tx.args state)
           (interpretYulBody fn tx state)) :
       resultsMatch
         (interpretIR contract tx initialState)
         (interpretYulFromIR contract tx initialState)
   ```

   **Status**: Proven assuming `hbody` hypothesis

3. **Equivalence Scaffolding** (`Compiler/Proofs/YulGeneration/Equivalence.lean`)
   - State alignment definitions
   - Result matching predicates
   - Fuel-parametric execution models
   - Composition lemmas for statement sequences

4. **Smoke Tests** (`Compiler/Proofs/YulGeneration/SmokeTests.lean`)
   - Concrete examples demonstrating equivalence for specific cases
   - Test harness for IR ↔ Yul alignment

#### ✅ Statement-Level Equivalence

**Status**: All 8 statement types proven! (PR #42)

The universal statement dispatcher has been implemented with mutual recursion:

```lean
-- All statement types now proven
theorem all_stmts_equiv : ∀ selector fuel stmt irState yulState,
    execIRStmt_equiv_execYulStmt_goal selector fuel stmt irState yulState
      statesAligned selector irState yulState →
      execResultsAligned selector
        (execIRStmt irState stmt)
        (execYulStmtFuel fuel yulState stmt)
```

All 8 statement types (assign, storage load/store, mapping load/store, conditional, return, revert) plus the composition theorem are proven. See `Compiler/Proofs/YulGeneration/StatementEquivalence.lean` for details.

## Property Test Coverage 🎯 **NEAR COMPLETE**

**Status**: 58% coverage (220/378), 158 remaining exclusions all proof-only

### Current Coverage

- **Total Properties**: 378
- **Covered**: 220 (58%)
- **Excluded**: 158 (all proof-only)
- **Missing**: 0

### Coverage by Contract

| Contract | Coverage | Exclusions | Status |
|----------|----------|------------|--------|
| SafeCounter | 100% (25/25) | 0 | ✅ Complete |
| ReentrancyExample | 100% (4/4) | 0 | ✅ Complete |
| SimpleStorage | 95% (19/20) | 1 proof-only | ✅ Near-complete |
| Owned | 87% (20/23) | 3 proof-only | ✅ Near-complete |
| OwnedCounter | 92% (44/48) | 4 proof-only | ✅ Near-complete |
| SimpleToken | 85% (52/61) | 9 proof-only | ✅ High coverage |
| Counter | 82% (23/28) | 5 proof-only | ✅ High coverage |
| Ledger | 100% (33/33) | 0 | ✅ Complete |
| Stdlib | 0% (0/136) | 136 proof-only | — Internal |

### Exclusion Categories

**Proof-Only Properties (158 exclusions)**: Internal proof machinery that cannot be tested in Foundry
- Storage helpers: `setStorage_*`, `getStorage_*`, `setMapping_*`, `getMapping_*`
- Internal helpers: `isOwner_*` functions tested implicitly
- Low-level operations used only in proofs

> **Note**: Sum conservation properties (previously excluded as "modeling limitations") were resolved in PR #135 by testing with fixed address sets.

## Differential Testing ✅ **PRODUCTION READY**

**Status**: Scaled to 70,000+ tests (10,000 per contract × 7 contracts) with 8-shard parallelization

### Features

- **Test Generation**: Randomized inputs covering edge cases
- **IR Interpreter**: Reference implementation for differential testing
- **Yul Execution**: Compare against actual EVM execution via Foundry
- **CI Integration**: Runs on every PR with 8 parallel shards

### Coverage

- All 7 compiled contracts have comprehensive differential test suites
- Property tests extracted from theorems provide additional coverage
- Edge cases: overflow, underflow, zero values, max values, access control

## Trust Assumptions

### Trusted Components (Outside Lean Verification)

1. **`solc` Yul Compiler**: Trusted to compile Yul → EVM bytecode correctly
   - Mitigation: CI compiles generated Yul as sanity check
   - Future: Yul ↔ EVM bridge verification

2. **EVM Semantics**: Assumed to match specification used in proofs
   - Mitigation: Differential testing against actual EVM execution
   - Future: Formal EVM semantics integration

3. ~~**Function Selectors**~~: Resolved — keccak256 axiom validated by CI against `solc --hashes` (PR #43, #46)

### Verified Components (Zero Trust)

1. **EDSL → ContractSpec**: Proven correct in Lean (Layer 1)
2. **ContractSpec → IR**: Proven correct in Lean (Layer 2)
3. **IR Interpreter**: Used for differential testing, verified against specs
4. **Property Tests**: Extracted from proven theorems, tested in Foundry

## Roadmap to Full Verification

### ✅ Completed Milestones

- [x] Complete Layer 3 statement-level equivalence proofs (PR #42)
- [x] Function selector axiom with CI validation (PR #43, #46)
- [x] External function linking for cryptographic libraries (PR #49)

### Short Term (1-2 months)

- [x] Add finite address set modeling for Ledger sum properties (Issue #39, closed)
- [x] Complete Ledger sum property proofs — 0 `sorry` remaining, proven in Conservation.lean (Issue #65)

### Medium Term (3-6 months)

- [ ] Yul → EVM bridge verification (or integrate existing EVM semantics)
- [ ] Add 2-3 more realistic example contracts (ERC721, governance, etc.)

### Long Term (6-12 months)

- [ ] Integration with production smart contract ecosystems
- [ ] Automated property extraction from natural language specs
- [ ] IDE integration for interactive proof development

## Contributing

See `Compiler/Proofs/README.md` for:
- Proof patterns and examples
- Common tactics
- Infrastructure components
- Testing and validation

See `scripts/README.md` for:
- Property test coverage scripts
- Differential testing setup
- CI integration

## References

- **Main README**: `README.md`
- **Compiler Proofs**: `Compiler/Proofs/README.md`
- **Property Scripts**: `scripts/README.md`
- **Research Documentation**: `docs-site/content/research.mdx`
- **GitHub Repository**: https://github.com/Th0rgal/verity

---

**Last Updated**: 2026-02-18
**Status Summary**: Layers 1-3 complete, trust reduction in progress, unified AST complete — all 7 contracts migrated (Issue #364)
