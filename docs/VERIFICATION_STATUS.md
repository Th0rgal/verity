# Verification Status

This document provides a comprehensive overview of the DumbContracts verification architecture, current status, and remaining work.

## Overview

DumbContracts implements a **three-layer verification stack** that proves smart contracts correct from specification to EVM bytecode:

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

## Layer 1: EDSL ≡ ContractSpec ✅ **COMPLETE**

**Status**: All 7 contracts fully verified

**What This Layer Proves**: User-facing EDSL contracts satisfy their human-readable specifications.

### Verified Contracts

| Contract | Properties | Status | Location |
|----------|------------|--------|----------|
| SimpleStorage | 20 | ✅ Complete | `DumbContracts/Specs/SimpleStorage/Proofs.lean` |
| Counter | 28 | ✅ Complete | `DumbContracts/Specs/Counter/Proofs.lean` |
| SafeCounter | 25 | ✅ Complete | `DumbContracts/Specs/SafeCounter/Proofs.lean` |
| Owned | 22 | ✅ Complete | `DumbContracts/Specs/Owned/Proofs.lean` |
| OwnedCounter | 45 | ✅ Complete | `DumbContracts/Specs/OwnedCounter/Proofs.lean` |
| Ledger | 32 | ✅ Complete | `DumbContracts/Specs/Ledger/Proofs.lean` |
| SimpleToken | 56 | ✅ Complete | `DumbContracts/Specs/SimpleToken/Proofs.lean` |
| **Total** | **228** | **✅ 100%** | — |

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

**Status**: All 7 contracts have IR generation with preservation proofs

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

## Layer 3: IR → Yul 🔄 **IN PROGRESS**

**Status**: Semantics and scaffolding complete, statement-level equivalence pending

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

#### 🔄 Pending Work

**Main Blocker**: Proving statement-level equivalence

```lean
-- Required to complete Layer 3
theorem stmt_equiv :
    ∀ selector fuel stmt irState yulState,
      statesAligned selector irState yulState →
      execResultsAligned selector
        (execIRStmt irState stmt)
        (execYulStmtFuel fuel yulState stmt)
```

**What This Requires**: For each IR/Yul statement type, prove that executing it in IR matches executing it in Yul when states are aligned.

**Statement Types to Prove**:
- Variable assignments
- Storage loads/stores
- Mapping loads/stores
- Arithmetic operations
- Conditionals (if/switch)
- Return statements
- Revert statements

**Why It's Blocked**: The proof requires careful handling of fuel consumption in recursive statement execution. The current fuel-parametric approach needs statement-level lemmas that compose correctly.

### Concrete Next Steps for Layer 3

1. **Prove Variable Assignment Equivalence**
   ```lean
   theorem exec_assign_equiv (selector : Nat) (fuel : Nat) :
       ∀ irState yulState var value,
         statesAligned selector irState yulState →
         execResultsAligned selector
           (execIRStmt irState (assign var value))
           (execYulStmtFuel fuel yulState (assign var value))
   ```

2. **Prove Storage Operation Equivalence**
   - `storageLoad` equivalence
   - `storageStore` equivalence
   - `mappingLoad` equivalence
   - `mappingStore` equivalence

3. **Prove Control Flow Equivalence**
   - Conditional (`if`) equivalence
   - Switch statement equivalence

4. **Prove Termination Equivalence**
   - `return` statement equivalence
   - `revert` statement equivalence

5. **Compose Statement Lemmas**
   Once all statement types are proven, use the composition theorem:
   ```lean
   theorem execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv
   ```
   to lift to full function body equivalence.

### Alternative Approaches

If fuel-parametric approach proves too complex:

1. **Well-Founded Recursion**: Replace fuel with well-founded recursion on statement structure
2. **Defunctionalization**: Convert to continuation-passing style
3. **Shallow Embedding**: Use Lean's built-in termination checking more directly

## Property Test Coverage 🎯 **NEAR COMPLETE**

**Status**: 63% coverage (after pending PRs), 89 remaining exclusions all proof-only

### Current Coverage (Main Branch)

- **Total Properties**: 292
- **Covered**: 155 (53.1%)
- **Excluded**: 137 (proof-only)
- **Missing**: 0

### After Pending PRs (#20, #21)

- **Total Properties**: 292
- **Covered**: 185 (63.4%)
- **Excluded**: 89 (all proof-only)
- **Missing**: 0

### Coverage by Contract

| Contract | Coverage | Exclusions | Status |
|----------|----------|------------|--------|
| SafeCounter | 100% (25/25) | 0 | ✅ Complete |
| SimpleStorage | 95% (19/20) | 1 proof-only | ✅ Near-complete |
| Owned | 91% (20/22) | 2 proof-only | ✅ Near-complete |
| OwnedCounter | 98% (44/45) | 1 proof-only | ✅ Near-complete |
| SimpleToken | 84% (47/56) | 9 proof-only | ✅ High coverage |
| Counter | 82% (23/28) | 5 proof-only | ✅ High coverage |
| Ledger | 78% (25/32) | 7 modeling limit | ⚠️ Limited |
| Stdlib | 0% (0/64) | 64 proof-only | — Internal |

### Exclusion Categories

**Proof-Only Properties (82 exclusions)**: Internal proof machinery that cannot be tested in Foundry
- Storage helpers: `setStorage_*`, `getStorage_*`, `setMapping_*`, `getMapping_*`
- Internal helpers: `isOwner_*` functions tested implicitly
- Low-level operations used only in proofs

**Modeling Limitations (7 exclusions)**: Properties requiring features not yet modeled
- Sum equations: Require finite address set modeling (e.g., total supply invariants)
- Currently affects Ledger contract

## Differential Testing ✅ **PRODUCTION READY**

**Status**: Scaled to 10,000+ tests with 8-shard parallelization

### Features

- **Test Generation**: Randomized inputs covering edge cases
- **IR Interpreter**: Reference implementation for differential testing
- **Yul Execution**: Compare against actual EVM execution via Foundry
- **CI Integration**: Runs on every PR with 8 parallel shards

### Coverage

- All 7 contracts have comprehensive differential test suites
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

3. **Function Selectors**: Precomputed keccak256 hashes assumed correct
   - Mitigation: CI verifies selector hashes against `solc --hashes`
   - Future: Selector hash proofs in Lean

### Verified Components (Zero Trust)

1. **EDSL → ContractSpec**: Proven correct in Lean (Layer 1)
2. **ContractSpec → IR**: Proven correct in Lean (Layer 2)
3. **IR Interpreter**: Used for differential testing, verified against specs
4. **Property Tests**: Extracted from proven theorems, tested in Foundry

## Roadmap to Full Verification

### Short Term (1-2 months)

- [ ] Complete Layer 3 statement-level equivalence proofs
- [ ] Merge property extraction PRs (#20, #21, #22)
- [ ] Add finite address set modeling for Ledger sum properties

### Medium Term (3-6 months)

- [ ] Selector hash proofs in Lean
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
- **GitHub Repository**: https://github.com/Th0rgal/dumbcontracts

---

**Last Updated**: 2026-02-14
**Status Summary**: Layers 1-2 complete, Layer 3 semantics ready, property extraction near-complete
