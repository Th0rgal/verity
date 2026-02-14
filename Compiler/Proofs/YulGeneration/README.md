# Layer 3: Yul Code Generation Proofs

This directory contains the verification proofs for Layer 3 (IR → Yul) of the DumbContracts compiler pipeline.

## File Overview

### Production Files (Complete)

- **`Semantics.lean`** - Executable semantics for Yul execution
  - State model (variables, storage, mappings, memory, calldata)
  - Expression evaluation (arithmetic, selectors, storage access)
  - Statement execution with fuel-parametric recursion
  - Status: ✅ Complete

- **`Equivalence.lean`** - State alignment and result matching definitions
  - `statesAligned` - Defines when IR and Yul states correspond
  - `execResultsAligned` - Defines when execution results match
  - `resultsMatch` - Final result equivalence predicate
  - Status: ✅ Complete

- **`Preservation.lean`** - Main Layer 3 preservation theorem
  - Proves Yul codegen preserves IR semantics
  - **Status**: ✅ Proven (modulo `hbody` hypothesis)
  - **Blocker**: Requires statement-level equivalence proofs

- **`Codegen.lean`** - Yul code generation helper lemmas
  - Switch case generation and selector mapping
  - Status: ✅ Complete

- **`Lemmas.lean`** - General utility lemmas
  - Status: ✅ Complete

- **`SmokeTests.lean`** - Concrete examples demonstrating equivalence
  - Test harness for IR ↔ Yul alignment
  - Status: ✅ Complete

### Scaffolding Files (Work in Progress)

- **`StatementEquivalence.lean`** ⚠️ **SCAFFOLDING ONLY - DO NOT IMPORT**
  - Contains theorem stubs with `sorry` placeholders
  - Provides worked example (variable assignment)
  - Documents proof strategy for each statement type
  - **Purpose**: Guide contributors implementing Layer 3 proofs
  - **Status**: ⚪ Scaffolding (all theorems have `sorry`)
  - **Import Risk**: Would compromise verification soundness if imported into production

## Layer 3 Completion Status

### What's Proven ✅

1. Yul semantics correctly model execution
2. State alignment definitions capture IR ↔ Yul correspondence
3. Main preservation theorem structure (`yulCodegen_preserves_semantics`)
4. Function dispatch logic (selector matching, switch cases)

### What's Pending ⚪

**Critical Path**: Prove statement-level equivalence for 8 statement types:

| # | Statement Type | Difficulty | File |
|---|----------------|------------|------|
| 1 | Variable Assignment | Low | `StatementEquivalence.lean:70` |
| 2 | Storage Load | Low | `StatementEquivalence.lean:107` |
| 3 | Storage Store | Low | `StatementEquivalence.lean:127` |
| 4 | Mapping Load | Medium | `StatementEquivalence.lean:147` |
| 5 | Mapping Store | Medium | `StatementEquivalence.lean:167` |
| 6 | Conditional (if) | Medium-High | `StatementEquivalence.lean:187` |
| 7 | Return | Low | `StatementEquivalence.lean:218` |
| 8 | Revert | Low-Medium | `StatementEquivalence.lean:236` |
| 9 | Composition | High | `StatementEquivalence.lean:256` |

**Once complete**: Replace `hbody` hypothesis in `Preservation.lean` with actual proofs,
achieving end-to-end verification EDSL → Yul.

## Contributing

See [`docs/ROADMAP.md`](../../../docs/ROADMAP.md) for:
- Detailed roadmap and timeline
- Proof strategy for each statement type
- Getting started guide for contributors
- Alternative approaches if fuel-parametric method is too complex

### Quick Start

1. Read `StatementEquivalence.lean` header and worked example
2. Pick a low-difficulty theorem (e.g., `storageLoad_equiv`)
3. Study IR semantics in `Compiler/Proofs/IRGeneration/IRInterpreter.lean`
4. Study Yul semantics in `Semantics.lean`
5. Replace `sorry` with your proof
6. Add smoke tests to `SmokeTests.lean`
7. Submit PR with your proof

### ⚠️ Important Notes

- **Never import `StatementEquivalence.lean`** into other modules until all `sorry`s are replaced
- Each statement proof should be self-contained and independently reviewable
- Add tests to `SmokeTests.lean` for each proven statement type
- Update progress table in `docs/ROADMAP.md` when theorems are completed

## References

- **Roadmap**: `docs/ROADMAP.md` - Layer 3 section
- **Verification Status**: `docs/VERIFICATION_STATUS.md` - Overall project status
- **IR Semantics**: `Compiler/Proofs/IRGeneration/IRInterpreter.lean`
- **Main Proof Inventory**: `Compiler/Proofs/README.md`

---

**Last Updated**: 2026-02-14
**Layer 3 Status**: Semantics complete, statement proofs pending (0/9 complete)
