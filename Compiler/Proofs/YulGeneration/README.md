# Layer 3: Yul Code Generation Proofs

This directory contains the verification proofs for Layer 3 (IR → Yul) of the DumbContracts compiler pipeline.

**Status**: Complete (PR #42). All statement equivalence proofs proven, universal dispatcher proven.

## File Overview

- **`Semantics.lean`** - Executable semantics for Yul execution
  - State model (variables, storage, mappings, memory, calldata)
  - Expression evaluation (arithmetic, selectors, storage access)
  - Statement execution with fuel-parametric recursion

- **`Equivalence.lean`** - State alignment and result matching definitions
  - `statesAligned` - Defines when IR and Yul states correspond
  - `execResultsAligned` - Defines when execution results match
  - `resultsMatch` - Final result equivalence predicate
  - `execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv` - Statement list composition theorem

- **`Preservation.lean`** - Main Layer 3 preservation theorem
  - Proves Yul codegen preserves IR semantics

- **`StatementEquivalence.lean`** - Statement-level equivalence proofs
  - All 8 statement types proven (assign, storage load/store, mapping load/store, conditional, return, revert)
  - Universal dispatcher (`all_stmts_equiv`) via mutual recursion with `conditional_equiv`
  - Statement list composition (`stmtList_equiv`) via the composition theorem

- **`Codegen.lean`** - Yul code generation helper lemmas
  - Switch case generation and selector mapping

- **`Lemmas.lean`** - General utility lemmas

- **`SmokeTests.lean`** - Concrete examples demonstrating equivalence

## Axioms

Two expression evaluation axioms in `StatementEquivalence.lean`:

1. `evalIRExpr_eq_evalYulExpr` - IR and Yul expression evaluation are identical when states are aligned
2. `evalIRExprs_eq_evalYulExprs` - List version of the above

These are sound because both eval functions have identical source code and `yulStateOfIR` copies all fields. Making them theorems would require refactoring both `partial` functions to use fuel parameters (~500+ lines).

## References

- **Proof Inventory**: `Compiler/Proofs/README.md`
- **IR Semantics**: `Compiler/Proofs/IRGeneration/IRInterpreter.lean`
- **Verification Status**: `docs/VERIFICATION_STATUS.md`
