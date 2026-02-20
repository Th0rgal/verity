# Layer 3: Yul Code Generation Proofs

This directory contains the verification proofs for Layer 3 (IR → Yul) of the Verity compiler pipeline.

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
  - Statement list composition via `execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv` in Equivalence.lean

- **`Codegen.lean`** - Yul code generation helper lemmas
  - Switch case generation and selector mapping

- **`Lemmas.lean`** - General utility lemmas

- **`SmokeTests.lean`** - Concrete examples demonstrating equivalence
- **`PatchRulesProofs.lean`** - Proof hooks for deterministic Yul patch rules
  - Defines `ExprPatchPreservesUnder` backend-agnostic proof contract for patch correctness
  - Registers evaluator-law proof obligations for the initial foundation patch pack (`or(x,0)`, `or(0,x)`, `xor(x,0)`)

## Expression Equivalence Theorems

Two expression evaluation theorems in `StatementEquivalence.lean`, proven by mutual structural induction:

1. `evalIRExpr_eq_evalYulExpr` - IR and Yul expression evaluation are identical when states are aligned
2. `evalIRExprs_eq_evalYulExprs` - List version of the above

These were previously axioms but were eliminated by making the IR interpreter total (PR #241). The proof works because both eval functions have identical structure and `yulStateOfIR` copies all fields (including `selector`).

## References

- **Proof Inventory**: `Compiler/Proofs/README.md`
- **IR Semantics**: `Compiler/Proofs/IRGeneration/IRInterpreter.lean`
- **Verification Status**: `docs/VERIFICATION_STATUS.md`
