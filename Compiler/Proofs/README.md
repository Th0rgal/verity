# Compiler Verification Proofs

Formal verification proofs for the Verity compiler pipeline: `EDSL -> CompilationModel -> IR -> Yul`.

See [TRUST_ASSUMPTIONS.md](../../TRUST_ASSUMPTIONS.md) for the full trust boundary and [verity.thomas.md/verification](https://verity.thomas.md/verification) for proof status.

## Verification Layers

- **Layer 1: EDSL = CompilationModel** -- Frontend semantic bridge. Generic typed-IR core in [`TypedIRCompilerCorrectness.lean`](../../Compiler/TypedIRCompilerCorrectness.lean); contract-level bridges are per-contract.
- **Layer 2: CompilationModel -> IR** -- Generic whole-contract theorem in [`Contract.lean`](IRGeneration/Contract.lean). 0 sorry, 0 axioms.
- **Layer 3: IR -> Yul** -- Generic statement/function equivalence in [`Preservation.lean`](YulGeneration/Preservation.lean). Dispatch bridge is an explicit theorem hypothesis.

All three layers carry zero project-specific axioms.

## Key Files

| File | Role |
|------|------|
| [`EndToEnd.lean`](EndToEnd.lean) | Composed Layers 2+3 theorem |
| [`IRGeneration/Contract.lean`](IRGeneration/Contract.lean) | Generic whole-contract Layer 2 theorem |
| [`IRGeneration/SupportedFragment.lean`](IRGeneration/SupportedFragment.lean) | `SupportedStmtList` fragment definition |
| [`IRGeneration/SupportedSpec.lean`](IRGeneration/SupportedSpec.lean) | Feature-local body interfaces |
| [`IRGeneration/SourceSemantics.lean`](IRGeneration/SourceSemantics.lean) | Helper-aware source semantics |
| [`IRGeneration/GenericInduction.lean`](IRGeneration/GenericInduction.lean) | Helper-aware induction interfaces |
| [`YulGeneration/StatementEquivalence.lean`](YulGeneration/StatementEquivalence.lean) | All 8 Yul statement types proven |
| [`YulGeneration/Preservation.lean`](YulGeneration/Preservation.lean) | IR -> Yul codegen preservation |

## Layer 2 Boundary Status

The `SupportedSpec` split and current boundary are recorded in [`artifacts/layer2_boundary_catalog.json`](../../artifacts/layer2_boundary_catalog.json). The `calls.helpers` sub-interface tracks internal helper call coverage.

**What is proved:**
- Generic whole-contract theorem for the supported fragment
- The helper-free conservative-extension goal is now closed: `interpretIRWithInternalsZeroConservativeExtensionGoal_closed`
- Conservative-extension decomposition: `InterpretIRWithInternalsZeroConservativeExtensionGoal`, `InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal`, `InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals`
- Lift theorems: `interpretIRWithInternalsZeroConservativeExtensionGoal_of_dispatchGoal`, `interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtSubgoals`
- Helper-aware theorem variants: `compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal`, `compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed`
- Expr-statement builtin classification via `exprStmtUsesDedicatedBuiltinSemantics`, with direct helper-free lemmas for `stop`, `mstore`, `revert`, `return`, and mapping-slot `sstore`
- The helper-aware compiled target provides total fuel-indexed helper-aware IR semantics
- The legacy-compatible external-body Yul subset witness is derived from the supported body interface

**Remaining work ([#1638](https://github.com/lfglabs-dev/verity/issues/1638)):**
- Thread summary-soundness evidence through the helper-aware body goal `SupportedFunctionBodyWithHelpersIRPreservationGoal` and the exact helper-rich target `SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal`
- Widen the supported fragment beyond the current `SupportedStmtList` closure

## Tracking

- Layer 2 completeness: [#1630](https://github.com/lfglabs-dev/verity/issues/1630)
- Machine-readable boundary: [`artifacts/layer2_boundary_catalog.json`](../../artifacts/layer2_boundary_catalog.json)
- Plan: [`docs/GENERIC_LAYER2_PLAN.md`](../../docs/GENERIC_LAYER2_PLAN.md)

## Build

```bash
lake build                                    # Build everything
lake build Contracts.SimpleStorage.Proofs     # Build one contract's proofs
```

## Proof Patterns

See [verity.thomas.md/guides/debugging-proofs](https://verity.thomas.md/guides/debugging-proofs) for proof techniques and common tactics.
