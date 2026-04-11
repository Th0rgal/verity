# Compiler Verification Proofs

Formal verification proofs for the Verity compiler pipeline: `EDSL -> CompilationModel -> IR -> Yul`.

See [TRUST_ASSUMPTIONS.md](../../TRUST_ASSUMPTIONS.md) for the full trust boundary and [verity.thomas.md/verification](https://verity.thomas.md/verification) for the full proof status.

## Verification Layers

- **Layer 1: EDSL = CompilationModel** — Frontend semantic bridge. Generic typed-IR core in [`TypedIRCompilerCorrectness.lean`](../../Compiler/TypedIRCompilerCorrectness.lean), contract-level bridges still per-contract.
- **Layer 2: CompilationModel -> IR** — Generic whole-contract theorem in [`Contract.lean`](IRGeneration/Contract.lean). 0 sorry, 0 axioms.
- **Layer 3: IR -> Yul** — Generic statement/function equivalence in [`Preservation.lean`](YulGeneration/Preservation.lean). 1 documented bridge hypothesis.

This branch now includes the generic compiler-level theorem `Compiler.Proofs.IRGeneration.Contract.compile_preserves_semantics`, rooted at successful `CompilationModel.compile` for an explicit supported whole-contract fragment. The former exact-state body-simulation axiom in `Compiler.Proofs.IRGeneration.Function` has now been eliminated.

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

## Tracking

- Theorem shape: [#1510](https://github.com/Th0rgal/verity/issues/1510)
- Axiom elimination: [#1618](https://github.com/Th0rgal/verity/issues/1618)
- Layer 2 completeness: [#1630](https://github.com/Th0rgal/verity/issues/1630)
- Machine-readable boundary: [`artifacts/layer2_boundary_catalog.json`](../../artifacts/layer2_boundary_catalog.json)
- Plan: [`docs/GENERIC_LAYER2_PLAN.md`](../../docs/GENERIC_LAYER2_PLAN.md)

## Layer 2 Boundary Status

The `SupportedSpec` split is now explicit and auditable: global invariants, feature-local body interfaces, and the current `calls.helpers` helper boundary all appear in `artifacts/layer2_boundary_catalog.json`.

The intended compiled-side compatibility subset is the legacy-compatible external-body Yul subset `LegacyCompatibleExternalStmtList`. The compiled-side retarget theorem is `InterpretIRWithInternalsZeroConservativeExtensionGoal`, decomposed via `InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal` and `interpretIRWithInternalsZeroConservativeExtensionGoal_of_dispatchGoal`. The proof further factors through `InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals` and `interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtSubgoals`. The helper-free conservative-extension goal is now closed: `interpretIRWithInternalsZeroConservativeExtensionGoal_closed`.

`IRInterpreter.lean` classifies dedicated expr-statement builtin cases through `exprStmtUsesDedicatedBuiltinSemantics` and provides direct helper-free lemmas for `stop`, `mstore`, `revert`, `return`, and mapping-slot `sstore`.

`Contract.lean` exposes `compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal` and the closed form `compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed`. The helper-aware compiled target remains available as total fuel-indexed helper-aware IR semantics.

The remaining blocker is summary-soundness evidence threaded through the exact helper-aware compiled induction seam, past the transitional `SupportedFunctionBodyWithHelpersIRPreservationGoal` and then through the exact target `SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal`. The later widening boundary remains tracked in [#1638](https://github.com/Th0rgal/verity/issues/1638).

## Build

```bash
lake build                                    # Build everything
lake build Contracts.SimpleStorage.Proofs     # Build one contract's proofs
```

## Proof Patterns

See [verity.thomas.md/guides/debugging-proofs](https://verity.thomas.md/guides/debugging-proofs) for proof techniques and common tactics.
