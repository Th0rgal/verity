# EVMYulLean Legacy and Reference-Oracle Audit

Date: 2026-05-20

## Scope

This audit separates the current EVMYulLean integration into:

- code that is safe to remove now;
- legacy/reference code still required by current proofs;
- custom or transitional semantics that are not part of the public Layer 3
  target but still support Layer 2/Layer 3 plumbing;
- non-proof application oracle code that should not be confused with the
  proof reference oracle.

The current public Layer 3 theorem target is native EVMYulLean execution through
`EvmYul.Yul.callDispatcher`, composed in `Compiler/Proofs/EndToEnd.lean`.
The old public custom-Yul EndToEnd target and `EvmYulLeanRetarget.lean` bridge
are gone.

## Summary

The repo no longer uses a custom Yul interpreter as the public EndToEnd proof
authority. It still uses legacy/reference code in three narrower ways:

1. builtin comparison helpers below the native trust boundary;
2. supported-fragment closure predicates that prove generated Verity Yul stays
   inside the native-admitted subset;
3. Layer 2 helper-free IR compatibility semantics, which are not Yul semantics
   but are still named "legacy" because they bridge current helper-free compiled
   IR into the newer helper-aware interfaces.

The largest remaining cleanup opportunity is to finish demoting the builtin
comparison oracle stack to conformance-only coverage. `IRGeneration/FunctionBody.lean`
now consumes direct EVMYulLean builtin facts, and `scripts/check_yul.py`
enforces the native `EvmYulLeanBuiltinSemantics` boundary rather than requiring
the reference oracle as the builtin boundary. `ReferenceOracle/Builtins.lean`
is no longer on that production proof import path. Removing it outright would
still break the legacy bridge test, the bridge lemma module, and axiom-report
coverage.

## Current Inventory

| Area | File(s) | Status | Reason |
| --- | --- | --- | --- |
| Native public target | `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean`, `Compiler/Proofs/EndToEnd.lean` | Keep | Provides native runtime lowering, `callDispatcher`, checkpoint-aware switch tails, and EndToEnd composition. |
| Native state projection | `EvmYulLeanStateBridge.lean` | Keep | Converts Verity `YulState`/IR storage views to EVMYulLean shared state. Directly imported by the native harness. |
| Runtime adapter | `EvmYulLeanAdapter.lean` | Keep for compatibility | Historical structural lowering remains here for tests and report compatibility. Native runtime lowering has moved to `EvmYulLeanNativeLowering.lean`. |
| Native runtime lowering | `EvmYulLeanNativeLowering.lean` | Keep | Maps emitted Yul builtins to EVMYulLean primops and lowers generated runtime statements/functions into native contracts. |
| Bridge predicates | `EvmYulLeanBridgePredicates.lean` | Keep for now | Current body closure and native harness consume `BridgedExpr`, `BridgedStmts`, and related admissibility predicates. |
| Body closure | `EvmYulLeanBodyClosure.lean` | Keep | Imported by EndToEnd and proves supported source bodies satisfy native bridge predicates. |
| Source/call closure | `EvmYulLeanSourceExprClosure.lean`, `EvmYulLeanCallClosure.lean` | Keep or demote to development-only after checking `PrintAxioms` policy | Source closure is imported by body closure. Call closure is only imported by `PrintAxioms.lean` and docs in this audit. |
| Builtin reference oracle | `ReferenceOracle/Builtins.lean` | Keep as conformance/reporting scaffolding until replaced | Directly imported by `EvmYulLeanBridgeLemmas.lean`, `EvmYulLeanBridgeTest.lean`, and `PrintAxioms.lean`; defines `legacyEvalBuiltinCall*` and backend comparison dispatch. |
| Builtin bridge lemmas | `EvmYulLeanBridgeLemmas.lean` | Keep as conformance/reporting scaffolding until replaced | Proves EVMYulLean builtin behavior agrees with legacy builtin formulas; imported by bridge tests and `PrintAxioms.lean`, but no longer by `IRGeneration/FunctionBody.lean`. |
| Builtin bridge test | `EvmYulLeanBridgeTest.lean` | Keep as conformance test, or move under a test-only namespace | Referenced by `Makefile` and fork conformance workflow. No production proof imports it. |
| Yul builtin-boundary CI check | `scripts/check_yul.py` | Native boundary enforced | The checker now requires `IRInterpreter.lean` to import `EvmYulLeanBuiltinSemantics` and call `evalBuiltinCallWithEvmYulLeanContext`; reference-oracle calls no longer satisfy this boundary. |
| Reference state re-export | removed | Removed in the cleanup PR | It had no direct imports and only re-exported `RuntimeTypes`. |
| Removed retarget stack | `EvmYulLeanRetarget.lean`, older adapter-correctness modules | Already removed | Only mentioned in docs/comments. |
| Stale build references | removed | Removed in the cleanup PR | Targeted verification and runner benchmarks now point at current native proof modules. |
| Deprecated private EndToEnd compatibility wrappers | removed | Removed in the cleanup PR | The unused private generated-callDispatcher wrappers over the legacy dispatcher-exec target were deleted; callers use the direct `nativeGeneratedCallDispatcherResultOf` theorem stack. |

## Dependency Evidence

Direct imports found in the current tree:

- `ReferenceOracle/Builtins.lean` is imported by:
  - `Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas`
  - `Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeTest`
  - `PrintAxioms`
- The removed reference state re-export had no direct imports.
- `EvmYulLeanNativeLowering.lean` is imported by:
  - `Compiler.Proofs.ArithmeticProfile`
  - `EvmYulLeanAdapter`
  - `EvmYulLeanBridgeLemmas`
  - `EvmYulLeanBuiltinSemantics`
  - `EvmYulLeanNativeHarness`
  - `EvmYulLeanNativeSignedArithLemmas`
  - `EvmYulLeanPureBuiltinLemmas`
- `EvmYulLeanAdapter.lean` is imported by:
  - `EvmYulLeanBridgeTest`
  - `PrintAxioms`
- `EvmYulLeanBridgeLemmas.lean` is imported by:
  - `EvmYulLeanBridgeTest`
  - `PrintAxioms`
- `IRGeneration/FunctionBody.lean` imports direct native builtin semantics:
  - `EvmYulLeanBuiltinSemantics`
  - `EvmYulLeanPureBuiltinLemmas`
- `EvmYulLeanBodyClosure.lean` is imported by:
  - `Compiler.Proofs.EndToEnd`
  - `PrintAxioms`
- `EvmYulLeanNativeHarness.lean` is imported by:
  - `Compiler.ERC20MinimalNativeWitness`
  - `Compiler.Proofs.EndToEnd`
  - `EvmYulLeanBodyClosure`
  - `PrintAxioms`
- `EvmYulLeanCallClosure.lean` is imported only by `PrintAxioms.lean`.

Approximate file sizes at audit time:

- `EndToEnd.lean`: 41,597 lines
- `EvmYulLeanNativeHarness.lean`: 37,543 lines
- `EvmYulLeanBodyClosure.lean`: 17,666 lines
- `EvmYulLeanBridgeLemmas.lean`: 3,331 lines
- `ReferenceOracle/Builtins.lean`: 427 lines
- Removed reference state re-export: 13 lines before deletion

## Safe To Remove Now

### Removed Reference State Re-export

This file is a compatibility re-export:

```lean
import Compiler.Proofs.YulGeneration.RuntimeTypes
```

No direct imports were found. Deleting it removes one misleading
`ReferenceOracle` module from the tree.

### Stale build references

The stale executable references to missing historical proof modules have been
replaced with current native proof modules. This does not affect the proof
boundary, but it reduces confusion when auditing the native integration.

### Documentation Wording For The Native Boundary

Docs should avoid saying that a custom-interpreter Yul preservation stack
remains part of Layer 3. A precise statement is:

> Public Layer 3 does not target a custom Yul interpreter. Remaining
> reference-oracle code is builtin comparison scaffolding; remaining "legacy"
> terminology in Layer 2 refers to helper-free IR compatibility, not a public
> Yul semantic target.

## Still Needed In Current Proofs

### `ReferenceOracle/Builtins.lean`

Keep for now as conformance/reporting scaffolding. It contains:

- `legacyEvalBuiltinCallWithContext`
- `BuiltinBackend.verity`
- `BuiltinBackend.evmYulLean`
- `evalBuiltinCallWithBackendContext`
- compatibility simplification lemmas for builtin evaluation

This is not the public EndToEnd target. The bridge lemma layer still proves
native EVMYulLean builtin behavior by comparing it to these legacy formulas, but
the production `FunctionBody.lean` proof now consumes direct native builtin
facts instead. Safe removal requires moving the remaining comparison coverage to
tests or deleting it from `PrintAxioms.lean`.

### `EvmYulLeanBridgeLemmas.lean`

Keep for now as conformance/reporting scaffolding. It is the main consumer of
`ReferenceOracle/Builtins.lean`, but it is no longer imported by
`IRGeneration/FunctionBody.lean`.

The cleanup path is to split this file into:

- direct EVMYulLean builtin facts;
- temporary legacy-comparison facts;
- a small compatibility module imported only by tests or historical proofs.

`FunctionBody.lean` now consumes direct native facts from
`EvmYulLeanBuiltinSemantics.lean` and `EvmYulLeanPureBuiltinLemmas.lean`, and the
remaining direct native `byte` wrapper facts have moved out of this module. The
remaining work is to decide whether the legacy comparison module should remain
as test coverage or leave the axiom-report target entirely.

### `EvmYulLeanBridgePredicates.lean`

Keep for now. The names are transitional, but the role is still active:
admissibility predicates for the emitted fragment. These predicates are not a
custom semantics target by themselves; they are proof-side closure conditions.

The long-term cleanup is to rename or split them into native-fragment predicates
so they no longer read as "bridge from a legacy semantics."

### `EvmYulLeanAdapter.lean`

Keep for compatibility. It now contains the historical structural lowering
surface (`lowerExpr`, `lowerStmtGroup`, `lowerProgram`) and imports
`EvmYulLeanNativeLowering.lean` so older imports still see native declarations.
Production native proof modules import the native lowering module directly.

### `EvmYulLeanBodyClosure.lean` and `EvmYulLeanSourceExprClosure.lean`

Keep. They are large, but they are part of the current proof path from
`SupportedSpec` to native-admitted generated bodies. Removing them would leave
EndToEnd without a supported-fragment closure proof.

### `EvmYulLeanStateBridge.lean`

Keep. This is necessary type/state plumbing from Verity runtime types into
EVMYulLean state. It is not legacy semantic authority.

### `EvmYulLeanCallClosure.lean`

Probably keep for now, but it is not on the active EndToEnd import path. It is
imported only by `PrintAxioms.lean`. If axiom printing does not need to cover
future external-call closure scaffolding, this module could be removed from
`PrintAxioms.lean` or moved to a development-only proof target.

## Custom/Legacy Semantics Still Present

### Builtin reference oracle

This is the only remaining proof-local "custom Yul" semantic evaluator in the
Layer 3 area. It is limited to builtin calls, not whole-program Yul execution.

Current risk:

- Theorems prove native builtins agree with Verity formulas.
- This is useful as regression scaffolding, but it keeps the formulas in the
  proof dependency graph.

Preferred end state:

- Closure proofs mention direct EVMYulLean builtin behavior.
- Legacy builtin formulas exist only as tests, if at all.

### Layer 2 helper-free IR compatibility

Files such as `IRGeneration/IRInterpreter.lean`,
`IRGeneration/GenericInduction.lean`, `IRGeneration/Dispatch.lean`, and
`IRGeneration/Contract.lean` still use names like:

- `LegacyCompatibleExternalStmtList`
- `LegacyCompatibleRuntimeContract`
- `execIRStmts`
- `execIRStmtsWithInternals`

This is not custom Yul semantics. It is IR-side execution and compatibility
plumbing for the helper-free subset while the helper-aware theorem is being
widened. It should not be removed as part of a Layer 3 native cleanup.

Preferred end state:

- Keep the IR semantics, but rename "legacy-compatible" surfaces once helper-rich
  execution is the default.
- Complete the helper-rich path tracked around #1638 so current helper-free
  compatibility witnesses become derivations rather than central premises.

### File-local transition evidence in `EndToEnd.lean`

`EndToEnd.lean` still contains private theorem families named around
`nativeIRRuntimeMatchesIR` and generated dispatcher-exec matches. These are
transition evidence, not public custom-Yul wrappers. They are private and feed
the active native `nativeGeneratedCallDispatcherResultOf` surface.

Cleanup opportunity:

- Collapse duplicated theorem families now that the public target is stable.
- Remove deprecated wrappers after all internal call sites target the direct
  projected native result.

## Not Legacy: Product Oracle Modules

`Compiler/Modules/Oracle.lean` and related tests implement user-facing
read-only oracle ECMs, such as `oracleReadUint256`. They are application
features and trust-surface reporting, not proof reference-oracle semantics.
They should not be removed as part of this cleanup.

## Recommended Cleanup Plan

### PR A: mechanical safe cleanup

- Delete the stale reference-state compatibility re-export. Done in this PR.
- Remove or replace stale `Makefile` / benchmark references to missing modules.
  Done in this PR.
- Tighten docs wording so "ReferenceOracle" is clearly builtin-only and below
  the public trust boundary.
- Validation: `lake build Compiler.Proofs.EndToEnd`, `lake build
  Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas`, `lake build
  Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness`, `make check`.

### PR B: split native runtime lowering from historical adapter

- Extract native runtime primop lookup and runtime lowering from
  `EvmYulLeanAdapter.lean` into a native module.
- Update native harness/imports to use the native module.
- Leave historical structural lowering only where tests or legacy comparison
  modules still need it.
- Validation: same as PR A plus `EvmYulLeanBridgeTest`.

### PR C: remove builtin reference oracle from production proof imports

- Re-state bridge predicate discharge lemmas against direct EVMYulLean builtin
  facts.
- Update `IRGeneration/FunctionBody.lean` so it no longer imports
  `EvmYulLeanBridgeLemmas.lean` if it only needs direct native facts.
- Move legacy builtin comparison facts into a test/conformance module.
- Delete `ReferenceOracle/Builtins.lean` once no production proof imports it.

### PR D: shrink EndToEnd transition evidence

- Replace deprecated internal wrappers with direct uses of
  `nativeGeneratedCallDispatcherResultOf`.
- Collapse duplicated positive/project/noMapping/mapping theorem families where
  possible.
- Keep theorem statements over `EvmYul.Yul.callDispatcher`.

### PR E: Layer 2 helper-rich completion

- Continue #1638: thread helper-summary soundness into the exact helper-aware
  compiled target.
- After helper-rich compiled semantics is primary, rename or retire
  "legacy-compatible" IR witnesses.

## Bottom Line

The EVMYulLean integration is no longer publicly based on custom Yul semantics.
The remaining custom/reference material is not safe to delete wholesale because
current proof modules still consume builtin comparison facts and native-fragment
closure predicates. The safe immediate cleanup removed the reference-state
re-export and stale build references. The meaningful perfection step is to remove
`ReferenceOracle/Builtins.lean` from production proof imports by replacing
legacy builtin comparison with direct EVMYulLean builtin lemmas.
