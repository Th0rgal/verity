# Generic Layer 2 Plan

Tracking:
- umbrella issue: [#1510](https://github.com/Th0rgal/verity/issues/1510)
- axiom-elimination milestone: [#1618](https://github.com/Th0rgal/verity/issues/1618)
- post-generic-completeness milestone: [#1630](https://github.com/Th0rgal/verity/issues/1630)

## Objective

Implement one compiler-level theorem proving whole-contract semantic preservation for
`CompilationModel.compile` over an explicit supported contract fragment, without any
contract-specific semantic bridge premise.

Target shape:

```lean
theorem compile_preserves_semantics
    (spec : CompilationModel.CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (hTxNormalized : Function.TxContextNormalized tx)
    (hcompile : CompilationModel.compile spec selectors = Except.ok ir) :
    SourceContractSemantics spec tx state =
      IRContractSemantics ir tx (lowerState state)
```

The exact relation may differ, but the theorem must:

- range over a whole `CompilationModel`
- mention successful `CompilationModel.compile`
- be reusable for arbitrary in-scope contracts
- avoid any `post`/`hpost`/contract-specific bridge premise

## Theorem Target Domain

The defensible end-state claim is **not** "all arbitrary Lean EDSL terms compile with a
proof-complete Layer 2 theorem". Arbitrary Lean escape hatches can still construct
`CompilationModel` values outside the frontend's intended macro-lowered surface.

The precise target for the widening work tracked in [#1630](https://github.com/Th0rgal/verity/issues/1630) is:

- prove the generic whole-contract theorem for a proof-complete `CompilationModel` subset
- prove that the macro-lowered image of `verity_contract` lands inside that subset

That is the mechanically checkable meaning of a future "whole EDSL is formally proven"
claim. Stronger claims about arbitrary Lean-produced `CompilationModel` values should not
be made unless the theorem domain itself expands to cover them.

The machine-readable boundary companion for this theorem target now lives in
[`artifacts/layer2_boundary_catalog.json`](../artifacts/layer2_boundary_catalog.json).
It records the exact target claim, the `SupportedSpec` split, the current helper
fail-closed gate, and the ranked follow-on blockers.

## Why The Current Architecture Cannot Satisfy The Goal

The current proof boundary stops too low and too late:

- `Compiler/Proofs/IRGeneration/SupportedFragment.lean` only re-exports a
  statement-list theorem over `SupportedStmtList`
- dispatch selection, parameter loading, whole-function assembly, and contract-level
  execution were therefore not proved generically as part of Layer 2

(Note: the manual `SemanticBridge.lean` has been removed. The generic compiler proof
now serves as the sole Layer 2 boundary.)

## Required Architectural Shift

Move the proof center from client-side bridge theorems to compiler-structure theorems.

The new generic proof should be built as a stack of reusable lemmas aligned with the
compiler pipeline in `Compiler/CompilationModel/Dispatch.lean`:

1. Source function-body semantics
2. Parameter loading correctness
3. `compileStmtList` body correctness
4. `compileFunctionSpec` correctness
5. Selector-dispatch correctness
6. Whole-contract `CompilationModel.compile` correctness

This means the proof architecture should mirror the compiler architecture instead of
mirroring the current contract corpus.

## Proposed Module Structure

Add new compiler-proof modules under `Compiler/Proofs/IRGeneration/`:

- `SupportedSpec.lean`
  Defines the supported whole-contract fragment.
- `ParamLoading.lean`
  Proves calldata/parameter loading matches source-level function invocation.
- `FunctionBody.lean`
  Bridges source function execution to compiled function body execution.
- `Dispatch.lean`
  Proves selector lookup and dispatch preserve function selection and revert behavior.
- `Contract.lean`
  States and proves the final generic whole-contract theorem for `CompilationModel.compile`.

Keep `SupportedFragment.lean` as a lower-level statement theorem only.

`Contracts/Proofs/SemanticBridge.lean` has been removed. The generic compiler proof
is now the sole source of Layer 2 whole-contract correctness.

## Semantic Interfaces To Introduce

### `SupportedSpec`

Introduce an explicit whole-contract supported-fragment witness, for example:

```lean
structure SupportedFunction (fields : List Field) (fn : FunctionSpec) : Prop where
  body : SupportedStmtList fields fn.body
  params : SupportedParamProfile fn.params
  returns : SupportedReturnProfile fn.returns
  internalCalls : SupportedInternalCallProfile fn.body

structure SupportedSpec (spec : CompilationModel) (selectors : List Nat) : Prop where
  selectorCount : selectors.length = spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name) |>.length
  noFallback : spec.functions.all (·.name != "fallback") = true
  noReceive : spec.functions.all (·.name != "receive") = true
  constructor : spec.constructor = none
  functions : ∀ fn, fn ∈ spec.functions -> fn.isInternal = false -> SupportedFunction spec.fields fn
```

The exact fields can differ, but the first theorem must make the scope auditable at
whole-contract level.

### Source Semantics

Do not state the contract theorem against a contract-specific `runSpec`.

Instead define a generic source execution function for a whole `CompilationModel`
contract, with the same observable shape as `interpretIR`:

- selector-based function lookup
- calldata argument decoding boundary
- success/revert behavior
- storage rollback on revert
- return value
- event/log surface if included

If the first theorem excludes events/logs or constructors, encode that in the theorem
boundary instead of hiding it in client proofs.

## Recommended First Supported Fragment

The shortest path to a real generic theorem is to prove a deliberately narrow but
whole-contract fragment:

- external functions only
- no constructor
- no fallback / receive
- no internal helper calls in the first theorem
- no linked/external functionality
- no events/logs in the first theorem
- function bodies already witnessed by `SupportedStmtList`
- parameter profiles restricted to the existing ABI head-word path already handled by
  the typed IR/compiler proof stack

This is the highest-leverage first slice because it closes the main correctness gap:
whole-contract dispatch plus `compileFunctionSpec`, without reopening all advanced
features at once.

## Proof Dependency Graph

The implementation should progress in this order:

1. Define `SupportedFunction` and `SupportedSpec`
2. Define source-level whole-function/whole-contract semantics for that fragment
3. Prove parameter loading correctness against source invocation semantics
4. Prove `compileFunctionSpec` preserves one supported external function
5. Prove selector lookup in `interpretIR` matches source function lookup
6. Prove whole-contract theorem for contracts whose external functions all satisfy
   `SupportedFunction`
7. Refactor one existing bridge theorem into a thin instantiation wrapper
8. Update docs so the repo points to the new theorem as the Layer 2 result

Do not start by expanding `SupportedStmtList`; that has lower leverage than proving the
contract/function layers above it.

## Highest-Leverage Actions

When choosing what to do next, prefer the first unfinished item in this list:

1. Introduce `SupportedSpec` and a source whole-contract semantics record with the same
   observable shape as `interpretIR`
2. Prove `compileFunctionSpec` correctness for one supported external function
3. Prove selector dispatch correctness at contract level
4. State and prove the final `CompilationModel.compile` theorem
5. Refactor one existing contract proof to instantiate the generic theorem
6. Only after that, broaden the supported fragment

This ordering matters because it converts the proof burden from per-contract to
per-compiler-boundary as early as possible.

## Concrete Acceptance Checks

The work is only done if all checks below pass:

- there is exactly one primary generic whole-contract theorem under
  `Compiler/Proofs/IRGeneration/`
- the theorem directly depends on `CompilationModel.compile`
- the theorem does not accept `post`, `hpost`, or any contract-specific semantic premise
- a supported contract can obtain Layer 2 correctness by theorem instantiation alone
- no new contract-specific Layer 2 bridge theorem is introduced to demonstrate success
- `SemanticBridge.lean` has been removed; the generic theorem is the sole Layer 2 proof source

## Tracking Checklist

Use this checklist in the PR description and keep it current:

- [x] Define `SupportedFunction` / `SupportedSpec`
- [x] Define source whole-contract semantics for the supported fragment
- [x] Prove param-loading correctness
- [x] Prove `compileFunctionSpec` correctness
- [x] Prove selector-dispatch correctness
- [x] Prove generic whole-contract `CompilationModel.compile` correctness
- [x] Refactor one existing contract proof into theorem instantiation
- [x] Update Layer 2 documentation boundaries

## Current Proof Status

The generic whole-contract theorem exists and its proof chain is complete:

- **`compile_preserves_semantics`** in [`Contract.lean`](../Compiler/Proofs/IRGeneration/Contract.lean), quantified over arbitrary supported `CompilationModel`s, selectors, a `SupportedSpec` witness, and successful `CompilationModel.compile`. No contract-specific bridge premise. The theorem now targets the canonical helper-aware source semantics induced by `SupportedSpec.helperFuel`, so future helper-summary composition can extend the existing theorem surface instead of replacing it.
- **`compileFunctionSpec_correct_generic`** in the same file, per-function correctness.
- **`interpretContract_correct_of_compiled_functions`** in [`Dispatch.lean`](../Compiler/Proofs/IRGeneration/Dispatch.lean), selector-dispatch preservation.
- **`counter_supported_spec_compile_preserves_semantics`** in [`Contract.lean`](../Compiler/Proofs/IRGeneration/Contract.lean), the first direct consumer instantiating the generic theorem for an existing supported demo model, with no contract-specific body-simulation premise.

The proof chain no longer depends on `supported_function_body_correct_from_exact_state`; that axiom has been deleted. The only remaining documented project axiom is the selector-level `keccak256_first_4_bytes` assumption in [`Compiler/Selector.lean`](../Compiler/Selector.lean), as tracked in [AXIOMS.md](../AXIOMS.md).

- `Compiler.Proofs.IRGeneration.Contract.compile_preserves_semantics`

This theorem is now quantified over a whole `CompilationModel`, selectors, a
`SupportedSpec` witness, and successful `CompilationModel.compile`, with no
contract-specific semantic bridge premise and no Layer 2 axiom. The source side
is already phrased in the helper-aware semantics family via the canonical fuel
computed from `SupportedSpec.helperFuel`; on the current fragment that helper-aware
semantics is proved equal to the legacy helper-free semantics, so the trusted
boundary is unchanged while the future helper-composition target is now the
current theorem surface. The function closure is discharged generically from the
supported statement fragment, and the compiled-function-table witness is derived
directly from `CompilationModel.compile = Except.ok ir`.

The main objective of issue #1618 is therefore complete. Remaining Layer 2 work
now sits under the post-generic widening/completeness plan in
[#1630](https://github.com/Th0rgal/verity/issues/1630):

- keep shrinking the body-level `SupportedSpec` witness by replacing the new
  `core` / `state` / `calls` / `effects` interfaces with positive proof
  interfaces
- helper calls now have an explicit summary inventory under `calls.helpers`, and
  `SourceSemantics.lean` now exposes a dedicated helper-aware source semantics
  target (`evalExprWithHelpers` / `execStmtListWithHelpers` /
  `interpretInternalFunctionFuel`), while `SupportedSpec.lean` now attaches a
  reusable `InternalHelperSummaryContract` interface and a strictly decreasing
  helper-rank measure directly to helper-summary witnesses. Expression-position
  helper callees are now tracked separately and must prove world preservation on
  success, which keeps the current helper-aware expression semantics honest
  without constraining statement-position helper summaries the same way.
  `SourceSemantics` now also defines `InternalHelperSummarySound` /
  `SupportedBodyHelperSummariesSound` plus direct-call consumption lemmas for
  `Expr.internalCall`, `Stmt.internalCall`, and `Stmt.internalCallAssign`, so
  helper summaries are now a proof-carrying source-semantics interface rather
  than just an inventory placeholder. `SourceSemantics.lean` now also exposes
  dedicated `SupportedFunctionHelperProofs` / `SupportedSpecHelperProofs`
  wrappers, so future helper composition has an explicit theorem-level slot for
  summary-soundness evidence instead of needing an ad hoc extra hypothesis, and
  `Contract.lean` now mirrors that at the public theorem surface via
  helper-proof-carrying variants such as
  `compile_preserves_semantics_with_helper_proofs`; the
  feature-local `state` / `calls` / `effects` scans recurse through nested `ite` / `forEach` bodies so those
  boundaries are control-flow complete rather than top-level-only, and
  compatibility lemmas still prove that the helper-aware semantics collapses to
  the existing helper-free semantics on the current `SupportedSpec` fragment
- the remaining helper blocker is now pinned down more precisely in
  [`artifacts/layer2_boundary_catalog.json`](../artifacts/layer2_boundary_catalog.json):
  callers still derive generic body proofs through the helper-free `SupportedStmtList` witness,
  the generic body theorem now already targets the helper-aware source semantics family under the current fail-closed helper gate,
  but summary-soundness/rank evidence is still not consumed inside that body proof,
  and the public theorem stack still targets legacy `execIRFunction` / `interpretIR`
  even though `IRInterpreter.lean` now defines helper-aware compiled-side targets
  (`execIRFunctionWithInternals`, `interpretIRWithInternals`) for internal-helper composition;
  the compiled-side blocker is tracked in [#1638](https://github.com/Th0rgal/verity/issues/1638)
- widen the supported whole-contract fragment without reintroducing axioms

## Non-Goals For The First Generic Theorem

The first theorem does not need to cover everything. It may explicitly leave out:

- constructor semantics
- fallback / receive
- events/logs
- external or linked calls
- internal helper compositional reuse:
  `IRInterpreter.lean` now defines helper-aware compiled-side targets
  (`execIRFunctionWithInternals`, `interpretIRWithInternals`) that can execute
  `IRContract.internalFunctions`, so the remaining work is retargeting the proof
  stack to those semantics and consuming helper-summary soundness/rank evidence
- dynamic ABI cases outside the current typed path

If a feature is out of scope, say so in the supported-fragment witness and docs.

## Regression Demonstration

Use one concrete contract as the first proof consumer. The best candidate is whichever
existing contract already fits the first supported fragment with the least auxiliary
machinery. `SimpleStorage` is the most obvious candidate if its current entrypoints can
be expressed entirely through the new generic theorem plus theorem-local state/tx
instantiation.

Success condition for the demo:

- the contract still compiles via `CompilationModel.compile`
- the generic theorem instantiates directly
- the old contract-specific Layer 2 theorems have been removed (SemanticBridge.lean deleted)
