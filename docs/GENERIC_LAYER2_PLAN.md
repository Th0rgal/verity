# Generic Layer 2 Plan

Tracking:
- umbrella issue: [#1510](https://github.com/Th0rgal/verity/issues/1510)
- current proof blocker: [#1564](https://github.com/Th0rgal/verity/issues/1564)

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

## Why The Current Architecture Cannot Satisfy The Goal

The current proof boundary stops too low and too late:

- `Compiler/Proofs/IRGeneration/SupportedFragment.lean` only re-exports a
  statement-list theorem over `SupportedStmtList`
- `Contracts/Proofs/SemanticBridge.lean` still proves whole-contract results by
  assuming a contract-specific `hpost`
- dispatch selection, parameter loading, whole-function assembly, and contract-level
  execution are therefore not proved generically as part of Layer 2

As long as whole-contract reasoning is centered in `SemanticBridge.lean`, the repo
does not have a generic compiler proof. It has a transport theorem around per-contract
proofs.

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

Keep `Contracts/Proofs/SemanticBridge.lean` only as:

`Contracts/Proofs/SemanticBridge.lean` becomes client/example layer only.

- examples
- regressions
- composition wrappers for already-proved generic theorems

It must stop being the source of Layer 2 whole-contract correctness.

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
- docs identify `SemanticBridge.lean` as example/wrapper layer, not proof source

## Tracking Checklist

Use this checklist in the PR description and keep it current:

- [x] Define `SupportedFunction` / `SupportedSpec`
- [x] Define source whole-contract semantics for the supported fragment
- [x] Prove param-loading correctness
- [x] Prove `compileFunctionSpec` correctness
- [x] Prove selector-dispatch correctness
- [x] Prove generic whole-contract `CompilationModel.compile` correctness
- [ ] Refactor one existing contract proof into theorem instantiation
- [ ] Update Layer 2 documentation boundaries

## Current Proof Status

The generic whole-contract theorem exists and its proof chain is complete:

- **`compile_preserves_semantics`** in [`Contract.lean`](../Compiler/Proofs/IRGeneration/Contract.lean), quantified over arbitrary supported `CompilationModel`s, selectors, a `SupportedSpec` witness, and successful `CompilationModel.compile`. No contract-specific bridge premise.
- **`compileFunctionSpec_correct_generic`** in the same file, per-function correctness.
- **`interpretContract_correct_of_compiled_functions`** in [`Dispatch.lean`](../Compiler/Proofs/IRGeneration/Dispatch.lean), selector-dispatch preservation.

The proof chain transitively depends on 1 documented axiom: `supported_function_body_correct_from_exact_state` in [`Function.lean`](../Compiler/Proofs/IRGeneration/Function.lean). This axiom covers non-core body simulation (storage writes, mapping writes, and other complex statement patterns). See [AXIOMS.md](../AXIOMS.md) for details and elimination plan.

**Remaining work**:
- No existing contract has been refactored to use the generic theorem yet; end-to-end examples still use manual bridge theorems in `SemanticBridge.lean`.
- Eliminating the body-simulation axiom requires proving the remaining non-core statement patterns ([#1564](https://github.com/Th0rgal/verity/issues/1564)).

## Non-Goals For The First Generic Theorem

The first theorem does not need to cover everything. It may explicitly leave out:

- constructor semantics
- fallback / receive
- events/logs
- external or linked calls
- internal helper compositional reuse
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
- the old contract-specific Layer 2 theorem is reduced to a wrapper or removed
