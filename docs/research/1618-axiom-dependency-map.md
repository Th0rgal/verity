# Issue #1618 dependency map: `supported_function_body_correct_from_exact_state`

Repository snapshot:

- Repo: `Th0rgal/verity`
- Branch analyzed: `main` as checked out into `research/1618-stmt-induction-map`
- Commit: `e7435c67e59c70c882aab4106133fd80f8a47ba3`

## Why this option

I chose Option A because the highest-leverage blocker on the current `main` branch is no longer "what should the generic induction library look like?". That work already exists in `Compiler/Proofs/IRGeneration/GenericInduction.lean`.

The practical blocker is now theorem wiring:

- which function-level theorem still dispatches between core, terminal, and generic paths,
- which hypotheses each branch consumes,
- where the old axiom-shaped contract has already been replaced, and
- what would still need to change if the generic theorem were tightened or reshaped.

That information directly unblocks follow-up implementation without guessing against stale issue text.

## Executive summary

The issue body describes a three-way split ending in the axiom `supported_function_body_correct_from_exact_state`. That is stale relative to the current `main` branch at `e7435c6`.

On the analyzed branch:

- there is no remaining direct declaration or call site of `supported_function_body_correct_from_exact_state`,
- `supported_function_correct` still branches `core` vs `non-core`,
- the non-core branch still branches `terminal` vs `generic`,
- the fallback branch now calls `supported_function_body_correct_from_exact_state_generic_with_helpers`,
- the helper-aware wrapper is a thin adapter over `supported_function_body_correct_from_exact_state_generic`.

So the live dependency fan-in is now:

1. `supported_function_correct`
2. `supported_function_body_correct_from_exact_state_core_extraFuel`
3. `supported_function_body_correct_from_exact_state_terminal_core_extraFuel`
4. `supported_function_body_correct_from_exact_state_generic_with_helpers`
5. `supported_function_body_correct_from_exact_state_generic`

## Branch structure in `supported_function_correct`

The controlling theorem is `supported_function_correct` in `Compiler/Proofs/IRGeneration/Function.lean:1135`.

Its body sets up:

- exact parameter binding state via `supported_function_param_state_exact`,
- runtime/IR correspondence after prebinding via `runtimeStateMatchesIR_prebindRawArgs`,
- runtime/IR correspondence after applying bindings via `runtimeStateMatchesIR_applyBindingsToIRState`.

It then dispatches as follows:

| Branch | Predicate | Theorem called | Location |
| --- | --- | --- | --- |
| core | `StmtListCompileCore (fn.params.map (·.name)) fn.body` | `supported_function_body_correct_from_exact_state_core_extraFuel` | `Function.lean:1220` |
| terminal non-core | `¬ core` and `StmtListTerminalCore (fn.params.map (·.name)) fn.body` | `supported_function_body_correct_from_exact_state_terminal_core_extraFuel` | `Function.lean:1393` |
| generic non-terminal | `¬ core` and `¬ terminal` and `StmtListGenericCore ... fn.body` | `supported_function_body_correct_from_exact_state_generic_with_helpers` | `Function.lean:1437` |

This means the old axiom-shaped "everything else" slot has already been replaced by a proved generic theorem with additional helper-surface assumptions.

## Dependency map

### 1. `supported_function_body_correct_from_exact_state_core`

- Definition: `Compiler/Proofs/IRGeneration/Function.lean:679`
- Caller theorem: no in-repo call sites on this branch
- Role: zero-extra-fuel specialization of the core body theorem
- Preconditions it requires:
  - normalized fields: `SourceSemantics.effectiveFields model = model.fields`
  - no events: `model.events = []`
  - no errors: `model.errors = []`
  - successful parameter binding: `bindSupportedParams ... = some bindings`
  - core witness: `StmtListCompileCore (fn.params.map (·.name)) fn.body`
  - successful body compilation
  - runtime/IR match for the pre-body state with `bindings := []`
  - exact bindings/IR-variable match for `bindings`
- Branch exercised: `core`
- What changes if the old axiom is replaced by a proved theorem with the same signature:
  - nothing at this node
  - this theorem is independent of the generic/axiom branch and serves as a baseline specialization

### 2. `supported_function_body_correct_from_exact_state_core_extraFuel`

- Definition: `Compiler/Proofs/IRGeneration/Function.lean:748`
- Called from: `supported_function_correct` at `Compiler/Proofs/IRGeneration/Function.lean:1220`
- Caller theorem name: `supported_function_correct`
- Preconditions passed by the caller:
  - `model`, `fn`, `bodyStmts`, `tx`, `initialWorld`
  - `state := ParamLoading.applyBindingsToIRState (prebindRawArgs initialState fn.params) bindings`
  - `bindings`
  - `extraFuel := sizeOf irFn.body - irFn.body.length`
  - `hnormalized` from `hSupported.normalizedFields`
  - `hnoEvents := hSupported.noEvents`
  - `hnoErrors := hSupported.noErrors`
  - `hbind`
  - `hcore`
  - `hbodyCompile`
  - `hbodyStateRuntime`
  - `hbodyStateBindings`
- Branch exercised: `core`
- What changes if the old axiom is replaced by a proved theorem with the same signature:
  - nothing at this call site
  - the core branch is already completely separate from the former axiom path
  - only a larger refactor that unifies all branches under `StmtListGenericCore` would remove this separate dispatch

### 3. `supported_function_body_correct_from_exact_state_terminal_core_extraFuel`

- Definition: `Compiler/Proofs/IRGeneration/Function.lean:818`
- Called from: `supported_function_correct` at `Compiler/Proofs/IRGeneration/Function.lean:1393`
- Caller theorem name: `supported_function_correct`
- Preconditions passed by the caller:
  - `model`, `fn`, `bodyStmts`, `tx`, `initialWorld`
  - `state := ParamLoading.applyBindingsToIRState (prebindRawArgs initialState fn.params) bindings`
  - `bindings`
  - `extraFuel := sizeOf irFn.body - irFn.body.length`
  - `hextraFuel := hbodyExtraFuelLower`
  - `hnormalized` from `hSupported.normalizedFields`
  - `hnoEvents := hSupported.noEvents`
  - `hnoErrors := hSupported.noErrors`
  - `hbind`
  - `hterminal`
  - `hbodyCompile`
  - `hbodyStateRuntime`
  - `hbodyStateBindings`
- Branch exercised: `terminal`
- What changes if the old axiom is replaced by a proved theorem with the same signature:
  - nothing at this call site
  - this branch continues to isolate the `ite`-capable proof path from the generic fallback
  - if future work subsumes terminal proofs into the generic library, this call site disappears, but that is a structural simplification rather than an axiom-elimination requirement

### 4. `supported_function_body_correct_from_exact_state_generic`

- Definition: `Compiler/Proofs/IRGeneration/GenericInduction.lean:3633`
- Called from: `supported_function_body_correct_from_exact_state_generic_with_helpers` at `Compiler/Proofs/IRGeneration/GenericInduction.lean:3769`
- Caller theorem name: `supported_function_body_correct_from_exact_state_generic_with_helpers`
- Preconditions passed by the caller:
  - `model`, `fn`, `bodyStmts`, `tx`, `initialWorld`, `state`, `bindings`, `extraFuel`
  - `hextraFuel`
  - `hnormalized`
  - `hnoEvents`
  - `hnoErrors`
  - `hgeneric`
  - `hbodyCompile`
  - `hscope`
  - `hbounded`
  - `hstateRuntime`
  - `hstateBindings`
- Branch exercised: `generic`
- What changes if the old axiom is replaced by a proved theorem with the same signature:
  - nothing in the wrapper call itself, because this theorem is already the proof-backed replacement
  - the important contract is that it still returns the same existential shape:
    - source execution result,
    - IR execution result at `bodyStmts.length + extraFuel + 1`,
    - `stmtResultMatchesIRExec`
  - any attempt to tighten this theorem by changing fuel shape or result shape would ripple into both the helper wrapper and `supported_function_correct`

### 5. `supported_function_body_correct_from_exact_state_generic_with_helpers`

- Definition: `Compiler/Proofs/IRGeneration/GenericInduction.lean:3724`
- Called from: `supported_function_correct` at `Compiler/Proofs/IRGeneration/Function.lean:1437`
- Caller theorem name: `supported_function_correct`
- Preconditions passed by the caller:
  - `model`
  - `fn`
  - `bodyStmts`
  - `helperFuel := hSupported.helperFuel`
  - `tx`
  - `initialWorld`
  - `state := ParamLoading.applyBindingsToIRState (prebindRawArgs initialState fn.params) bindings`
  - `bindings`
  - `extraFuel := sizeOf irFn.body - irFn.body.length`
  - `hextraFuel := hbodyExtraFuelLower`
  - `hnormalized` from `hSupported.normalizedFields`
  - `hnoEvents := hSupported.noEvents`
  - `hnoErrors := hSupported.noErrors`
  - helper surface closure:
    `hsupportedFn.body.calls.helperCompatibility.surfaceClosed`
  - generic witness:
    `hgeneric`, derived from `hsupportedFn.body.genericCore`
  - `hbodyCompile`
  - `hscope`, derived from `hbind`
  - `hbounded`, derived from `hbind`
  - `hbodyStateRuntime`
  - `hbodyStateBindings`
- Branch exercised: `generic` fallback for non-core, non-terminal bodies
- What changes if the old axiom is replaced by a proved theorem with the same signature:
  - on this branch, that replacement has effectively already happened
  - the only remaining change would be simplification:
    - if helper-aware semantics become the default body theorem, this wrapper could disappear
    - if helper closure is discharged elsewhere, `supported_function_correct` could call `..._generic` directly

## Additional observations about theorem shape

These are the pieces of theorem surface that the current function-level proof depends on most strongly.

### Fuel contract is stable and reused everywhere

Every active branch ultimately needs:

- an execution statement over `execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts`
- with `extraFuel` chosen at function level as `sizeOf irFn.body - irFn.body.length`
- and, for the terminal/generic branches, a lower bound
  `sizeOf bodyStmts - bodyStmts.length ≤ extraFuel`

This is the most important compatibility point. A future theorem that proves the same semantic fact but changes the fuel formula will force edits in:

- `supported_function_correct`
- the generic helper wrapper
- the downstream bridge to `compileFunctionSpec_correct_of_body_supported_extraFuel`

### The generic path still depends on two derivations outside the theorem

The function-level generic call site does not just need `hgeneric`. It also needs:

- `hscope`, reconstructed from `hbind`
- `hbounded`, reconstructed from `hbind`

That means a future refactor that wants a "drop-in axiom replacement" should preserve those inputs or provide local lemmas that derive them just as cheaply.

### Helper-awareness is an adapter, not the proof engine

`supported_function_body_correct_from_exact_state_generic_with_helpers` is not a second proof of body correctness. It:

1. calls `supported_function_body_correct_from_exact_state_generic`,
2. proves `execStmtListWithHelpers = execStmtList` under helper-surface closure,
3. rewrites the source-side result.

So the real proof engine is `..._generic`; the helper theorem is interface glue.

## What would change if a theorem with the old axiom signature reappeared

If the project decided to reintroduce a single theorem exactly matching the historical axiom interface, the smallest integration surface would be:

1. keep the current `core` branch unchanged,
2. keep the current `terminal` branch unchanged,
3. replace only the generic fallback call at `Function.lean:1437` with that theorem,
4. discharge any additional helper-surface assumptions either:
   - inside the replacement theorem, or
   - in a one-step wrapper analogous to `..._generic_with_helpers`.

In other words, the old "axiom slot" has not disappeared from the function-level architecture. It has been filled by a proved theorem stack with two extra facts:

- `StmtListGenericCore ... fn.body`
- `stmtListTouchesUnsupportedHelperSurface fn.body = false`

That is the narrowest compatibility target for future changes.

## Net result for follow-up implementation

The highest-value follow-up is not another top-down design note. It is to decide whether future work wants to preserve or collapse these two interfaces:

- keep the current three-branch shape and improve generic coverage behind `StmtListGenericCore`, or
- subsume `core` and `terminal` into the generic library so `supported_function_correct` has one body theorem call.

Either way, the current dependency bottleneck is now explicit:

- one function-level dispatcher,
- one helper adapter,
- one generic proof engine,
- two legacy specialized proof branches.
