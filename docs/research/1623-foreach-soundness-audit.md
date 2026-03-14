# Issue #1623: `forEach` Soundness Audit

## Chosen option

Option A: audit the semantic gap.

This is the highest-leverage artifact because the bug is a soundness split between three different layers:

1. the trusted EDSL execution model,
2. the compilation-model/source proof machinery, and
3. the generated Yul.

Before changing semantics, it is important to pin down which layer is wrong in which way, and which existing proofs are actually affected today.

## Executive summary

`forEach` is currently unsound as a proof primitive.

- The user-facing EDSL helper is definitionally wrong: [`Contracts/Common.lean:331`](/workspaces/mission-9e57d516/verity/Contracts/Common.lean#L331) defines
  `forEach (_name : String) (_count : Uint256) (body : Contract Unit) : Contract Unit := body`.
  Under [`Verity/Core.lean:124-134`](/workspaces/mission-9e57d516/verity/Verity/Core.lean#L124), this means EDSL execution runs the loop body exactly once and ignores both the binder name and the count.
- The compiler lowering is correct: [`Compiler/CompilationModel/Compile.lean:173-180`](/workspaces/mission-9e57d516/verity/Compiler/CompilationModel/Compile.lean#L173) lowers `Stmt.forEach` to a real Yul `for` loop with `i := 0`, condition `lt(i, count)`, and post-step `i := add(i, 1)`.
- The compilation-model source semantics also has a gap: [`Compiler/Proofs/IRGeneration/SourceSemantics.lean:314-377`](/workspaces/mission-9e57d516/verity/Compiler/Proofs/IRGeneration/SourceSemantics.lean#L314) and [`Compiler/Proofs/IRGeneration/SourceSemantics.lean:638-744`](/workspaces/mission-9e57d516/verity/Compiler/Proofs/IRGeneration/SourceSemantics.lean#L638) define `execStmt` / `execStmtWithHelpers` without any `.forEach` branch. A direct attempt to execute a `Stmt.forEach` falls through to the default `| _, _ => .revert`.

So the repo has two separate problems:

1. EDSL-level proofs about contracts that use `forEach` reason about one iteration, while compiled code performs `count` iterations.
2. Compilation-model/source semantics does not currently model `Stmt.forEach` execution at all.

## 1. What the current proof model computes for `forEach`

### 1.1 EDSL contract semantics

The trusted EDSL helper is:

```lean
def forEach (_name : String) (_count : Uint256) (body : Contract Unit) : Contract Unit := body
```

Source: [`Contracts/Common.lean:331`](/workspaces/mission-9e57d516/verity/Contracts/Common.lean#L331)

Since `Contract` is just `ContractState -> ContractResult α`, and `Contract.run` executes the given contract with rollback-on-revert semantics, the equation above implies:

```lean
(forEach name count body).run s = body.run s
```

for every `name`, `count`, `body`, and initial state `s`.

Relevant definitions:

- [`Verity/Core.lean:121-134`](/workspaces/mission-9e57d516/verity/Verity/Core.lean#L121)

Consequences:

- `count = 0` still executes `body` once.
- `count = 1` executes `body` once.
- `count = n + 1` also executes `body` once.
- The binder name is ignored completely.
- There is no loop index visible to the EDSL evaluator.

This is the concrete source of the soundness bug described in issue #1623.

### 1.2 Compilation-model/source semantics

The macro translation preserves `forEach` into the compilation model:

- [`Verity/Macro/Translate.lean:3199-3212`](/workspaces/mission-9e57d516/verity/Verity/Macro/Translate.lean#L3199)

That is, EDSL syntax `forEach "i" count (do ...)` becomes:

```lean
Stmt.forEach "i" countExpr bodyStmts
```

and `Stmt.forEach` is a first-class statement constructor:

- [`Compiler/CompilationModel/Types.lean:409`](/workspaces/mission-9e57d516/verity/Compiler/CompilationModel/Types.lean#L409)

However, the proof semantics for `Stmt` currently does not execute it:

- [`Compiler/Proofs/IRGeneration/SourceSemantics.lean:314-377`](/workspaces/mission-9e57d516/verity/Compiler/Proofs/IRGeneration/SourceSemantics.lean#L314)
- [`Compiler/Proofs/IRGeneration/SourceSemantics.lean:638-735`](/workspaces/mission-9e57d516/verity/Compiler/Proofs/IRGeneration/SourceSemantics.lean#L638)

Both `execStmt` and `execStmtWithHelpers` enumerate specific cases, but neither includes `.forEach`. Therefore:

- `execStmt fields state (.forEach var count body) = .revert`
- `execStmtWithHelpers spec fields fuel state (.forEach var count body) = .revert`

by fallthrough to the final wildcard case.

This is distinct from the EDSL bug. The EDSL executes the body once; the compilation-model source semantics executes it zero times and reverts.

## 2. What compiled Yul actually does

The compiler lowering is:

```lean
| Stmt.forEach varName count body => do
    let countExpr ← compileExpr ...
    let bodyStmts ← compileStmtList ... (varName :: inScopeNames) body
    let initStmts := [YulStmt.let_ varName (YulExpr.lit 0)]
    let condExpr := YulExpr.call "lt" [YulExpr.ident varName, countExpr]
    let postStmts := [YulStmt.assign varName (YulExpr.call "add" [YulExpr.ident varName, YulExpr.lit 1])]
    pure [YulStmt.for_ initStmts condExpr postStmts bodyStmts]
```

Source:

- [`Compiler/CompilationModel/Compile.lean:173-180`](/workspaces/mission-9e57d516/verity/Compiler/CompilationModel/Compile.lean#L173)

So compiled Yul has the intended bounded-loop behavior:

- initialize `varName := 0`
- execute the body while `varName < count`
- increment `varName` after each iteration

Operationally, assuming the body does not terminate early via revert/return/stop:

- `count = 0` executes the body `0` times
- `count = 1` executes the body `1` time with `varName = 0`
- `count = n + 1` executes the body `n + 1` times with `varName = 0, 1, ..., n`

This is the behavior the proof layer should model.

## 3. Every contract/test that uses `forEach`

### 3.1 User-facing contract use

There is one concrete contract-level use today:

- [`Contracts/Counter/Counter.lean:73`](/workspaces/mission-9e57d516/verity/Contracts/Counter/Counter.lean#L73)

Specifically:

- `Contracts.Counter.previewLowLevel (target count)` uses `forEach "i" count (do mstore 96 count; pure ())`

This is the only end-user contract function in the repo currently using `forEach`.

### 3.2 Compilation-model and proof tests that construct `Stmt.forEach`

These are test/infrastructure uses, not end-user contracts:

- [`Compiler/CompilationModelFeatureTest.lean:1735`](/workspaces/mission-9e57d516/verity/Compiler/CompilationModelFeatureTest.lean#L1735)
  `reservedForEachBinderSpec` uses `Stmt.forEach "__loop_idx" (Expr.literal 1) [...]`
- [`Compiler/Proofs/IRGeneration/SupportedSpec.lean:773`](/workspaces/mission-9e57d516/verity/Compiler/Proofs/IRGeneration/SupportedSpec.lean#L773)
  test proving a `Stmt.forEach ... [Stmt.externalCallBind ...]` fragment is supported

### 3.3 Infrastructure definitions and handlers

These are not semantic users, but they are relevant implementation sites:

- [`Contracts/Common.lean:331`](/workspaces/mission-9e57d516/verity/Contracts/Common.lean#L331) EDSL helper definition
- [`Verity/Macro/Translate.lean:3199-3212`](/workspaces/mission-9e57d516/verity/Verity/Macro/Translate.lean#L3199) macro translation
- [`Compiler/CompilationModel/Types.lean:409`](/workspaces/mission-9e57d516/verity/Compiler/CompilationModel/Types.lean#L409) `Stmt.forEach`
- [`Compiler/CompilationModel/Compile.lean:173-180`](/workspaces/mission-9e57d516/verity/Compiler/CompilationModel/Compile.lean#L173) Yul lowering
- various validators / usage-analysis / trust-surface passes mentioned in issue text; these all structurally traverse `Stmt.forEach`, but they do not define runtime semantics

## 4. Which proofs are currently unsound

### 4.1 Concretely unsound today

The concrete affected contract function is:

- [`Contracts/Counter/Counter.lean:63-79`](/workspaces/mission-9e57d516/verity/Contracts/Counter/Counter.lean#L63)
  `previewLowLevel`

Why it is unsound:

- the EDSL definition used as a trusted contract model executes the `mstore` body once regardless of `count`
- the generated Yul executes that body `count` times

Any proof, theorem, or external reasoning step that treats the EDSL meaning of `previewLowLevel` as matching the compiled program is therefore unsound.

### 4.2 Generated per-function bridge declarations for `previewLowLevel`

The macro pipeline systematically generates, for every function, the declarations:

- `<fn>_modelBody`
- `<fn>_model`
- `<fn>_bridge`
- `<fn>_semantic_preservation`

Source:

- [`Verity/Macro/Translate.lean:3630-3633`](/workspaces/mission-9e57d516/verity/Verity/Macro/Translate.lean#L3630)
- [`Verity/Macro/Bridge.lean:17-42`](/workspaces/mission-9e57d516/verity/Verity/Macro/Bridge.lean#L17)

For `previewLowLevel`, this means the environment contains:

- `Contracts.Counter.previewLowLevel_modelBody`
- `Contracts.Counter.previewLowLevel_model`
- `Contracts.Counter.previewLowLevel_bridge`
- `Contracts.Counter.previewLowLevel_semantic_preservation`

Important nuance:

- in the current codebase, `_bridge` and `_semantic_preservation` are only definitional equalities between a function model and its generated body; they are not themselves deep semantic correctness theorems
- so those declarations are not false statements
- however, any downstream consumer that interprets the generated model as a semantically faithful proof artifact for `previewLowLevel` is relying on an unsound source meaning because `forEach` is wrong in the trusted EDSL

### 4.3 Not currently affected

The following existing proof suites are not currently made unsound by this bug because they do not use `forEach`:

- [`Contracts/Counter/Proofs/Basic.lean`](/workspaces/mission-9e57d516/verity/Contracts/Counter/Proofs/Basic.lean)
- [`Contracts/Counter/Proofs/Correctness.lean`](/workspaces/mission-9e57d516/verity/Contracts/Counter/Proofs/Correctness.lean)
- the `Counter` smoke assertions in [`Contracts/Smoke.lean:1064-1097`](/workspaces/mission-9e57d516/verity/Contracts/Smoke.lean#L1064)
  only cover `increment`, `decrement`, and `getCount`

Also, the differential-test interpreter currently dispatches only:

- `increment`
- `decrement`
- `getCount`

for `Counter`:

- [`Contracts/Interpreter.lean:359-363`](/workspaces/mission-9e57d516/verity/Contracts/Interpreter.lean#L359)

So the current interpreter-backed differential testing path does not appear to execute `previewLowLevel`.

### 4.4 Proof machinery that is incomplete rather than unsound

The `SourceSemantics.execStmt` / `execStmtWithHelpers` gap for `.forEach` is currently an incompleteness bug in the compilation-model proof semantics:

- direct execution of model bodies containing `.forEach` reverts instead of looping
- this does not certify a false loop theorem on its own
- but it blocks any future source-level proof that tries to reason directly about `.forEach`

So:

- EDSL `forEach` is unsound
- compilation-model `SourceSemantics` for `.forEach` is missing/incomplete

Both need to be fixed for end-to-end soundness.

## 5. Minimal reproducer of the semantic gap

Take the body:

```lean
forEach "i" count (do
  mstore 96 count
  pure ())
```

Current EDSL meaning:

- one `mstore`, regardless of `count`

Current compilation-model source semantics:

- revert, because `.forEach` has no `execStmt` case

Compiled Yul meaning:

- `count` many `mstore`s, with loop variable `i = 0 .. count - 1`

For `count = 0`, all three disagree:

- EDSL: executes once
- `SourceSemantics`: reverts
- Yul: executes zero times

## 6. Implications for the eventual fix

To restore soundness, the repo will need all of the following:

1. Replace the EDSL helper stub in `Contracts/Common.lean` with an actually iterative semantics.
2. Add matching `.forEach` cases to `SourceSemantics.execStmt` and `execStmtWithHelpers`.
3. Add the obvious simp lemmas for zero and successor counts.
4. Re-audit any theorem or generated artifact that treats `previewLowLevel` as a trusted contract-level model.

Given the current repo state, the highest-priority semantic regression test after the fix should be:

- a function whose `forEach` body has an observable repeated side effect
- run at `count = 0`, `1`, and `2`
- checked both at the EDSL level and after lowering to Yul

## Bottom line

Issue #1623 is real and currently splits the repo into three inconsistent meanings of `forEach`:

- EDSL: one iteration
- source proof semantics: revert
- compiled Yul: correct bounded loop

Today’s concrete end-user impact is concentrated in `Contracts.Counter.previewLowLevel`, which is the only contract in-tree that uses `forEach`. That is enough to make proofs or trusted reasoning about that function unsound until the semantics are fixed.
