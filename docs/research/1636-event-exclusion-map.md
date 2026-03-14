# Issue #1636: Event Exclusion Map for Layer 2 Proofs

## Chosen option

This artifact implements **Option A**.

Reason: the repository already compiles `emit`/`rawLog` correctly, and the immediate blocker is the proof-surface gating chain in `SupportedSpec.lean`. Mapping that chain precisely is the shortest path to an implementation PR.

## Baseline: event emission already compiles

The problem is not code generation.

- `Stmt.emit` and `Stmt.rawLog` are first-class statement constructors in [Compiler/CompilationModel/Types.lean](/workspaces/mission-e5876dfd/repo/Compiler/CompilationModel/Types.lean):410 and [Compiler/CompilationModel/Types.lean](/workspaces/mission-e5876dfd/repo/Compiler/CompilationModel/Types.lean):416.
- The typed-IR compiler lowers them in [Compiler/TypedIRCompiler.lean](/workspaces/mission-e5876dfd/repo/Compiler/TypedIRCompiler.lean):361-376.
- Typed IR lowers them to `logN` Yul in [Compiler/TypedIRLowering.lean](/workspaces/mission-e5876dfd/repo/Compiler/TypedIRLowering.lean):96-101.
- The typed interpreter appends events to `world.events` in [Verity/Core/Free/TypedIR.lean](/workspaces/mission-e5876dfd/repo/Verity/Core/Free/TypedIR.lean):248-260.
- The contract monad already models event append via `emitEvent` in [Verity/Core.lean](/workspaces/mission-e5876dfd/repo/Verity/Core.lean):463-470.

Conclusion: issue `#1636` is a **Layer 2 proof-surface exclusion**, not a frontend/compiler/codegen gap.

## Exclusion map

### 1. Effect-surface gate marks `emit` and `rawLog` unsupported

- Function: `stmtTouchesUnsupportedEffectSurface`
- Exact line: [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):285
- Emit/rawLog case: [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):286-288
- Current check:

```lean
def stmtTouchesUnsupportedEffectSurface : Stmt → Bool
  | .requireError _ _ _ | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .emit _ _ | .rawLog _ _ _
  | .externalCallBind _ _ _ | .ecm _ _ => true
```

- Why this excludes events:
  `emit` and `rawLog` are classified as unsupported "observable/effect-rich" statements.
- What would need to change:
  Move event emission out of the unsupported effect bucket. The minimal boolean change is to return `false` for `.emit _ _` and `.rawLog _ _ _`, but that only works if a positive event-output interface replaces the missing proof obligations.

### 2. Legacy contract-surface gate still hard-rejects `emit` and `rawLog`

- Function: `stmtTouchesUnsupportedContractSurface`
- Exact line: [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):448
- Emit/rawLog case: [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):463-466
- Current check:

```lean
def stmtTouchesUnsupportedContractSurface (stmt : Stmt) : Bool :=
  match stmt with
  ...
  | .emit _ _ | .internalCall _ _ | .internalCallAssign _ _ _
  | .rawLog _ _ _ | .externalCallBind _ _ _ | .ecm _ _ => true
```

- Why this excludes events:
  Even if feature-local interfaces were widened, the compatibility scan still labels event statements as unsupported.
- What would need to change:
  Flip the `.emit` and `.rawLog` cases to `false`, or redefine this legacy scan in terms of the new event-aware interface so it no longer treats events as a fail-closed surface.

### 3. The legacy contract-surface theorem explicitly folds in the effect surface

- Function: `stmtListTouchesUnsupportedContractSurface_eq_featureOr`
- Exact line: [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):986
- Effect-surface fold: [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):988-1002
- Current check:

```lean
stmtListTouchesUnsupportedContractSurface stmts =
  (stmtListTouchesUnsupportedCoreSurface stmts ||
    stmtListTouchesUnsupportedStateSurface stmts ||
    stmtListTouchesUnsupportedCallSurface stmts ||
    stmtListTouchesUnsupportedEffectSurface stmts)
```

- Why this excludes events:
  The contract-level exclusion is definitionally tied to the effect surface, so any `emit`/`rawLog` marked there keeps the whole body outside the proof fragment.
- What would need to change:
  Either:
  1. event emission stops being part of `stmtListTouchesUnsupportedEffectSurface`, or
  2. `stmtListTouchesUnsupportedContractSurface` is redefined so event output is modeled separately instead of counted as unsupported.

### 4. The positive body witness requires the effect surface to be closed

- Structure: `SupportedBodyEffectInterface`
- Exact line: [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):862-863
- Current check:

```lean
structure SupportedBodyEffectInterface (fn : FunctionSpec) : Prop where
  surfaceClosed : stmtListTouchesUnsupportedEffectSurface fn.body = false
```

- Why this excludes events:
  Every supported function body must prove that its effect surface is empty. With the current definition, any body containing `emit` or `rawLog` cannot satisfy this witness.
- What would need to change:
  Replace "effect surface closed" with a positive event-output interface, for example a witness that event statements refine a log trace while preserving the existing storage-state guarantees.

### 5. Every supported function body must carry that effect witness

- Structure: `SupportedBodyInterface`
- Exact line: [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):869-875
- Current check:

```lean
structure SupportedBodyInterface (spec : CompilationModel) (fn : FunctionSpec) : Prop where
  stmtList : SupportedStmtList spec.fields fn.body
  core : SupportedBodyCoreInterface fn
  state : SupportedBodyStateInterface fn
  calls : SupportedBodyCallInterface spec fn
  effects : SupportedBodyEffectInterface fn
  noLocalObligations : fn.localObligations = []
```

- Why this excludes events:
  The supported-body witness directly depends on the effect witness above.
- What would need to change:
  Replace or widen `effects` so supported bodies can contain event statements together with a proof obligation about emitted logs.

### 6. The body witness is re-exported back into the legacy contract-surface closure theorem

- Theorem: `SupportedBodyInterface.surfaceClosed`
- Exact line: [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):1218-1226
- Current check:

```lean
theorem SupportedBodyInterface.surfaceClosed ... :
    stmtListTouchesUnsupportedContractSurface fn.body = false := by
  exact stmtListTouchesUnsupportedContractSurface_eq_false_of_featureClosed fn.body
    hBody.core.surfaceClosed
    hBody.state.surfaceClosed
    hBody.calls.surfaceClosed
    hBody.effects.surfaceClosed
```

- Why this excludes events:
  Even after feature-local refactors, the supported-body witness is still collapsed back into the legacy "unsupported contract surface" result, and `hBody.effects.surfaceClosed` is one of the required inputs.
- What would need to change:
  Update this theorem and its callers to derive a body-level closure result that is event-aware, likely by splitting "state-preserving support" from "output-trace support".

### 7. `emit` specifically also hits a whole-contract `spec.events = []` gate

- Structure: `SupportedSpecSurface`
- Exact line: [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):900-903
- Re-export theorem: [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):1258-1262
- Current check:

```lean
structure SupportedSpecSurface (spec : CompilationModel) : Prop where
  noConstructor : spec.constructor = none
  noEvents : spec.events = []
  noErrors : spec.errors = []
  noExternals : spec.externals = []
```

- Why this excludes events:
  `Stmt.emit` depends on event definitions, so a contract that uses typed `emit` cannot satisfy `spec.events = []`. `Stmt.rawLog` does not require `spec.events`, so this gate is specific to typed-event support, not raw logs.
- What would need to change:
  Widen `SupportedSpecSurface` so event declarations are allowed when accompanied by an event semantics/log-trace interface.

## What does **not** exclude events

These definitions already treat event emission as supported in their own narrower dimension.

- `stmtTouchesUnsupportedCoreSurface` returns `false` for `.emit` and `.rawLog` in [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):322-323.
- `stmtTouchesUnsupportedStateSurface` returns `false` for `.emit` and `.rawLog` in [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):341-342.
- `stmtTouchesUnsupportedCallSurface` returns `false` for `.emit` and `.rawLog` in [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):367-368.
- `stmtTouchesUnsupportedHelperSurface` returns `false` for `.emit` and `.rawLog` in [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):391-392.
- `stmtTouchesUnsupportedForeignSurface` returns `false` for `.emit` and `.rawLog` in [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):414-415.
- `stmtTouchesUnsupportedLowLevelSurface` returns `false` for `.emit` and `.rawLog` in [Compiler/Proofs/IRGeneration/SupportedSpec.lean](/workspaces/mission-e5876dfd/repo/Compiler/Proofs/IRGeneration/SupportedSpec.lean):439.

This is the key architectural signal: events are already treated as **not** being a state, helper, foreign-call, or low-level-mechanics problem. The remaining blocker is the dedicated "effect/output" boundary plus the typed-event declaration gate.

## Downstream workaround pattern in `morpho-verity`

`morpho-verity` is accessible at `Th0rgal/morpho-verity`, and it contains the documented workaround.

### Pattern summary

The workaround is:

1. attach a site-local `local_obligations [...]` annotation explaining the handwritten event/log boundary,
2. manually stage payload words with `mstore`,
3. emit the event with `rawLog` and explicit topics.

This is exactly the verbose escape hatch described in issue `#1636`.

### Example 1: `flashLoan`

- Macro version: [Morpho/Compiler/MacroSlice.lean](/workspaces/mission-e5876dfd/morpho-verity/Morpho/Compiler/MacroSlice.lean):368-373
- Current pattern:

```lean
function flashLoan ... local_obligations
  [flash_loan_memory := assumed "... raw log ... expected FlashLoan event."] : Unit := do
  ...
  mstore 0 assets
  rawLog [flashLoanTopic, sender, token] 0 32
```

- Spec-model version: [Morpho/Compiler/Spec.lean](/workspaces/mission-e5876dfd/morpho-verity/Morpho/Compiler/Spec.lean):639-650
- Key event tail:
  `Stmt.mstore (Expr.literal 0) (Expr.param "assets")`
  followed by
  `Stmt.rawLog [Expr.literal flashLoanEventTopic, Expr.caller, Expr.param "token"] (Expr.literal 0) (Expr.literal 32)`

### Example 2: `setAuthorizationWithSig`

- Macro version: [Morpho/Compiler/MacroSlice.lean](/workspaces/mission-e5876dfd/morpho-verity/Morpho/Compiler/MacroSlice.lean):213-256
- Current pattern:
  the function carries `local_obligations [authorization_sig_memory := assumed "... direct memory writes and low-level operations ..."]`, then uses multiple `mstore`s and two `rawLog`s:
  - first log at [Morpho/Compiler/MacroSlice.lean](/workspaces/mission-e5876dfd/morpho-verity/Morpho/Compiler/MacroSlice.lean):250-252
  - second log at [Morpho/Compiler/MacroSlice.lean](/workspaces/mission-e5876dfd/morpho-verity/Morpho/Compiler/MacroSlice.lean):254-256
- Spec-model version: [Morpho/Compiler/Spec.lean](/workspaces/mission-e5876dfd/morpho-verity/Morpho/Compiler/Spec.lean):654-705
- Key event tails:
  - increment nonce log at [Morpho/Compiler/Spec.lean](/workspaces/mission-e5876dfd/morpho-verity/Morpho/Compiler/Spec.lean):697-699
  - set-authorization log at [Morpho/Compiler/Spec.lean](/workspaces/mission-e5876dfd/morpho-verity/Morpho/Compiler/Spec.lean):702-704

### Why this workaround exists

The workaround succeeds at compilation, but it does not make the function body eligible for whole-contract Layer 2 support because:

- `mstore` is already outside the current proof fragment, and
- `rawLog` is explicitly outside the effect/output proof fragment.

That is why the workaround is useful for executable parity and trust-report localization, but not for proving eventful contracts inside the current Layer 2 theorem boundary.

## Minimal implementation direction implied by this map

If the implementation follows the issue proposal (`logTrace : List LogEntry`), the minimum proof-surface edits are:

1. Stop classifying `.emit` and `.rawLog` as unsupported in `stmtTouchesUnsupportedEffectSurface`.
2. Stop classifying `.emit` and `.rawLog` as unsupported in `stmtTouchesUnsupportedContractSurface`.
3. Replace `SupportedBodyEffectInterface.surfaceClosed` with a positive event/log-trace interface.
4. Update `SupportedBodyInterface.surfaceClosed` so contract-surface closure no longer treats event output as a rejection reason.
5. Widen `SupportedSpecSurface.noEvents` for typed-event contracts using `Stmt.emit`.

If the first implementation step aims for the narrowest possible change, the least invasive order is:

1. support `rawLog` in the proof state first,
2. thread the new output-trace witness through the body interfaces,
3. only then widen `spec.events = []` so typed `emit` can ride on the same output-trace machinery.

That ordering keeps raw event output and typed event definitions as two separate proof-surface changes, which matches the current code structure.
