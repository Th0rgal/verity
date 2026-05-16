# G1 Follow-up Plan: Completing the Native EVMYulLean Transition

This document tracks the **follow-up PR** to
[PR #1822](https://github.com/lfglabs-dev/verity/pull/1822). PR #1822 landed
the public-surface retarget plus G1 increments S1–S4 (leaf
`ExecOnlyBridgeAtFuelRevived` constructors covering the observational-no-op
body family). This PR's goal is to close G1 steps S5–S8 and reach the **full
clean transition** end state.

## Goal: "Full Clean Transition"

`compile_preserves_native_evmYulLean_of_compile_ok_supported_generated_callDispatcher`
holds for **every supported-generated contract directly against
`EvmYul.Yul.callDispatcher`**, with:

1. No `hUserBodyHalt` premise on the public theorem.
2. No opt-in legacy machinery on the proof chain for the supported fragment
   (the legacy fuel-based executor, the retargeting layer, and the
   reference-oracle composition have all been removed in DoD-5).
3. Zero `sorry`, zero new axioms (invariant carried over from PR #1822).

The G1 plan in `docs/NATIVE_EVMYULLEAN_TRANSITION.md` decomposes this into
steps S5–S8. Below is the parallelization design.

## Work Decomposition (DAG)

Each node is a single, independently buildable Lean increment. Edges are
**proof-time dependencies** (the downstream node imports / uses the upstream
theorem). A worker can claim any node whose upstream nodes are merged.

```
            ┌─ A1 ─┐
            │      │
            ├─ A2 ─┼──→ D1 ──→ E6 ──→ F6 ──┐
            │      │                       │
            ├─ A3 ─┘                       │
A (IR-side) │                              │
            │                              ├──→ G (S8)
            ├─ B1 ─┐                       │
B (harness) ├─ B2 ─┼──→ D2 ──→ E7 ──→ F7 ──┤
            └─ B3 ─┘                       │
                                           │
   (pre-existing leaves, no upstream)      │
            E1 ──→ F1 ──┐                  │
            E2 ──→ F2 ──┤                  │
            E3 ──→ F3 ──┼──────────────────┘
            E4 ──→ F4 ──┤
            E5 ──→ F5 ──┘
```

### Layer A — IR-side companion lemmas
*Files: `Compiler/Proofs/IRGeneration/IRInterpreter.lean` only.*

- **A1** `execIRStmts_continue_of_nativePreservableStraightStmts_pre_leave`
  — for a `<straight-stmts>` prefix followed by a `.leave` terminator,
  `execIRStmts` runs through the prefix to `.continue state'` with `state'`
  observationally equal on storage slots and events.
- **A2** `execIRStmts_continue_of_nativePreservableStraightStmts_falling_through`
  — same lemma without the trailing `.leave`. Same induction structure as A1;
  the two are typically shipped together.
- **A3** `execIRFunction_continue_extract_eq` — for `fn.returnVars = []`, the
  function-return extraction over `.continue state'` is a no-op
  (`= execIRStmts fuel state stmts` modulo projection).

**Why pure IR-side:** these lemmas mention no native lowering, no
`reviveJump`, no harness state. A worker can land them without touching
`EvmYulLeanNativeHarness.lean` or `EndToEnd.lean`.

### Layer B — Native harness lemmas
*Files: `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean` only.*

- **B1** `exec_block_lowerStmtsNativeWithSwitchIds_with_leave_ok_eq_of_NativeBlockPreservesWord`
  — variant of `exec_block_leave_ok_add_ten` that splices a
  `NativePreservableStraightStmts`-derived prefix in front of `.Leave`.
- **B2** `exec_block_lowerStmtsNativeWithSwitchIds_ok_eq_of_NativeBlockPreservesWord`
  — no-leave variant: a `.Block (lower preStmts)` with per-slot preservation
  exits with `.ok finalState` and `finalState` projects observationally to
  `initial.reviveJump`.
- **B3** `exec_block_append_eq_of_continue` — general helper: if
  `exec n (.Block xs) state = .ok mid` then
  `exec (n + suffixLen) (.Block (xs ++ ys)) state = exec suffixLen (.Block ys) mid`
  (modulo fuel padding). Used by B1 and B2.

**Why pure harness-side:** these are facts about `EvmYul.Yul.exec` and the
`Block` reduction rule, not about source-IR semantics.

### Layer D — Revived constructors
*Files: `Compiler/Proofs/EndToEnd.lean`.*

- **D1** `NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived.of_nativePreservableStraightStmts_leave`
  — bodies of shape `preStmts ++ [.leave]` with
  `NativePreservableStraightStmts preStmts`. Depends on A1 + B1 + a new
  source-side helper `nativeResultsMatchOn_execIRFunction_nativePreservableStraightStmts_leave_body_markedPrefix`
  (shipped inline in the same commit).
- **D2** `NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived.of_bridgedStraightStmts_falling_through`
  — bodies of shape `preStmts` (no terminator), `fn.returnVars = []`. Depends
  on A2 + A3 + B2 (+ B3 transitively) + a new source-side helper
  `nativeResultsMatchOn_execIRFunction_bridgedStraightStmts_falling_through_body_markedPrefix`
  (shipped inline).

### Layer E — `NativeGeneratedSelectorHitSuccessBridge` adapter chains
*Files: `Compiler/Proofs/EndToEnd.lean`.*

For each Revived leaf, the public success bridge is produced via a 4-link
chain (`Revived → Preserves → Result → SuccessBridge`). One Ei commit per
leaf, each independently green.

- **E1** `.of_empty_body` chain *(pre-existing; verify wiring)*
- **E2** `.of_leave_body` chain *(pre-existing; verify wiring)*
- **E3** `.of_block_empty` chain *(shipped Revived; chain pending)*
- **E4** `.of_block_leave` chain *(shipped Revived; chain pending)*
- **E5** `.of_singleton_comment` chain *(shipped Revived; chain pending)*
- **E6** `.of_nativePreservableStraightStmts_leave` chain *(depends on D1)*
- **E7** `.of_bridgedStraightStmts_falling_through` chain *(depends on D2)*

### Layer F — Label-prefix variants
*Files: `Compiler/Proofs/EndToEnd.lean`.*

Each Fi piggybacks on its Ei. One new theorem
`NativeGeneratedSelectorHitSuccessBridge.of_<leaf>_with_label_prefix` that
takes `fn.body = .comment label :: <leaf body>`, uses the already-shipped
`exec_block_noop_block_head_eq`, and composes the leaf's Ei adapter.

F1..F7 correspond to E1..E7. This step also subsumes the deferred
`.of_comment_cons` shape from G1-S4 — handling comment prefixes at the
success-bridge layer is structurally simpler than recursing inside the
Revived predicate.

### Layer G — Final premise drop (G1-S8)
*Files: `Compiler/Proofs/EndToEnd.lean` and `EvmYulLeanRetarget.lean` call sites.*

Refactor
`compile_preserves_native_evmYulLean_of_compile_ok_supported_generated_callDispatcher`
to remove the `hUserBodyHalt` premise. The case split inside the theorem
collapses (every shape the dispatcher emits now has a `Revived` bridge via
some `Ei`/`Fi`). Update SimpleStorage native theorem and any other public
callsites.

## Parallelization Plan

### Wave 0 — Foundation (parallel, 3 workers)
All in parallel, immediately startable from `main` post-#1822.

- **Worker α** — Layer A (A1+A2+A3 in one commit/PR).
- **Worker β** — Layer B (B1+B2+B3 in one commit/PR).
- **Worker γ** — Layers E1–E5 + F1–F5 (5 short independent commits, one
  branch). Pre-existing leaves: no upstream blocking.

### Wave 1 — Constructors (parallel, 2 workers; starts when Wave 0 α+β land)
- **Worker δ** — D1 (depends on A1, B1).
- **Worker ε** — D2 (depends on A2, A3, B2).

### Wave 2 — Last two chains (parallel, 2 workers; after Wave 1)
- **Worker ζ6** — E6 + F6 (depends on D1).
- **Worker ζ7** — E7 + F7 (depends on D2).

### Wave 3 — Premise drop (1 worker; after Wave 2)
- **Worker η** — G (drop `hUserBodyHalt`).

**Total throughput:** 3 + 2 + 2 + 1 = 8 worker-tasks across 4 sequential
waves. Critical path length: 4 waves. If each wave takes ~1 worker-day, the
full follow-up lands in ~4 days of orchestrator time.

## Alternatives

The straight-line "constructor pyramid" above is the safest path. Three
alternatives are worth considering before kicking off the workers:

### ALT-1 — Predicate refactor
**Idea:** parameterize
`NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived` over a body-shape
witness, so D1+D2 become *one* constructor over `NativePreservableStraightStmts`
plus an optional trailing `.leave`.

- **Pros:** removes the duplication between D1 and D2; future shapes don't
  need a new constructor.
- **Cons:** the predicate is referenced from many call sites; refactoring it
  is a one-shot invasive change that blocks every other worker until it
  lands. Better suited to a separate cleanup PR after S5–S8 ship.

### ALT-2 — Direct semantic equivalence lemma
**Idea:** prove
`nativeResultsMatchOn (executeIR fn) (executeNative fn) ↔ true` directly for
all `BridgedStraightStmts`-shaped `fn.body`, skipping the Revived predicate
entirely.

- **Pros:** collapses A+B+D+E+F into one big proof; conceptually clean.
- **Cons:** requires understanding the full observation projection at once
  (vs. the per-slot preservation that B-layer lemmas already provide).
  Higher proof-design risk; worse for parallelization (no obvious
  sub-targets).

### ALT-3 — Tactic-driven wiring
**Idea:** write a Lean macro / tactic that auto-generates each Ei + Fi chain
given a Revived constructor name.

- **Pros:** Layer E + F becomes ~10 lines per leaf instead of ~40.
- **Cons:** tactic-engineering investment up-front; only pays off if many
  more leaves are added later. Realistic for a *post-S8* cleanup.

### ALT-4 — Skip Layer F via dispatcher-shape normalization
**Idea:** prove a single lemma that the runtime dispatcher always emits a
leading `.comment "<label>"` head, and use it to normalize all
`fn.body = .comment _ :: rest` cases to `rest` before invoking any Revived
bridge.

- **Pros:** eliminates all 7 `_with_label_prefix` variants (Layer F).
- **Cons:** requires inspecting the lower-level dispatcher generation and
  proving a global invariant on its output shape; might not hold for
  hand-written contracts or future dispatcher refactors.

**Recommended:** ship the straight-line plan (A+B+D+E+F+G) as designed.
Revisit ALT-1 and ALT-3 as a separate cleanup PR once the public theorem
no longer has `hUserBodyHalt`.

## Definitions of Done

Every node lands as **one PR or one commit** that satisfies all of:

### Universal (every node)
- `lake build Compiler.Proofs.EndToEnd` exits 0.
- `python3 scripts/check_native_transition_doc.py` passes.
- `python3 scripts/generate_print_axioms.py --check` passes.
- Zero `sorry`, zero `admit`, zero new `axiom`.
- No modification to any existing theorem **signature** (additive only),
  with the explicit exception of node G.
- Commit message follows the existing style (subject + body + `Co-Authored-By`
  trailer).

### Layer-specific

| Node  | Modified files                                                 | Public surface delta                                                                                                                                              |
|-------|----------------------------------------------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| A     | `IRInterpreter.lean`                                           | 3 new private theorems.                                                                                                                                           |
| B     | `EvmYulLeanNativeHarness.lean`                                 | 3 new theorems (one general append helper + 2 block-exec wrappers).                                                                                               |
| D1    | `EndToEnd.lean`                                                | 1 new `private theorem` constructor + 1 new source helper (`..._markedPrefix`).                                                                                   |
| D2    | `EndToEnd.lean`                                                | Same as D1, different shape.                                                                                                                                      |
| Ei    | `EndToEnd.lean`                                                | Up to 4 new theorems wiring the leaf through the chain.                                                                                                           |
| Fi    | `EndToEnd.lean`                                                | 1 new `_with_label_prefix` theorem.                                                                                                                               |
| G     | `EndToEnd.lean`, `EvmYulLeanRetarget.lean`, SimpleStorage proofs | `hUserBodyHalt` premise **removed** from public theorem; downstream callsites updated; `git grep hUserBodyHalt` returns 0 matches in the public surface.        |

### Acceptance smoke tests
- After **all of E + F** land: a smoke-test contract whose `fn.body` matches
  each leaf (and its label-prefixed variant) produces a
  `NativeGeneratedSelectorHitSuccessBridge` via the new adapter, with no
  `hUserBodyHalt` discharge needed.
- After **G** lands:
  `compile_preserves_native_evmYulLean_of_compile_ok_supported_generated_callDispatcher`
  signature has one fewer premise; every existing callsite that used to pass
  `hUserBodyHalt` no longer needs it.

## Worker Spawning Notes

When this PR is converted into actual work via orchestrator workers
(`mcp__orchestrator__batch_create_workers`):

- **Filesystem isolation caveat (carried over from PR #1822 boss notes):**
  worker containers do not share the host's worktree paths; they need their
  own git checkout. The "working_directory" parameter is a hint, not a mount.
  Workers should `git clone` from the canonical remote and push their own
  feature branch (e.g. `worker/g1-s5-A1`), then the boss merges.
- **Per-wave kickoff:** boss waits for the upstream wave to land on `main`
  before spawning the next wave's workers, so each worker rebases from a
  green base.
- **Conflict avoidance:** every node above modifies a disjoint set of files
  (or non-overlapping sections of `EndToEnd.lean`), so within a wave the
  workers should never conflict.
- **Resource budget per worker:** expect ~30–60 min per layer-A/B/D node,
  ~15–30 min per Ei/Fi node, ~30–60 min for G. The `claude-opus-4-7` backend
  at "high" effort was used in the PR #1822 trial run.

## References

- `docs/NATIVE_EVMYULLEAN_TRANSITION.md` — full plan with proof sketches,
  constructor signatures, and harness-lemma signatures for each step.
- `docs/NATIVE_EVMYULLEAN_DONE_GRAPH.md` — overall transition graph.
- `docs/NATIVE_EVMYULLEAN_FULL_TRANSITION_DONE.md` — completion contract.
- PR #1822 — shipped foundation (S1–S4 + public-surface retarget).

## Implementation Research Addendum

This section captures concrete code-level facts gathered during a follow-up
review of the post-#1822 tree. It is intended to compress onboarding cost for
future implementers (human or agent).

### Verified shipped artifacts (post-#1822)

All four leaf Revived constructors landed in
`Compiler/Proofs/EndToEnd.lean`:

| Leaf                                                                                       | Line   |
|--------------------------------------------------------------------------------------------|--------|
| `NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived.of_empty_body`                 | (in #1822 — present pre-1822 baseline) |
| `NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived.of_leave_body`                 | 16822  |
| `NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived.of_block_leave`                | 16936  |
| `NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived.of_block_empty`                | 17048  |
| `NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived.of_singleton_comment`          | 17163  |

The success-bridge chain is shipped only for `of_empty_body`:

| Chain                                                       | Line   |
|-------------------------------------------------------------|--------|
| `NativeGeneratedSelectorHitSuccessBridge.of_empty_body`     | 21401  |

**Correction to the plan above:** the E2 chain
(`NativeGeneratedSelectorHitSuccessBridge.of_leave_body`) is **not**
pre-existing — the original plan was wrong about that. E2 must be authored
alongside E3, E4, E5.

### Chain-wiring template (for E2–E5, E6, E7)

Each new `NativeGeneratedSelectorHitSuccessBridge.of_<leaf>` follows this
shape, derived from the working `of_empty_body` chain at line 21401:

```lean
private theorem NativeGeneratedSelectorHitSuccessBridge.of_<leaf>
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (irContract : IRContract) (tx : IRTransaction) (state : IRState)
    (observableSlots : List Nat)
    (hcompile : CompilationModel.compile spec selectors = Except.ok irContract)
    (hSelectorRange : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelectorsRange : ∀ selector, selector ∈ selectors → selector < ...)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hShape : <body-shape predicate for the leaf>) :
    NativeGeneratedSelectorHitSuccessBridge irContract tx state observableSlots :=
  -- Option A (used by of_empty_body): convert leaf to user-body exec bridge
  --   first, then go through of_user_body_exec_bridge_atFuel_revived.
  -- Option B (probably needed for the new leaves): use
  --   NativeGeneratedSelectorHitSuccessBridge.of_selected_user_body_exec_only_and_preserves
  --   at EndToEnd.lean:21333 with both
  --     - the matching Revived leaf constructor, and
  --     - a NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel
  --       obtained from .of_nativeStmtsWriteNames_not_mem
  --       (EndToEnd.lean:17574) on the body shape.
  …
```

**Concrete observation:** every new leaf except `of_empty_body` produces an
`ExecOnlyBridgeAtFuelRevived` (the *Selected* variant). To reach the success
bridge, route through
`NativeGeneratedSelectorHitSuccessBridge.of_selected_user_body_exec_only_and_preserves`
(`EndToEnd.lean:21333`) which requires a paired
`NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel`.

### Preservation-bridge construction (the actual blocker for E2–E5)

The paired preservation premise is produced via
`NativeGeneratedSelectorHitUserBodyPreservesBridgeAtFuel.of_nativeStmtsWriteNames_not_mem`
(`EndToEnd.lean:17574`). For each leaf body shape:

| Body shape         | Lowered native shape | Per-stmt preservation lemma in `EvmYulLeanNativeHarness.lean`         |
|--------------------|----------------------|------------------------------------------------------------------------|
| `[]`               | `[]`                 | trivial (empty list)                                                   |
| `[.leave]`         | `[.Leave]`           | needs a `NativeStmtPreservesWord_leave` lemma (not yet shipped)         |
| `[.block []]`      | `[.Block []]`        | `NativeStmtPreservesWord_empty_block` at `EvmYulLeanNativeHarness.lean:14335` ✅ |
| `[.block [.leave]]`| `[.Block [.Leave]]`  | needs `NativeStmtPreservesWord_block` applied to a single `Leave` child |
| `[.comment text]`  | `[.Block []]`        | `NativeStmtPreservesWord_lowerStmtGroupNativeWithSwitchIds_comment` at `EvmYulLeanNativeHarness.lean:14343` ✅ |

So the **per-statement preservation half** is **already shipped** for the
`[.block []]` and `[.comment]` shapes, **partially shipped** for the bare
`[.leave]` and `[.block [.leave]]` shapes (no top-level `Leave` preservation
lemma — needs a 4-line addition), and **not yet shipped** for any
`NativePreservableStraightStmts` prefix (Layer D's eventual responsibility).

The **freshness half** (matched temp name fresh in the lowered body) is
discharged by the same `nativeSwitchTempsFreshForNativeBodies` machinery
already used at `EndToEnd.lean:21088`. Each new chain needs to plumb a
freshness witness through; the easiest path is to follow the pattern of the
`hSwitchFresh` argument in
`of_selected_user_body_exec_only_and_bridgedStraightStmts_mapping_switchFresh`
(`EndToEnd.lean:21075`).

### Layer A — IR-side lemmas, concrete file location

All three Layer A lemmas (`A1`, `A2`, `A3`) belong in
`Compiler/Proofs/IRGeneration/IRInterpreter.lean` (4762 lines). The existing
`execIRStmts` definition + supporting projection lemmas live there. There is
no existing per-`NativePreservableStraightStmt` companion lemma — the
straight-stmt induction is the new work.

### Layer B — Harness-side lemmas, concrete file location

`Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean` already
contains the leaf-only harness lemmas (`exec_block_leave_ok_add_ten` etc.).
The generalised
`exec_block_lowerStmtsNativeWithSwitchIds_with_leave_ok_eq_of_NativeBlockPreservesWord`
(B1) and its no-leave cousin (B2) are net-new. The general append helper (B3)
should be stated as:

```lean
theorem exec_block_append_eq_of_continue
    (fuel : Nat) (xs ys : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state mid : EvmYul.Yul.State)
    (hxs : EvmYul.Yul.exec fuel (.Block xs) codeOverride state = .ok mid) :
    ∀ suffixFuel,
      EvmYul.Yul.exec (fuel + suffixFuel) (.Block (xs ++ ys)) codeOverride state
        = EvmYul.Yul.exec suffixFuel (.Block ys) codeOverride mid := by
  …
```

Note: the `.Block` reduction rule in `EvmYul.Yul.exec` resets the leave flag
on entry and threads it through children, so B3 needs to be careful with the
`.continue`/`.leave` flag — likely two variants are needed in practice.

### Layer D — Revived constructors, exact file insertion point

D1 and D2 belong **immediately after** `of_singleton_comment` at
`EndToEnd.lean:17163` (i.e. right after the last shipped leaf in the same
section). They must:

- Take a `NativePreservableStraightStmts` witness for the prefix.
- For D1, additionally accept a `Leave` terminator (same as `of_leave_body`'s
  finishing argument).
- For D2, take a `fn.returnVars = []` witness so the fall-through projects to
  `.continue`-shaped final state.

The matching source-side helpers
(`nativeResultsMatchOn_execIRFunction_nativePreservableStraightStmts_leave_body_markedPrefix`
and its fall-through cousin) follow the template of
`nativeResultsMatchOn_execIRFunction_leave_body_markedPrefix` and
`nativeResultsMatchOn_execIRFunction_block_leave_body_markedPrefix` already
in the same file.

### Layer F — `_with_label_prefix` strategy

Each `_with_label_prefix` variant operates at the **success-bridge layer**:
given a body of shape `.comment label :: <leaf body>`, it strips the leading
comment using the **already shipped** harness lemma
`exec_block_noop_block_head_eq` (search the harness file for the name) and
delegates to the bare-leaf Ei chain.

**Critical observation:** F1 (label prefix on `of_empty_body`) and E5
(`of_singleton_comment`) describe **exactly the same** dispatched-body shape
`[.comment text]`. F1 is therefore redundant once E5 lands and can be dropped
from the plan; only F2..F5/F6/F7 remain as new theorems.

### Layer G — premise drop, exact call-site list

`hUserBodyHalt` appears in the signature of
`compile_preserves_native_evmYulLean_of_compile_ok_supported_generated_callDispatcher`
in `EndToEnd.lean`. Downstream call sites that pass it in:

```
$ grep -rn "hUserBodyHalt\|userBodyHalt" \
    Compiler/Proofs/EndToEnd.lean \
    Compiler/Proofs/EvmYulLeanRetarget.lean \
    Compiler/Proofs/SimpleStorage*.lean
```

This produces the **complete list** of touch sites the G-worker must update.
The G commit's lake-build smoke test is: every existing call site that
discharged `hUserBodyHalt` via a body-shape case split now closes through one
of E2–E7 / F2–F7.

### Realistic effort estimate (revised)

PR #1822 shipped ~3 working days of senior-engineer Lean work for S1–S4
(four leaf constructors + chain wiring + retarget infrastructure). The S5–S8
delta requires:

- **A** (3 IR-side lemmas, ~20-constructor induction): 1–2 days
- **B** (3 harness lemmas, careful `.Block` reduction reasoning): 1–2 days
- **D1+D2** (two Revived constructors + two source helpers): 1 day
- **E2–E7** (six chain wirings + freshness plumbing): 1–2 days
- **F2–F7** (six label-prefix variants): 0.5–1 day
- **G** (premise drop + call-site sweep): 0.5 day

**Total: 5–9 senior-engineer days**, not parallelizable beyond the 4-wave DAG
above (because each wave's downstream layer mechanically depends on the
upstream theorems being elaborated and in scope).

This effort estimate is **not compatible with a single autonomous coding
session**; the orchestrator-worker approach (PR #1822 trial) repeatedly
stalled or fabricated phantom branches under the same scope. The pragmatic
path forward is for a human engineer (or a sequence of bounded agent
sessions, each with its own PR for one DAG node) to land the layers
incrementally.

## Implementation status & known issue with Layer A's predicate (May 2026)

**Layers shipped on the PR branch (`native-evmyullean-g1-s5-s8-followup`):**
- Layer B (B1, B2, B3) — commit `8b9077ab`. B2 is degenerate
  (`simpa [List.append_nil] using hPre`); D2 will likely need a stronger B2.
- Layer A (A1, A2, A3) — commits `1fdab2b2` then `ade52b0c`. The first
  commit shipped a vacuous `IRStmtPreservesObs` predicate (required strict
  storage AND events equality, false for sstore/log/etc). The second commit
  weakened it to just `execIRStmt _ state stmt = .continue state'`.

**Remaining issue with the weakened predicate:**

Even after the weakening, `IRStmtPreservesObs` is still not satisfied
*unconditionally* for most `NativePreservableStraightStmt` constructors.
Reasons (visible in `IRInterpreter.lean:execIRStmt`):

1. `letMany _ _` unconditionally returns `.revert state` in IR (IR's
   semantics for `.letMany` is currently a stub revert).
2. `let_`, `assign`, all `expr_*` constructors that take expression args
   (`sstore`, `mstore`, `tstore`, `log0..4`, `calldatacopy`,
   `returndatacopy`, etc.) return `.revert` when their expressions
   fail to evaluate. The predicate quantifies over ALL states, so it
   only holds for stmts whose expressions evaluate in every state —
   essentially literals and well-bound references only.
3. The 3 explicit terminators (`expr_stop`, `expr_return`, `expr_revert`)
   are excluded by the prefix-then-`.leave` shape but the predicate has
   no way to reflect that.

So the cross-cast lemma `IRStmtPreservesObs.of_nativePreservableStraightStmt`
that D1 was supposed to use is provable ONLY for `.comment text`. For
everything else, D1 needs additional witnesses (state-relative
evaluability) or a different decomposition entirely.

**Recommended path for the next implementer:**

The cleanest correct shape is a state-relative predicate:

```lean
def IRStmtPreservesObs (stmt : YulStmt) (state : IRState) : Prop :=
  ∀ fuel, ∃ state', execIRStmt (fuel + 1) state stmt = .continue state'
```

Then A1/A2 thread state through the inductive hypothesis. The cross-cast
becomes "given a NativePreservableStraightStmt and a witness that all
intermediate states evaluate the stmt's expressions, IRStmtPreservesObs
holds at each step." For compiled IR this is true because the compiler
guarantees variable bindings; this fact lives in the source-side helpers
already templated as `nativeResultsMatchOn_execIRFunction_*_markedPrefix`.

**Substrate caveat:** during the May 2026 attempts, the orchestrator-worker
substrate hit `orphan_no_runner` and freeze failures on 4/4 spawn attempts
for Layer D and Layer EF, with no convergence in this session. Direct
implementation across multiple turns is the only working path until the
substrate (sandboxed.sh) is fixed.

## Stage 2 Plan (after #1826 foundation merge)

The `_revived` foundation is now landed in main (#1826). Stage 2 carries
the remaining Layer D / E / F / G work in this stacked PR.

### Stage 2 scope (all deferred from #1826)

- **D1 / S5**: `NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived.of_nativePreservableStraightStmts_leave`
  + new source-side helper
  `nativeResultsMatchOn_execIRFunction_nativePreservableStraightStmts_leave_body_markedPrefix`
- **D2 / S6**: `NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived.of_bridgedStraightStmts_falling_through`
  + new source-side helper
  `nativeResultsMatchOn_execIRFunction_bridgedStraightStmts_falling_through_body_markedPrefix`
- **E2/E4/E6/E7 / S7**: success-bridge wiring via `_revived` cascade
- **F2/F4/F6/F7**: label-prefix variants
- **G / S8**: drop `hUserBodyHalt` premise

### Architectural prerequisite

D1 and D2 both require a per-`BridgedStraightStmt`-constructor IR↔native
observation-equivalence theorem that does not currently exist as generic
infrastructure. The existing concrete-body helpers (e.g.
`store0_calldataload4_stop_markedPrefix`) hand-roll their own equivalence
inline. Stage 2's first task is to build the generic compositional
theorem (~500-1000 LoC of inductive proof per direction).

### Stage 2 sequencing

1. Build the per-`BridgedStraightStmt` IR↔native observation correspondence
2. D2 (simpler — falling-through case)
3. D1 (preStmts ++ [.leave] case)
4. E2/E4/E6/E7 success-bridge cascade (Path B chains using `_revived`)
5. F2/F4/F6/F7 label-prefix variants
6. S8 dispatcher refactor

### Stage 2 progress (2026-05-14)

**Shipped degenerate slots** (hOnlyEmpty narrowing — preStmts = []):

- D1/S5 degenerate (`193537a5`), D2/S6 degenerate (`7b9c2e86`)
- E7 degenerate (`c272db72`) + 5-commit `_revived` Preserves chain
- E2/E4/E6 SuccessBridge slots (`f1c087fc`) — conditional on
  `LeaveAwareCallDispatcherContinuation`
- S8 `_via_result` private variant (`e0dd38ad` + `cebb0325`)
- F2/F4/F6 direct (`62f662ea` + `b4863167`), F7 via E3 delegation
  (`eb9b9735` + `a52accfd`)

**Parallel `_revived` upstream chain** (so the OLD-form
`NativeBlockPreservesWord` is mirrored end-to-end on the dispatcher result
stack — discharges `LeaveAwareCallDispatcherContinuation` unconditionally):

- `NativeBlockPreservesWord_revived_nativeRevertZeroZero` (`b89b43cb` +
  `9ba14c3d` refactor) — vacuity leaf
- `NativeStmtPreservesWord_revived_if_of_cond_preserves_reviveJump`
  (`0b4151d6`) — takes a `reviveJump`-stated cond premise
- `NativeBlockPreservesWord_revived_switchCaseBody_payable_of_user_body`
  (`b002443a` + `35e998f5` — drops `hCondReviveJump`)
- `NativeBlockPreservesWord_revived_switchCaseBody_nonpayable_of_user_body`
  (`b5410c1a` + `35e998f5` — drops both cond premises)

### Stage 2 progress (2026-05-15)

**Universal-input cond-reviveJump discharge** ✓ (DoD-4 closed):

- `eval_lowerExprNative_lt_calldatasize_fuel` (state-generic, fuel ≥ 8)
- `eval_lowerExprNative_lt_calldatasize_fuel_ge_6` (tight, fuel ≥ 6)
- `eval_lowerExprNative_callvalue_fuel` (state-generic, fuel ≥ 5)
- `eval_lowerExprNative_callvalue_fuel_ge_2` (tight, fuel ≥ 2)
- `eval_lt_calldatasize_lit_preserves_reviveJump` — UNIVERSAL (any fuel,
  any state form), splits fuel < 6 (vacuous, `maxHeartbeats 4M`) vs ≥ 6
- `eval_callvalue_preserves_reviveJump` — UNIVERSAL similarly
- Both `_revived_switchCaseBody_*` now apply the universal discharge
  internally; `hCondReviveJump`/`hCallvalueReviveJump`/`hCalldataReviveJump`
  premises dropped.

Commits: `ce401bf0` (state-generic foundation), `b0611174` (callvalue
universal), `a2e91c49` (lt-calldatasize universal), `35e998f5` (drop
cond premises from `_revived_switchCaseBody_*`).

**Polish (DoD-5) ✓ COMPLETE**:
- `EvmYulLeanRetarget.lean` (1631 LoC) deleted (`2eac7c6d`)
- 9 more legacy modules deleted in `0751d4ac`
  (Preservation, StatementEquivalence, Equivalence, Codegen, Lemmas in
  YulGeneration/; AdapterCorrectness, NativeSmokeTest,
  NativeDispatchOracleTest in YulGeneration/Backends/; ReferenceOracle/Semantics)
  plus the two MacroTranslate{InvariantTest,RoundTripFuzz} legacy regression
  files (1240 + 389 LoC).
- 7058 lines removed total.
- CI plumbing cleanup (`6307373a`, `a563505a`, `c3ffd809`): verify.yml
  macro-fuzz job removed, fork-conformance path filters scrubbed, sync spec
  updated, dependent Python scripts and tests adjusted.
- Legacy fuel-based executor references: 0. `git grep` returns nothing.
- Final scrub (`aafc0e26`): all `legacyExecYulFuel` mentions removed from
  TRUST_ASSUMPTIONS.md, INTERPRETER_FEATURE_MATRIX.md,
  NATIVE_EVMYULLEAN_TRANSITION.md, NATIVE_EVMYULLEAN_G1_FOLLOWUP_PLAN.md,
  VERIFICATION_STATUS.md, check_lean_hygiene.py, check_proof_length.py,
  test_check_lean_hygiene.py — DoD-5's `git grep -n legacyExecYulFuel = 0`
  strictly satisfied.

**DoD-6 ✓** sorry count 5 ≤ upstream/main 7; axiom count 0 = 0.
**DoD-7 ✓** `lake clean && lake build` green (5m12s).
**DoD-8 ✓** `make check` green (1m41s).
**DoD-10 ✓** TRUST_ASSUMPTIONS.md / AUDIT.md / AXIOMS.md updated (`5d1010d1`).

### Remaining (DoD-1, DoD-2, DoD-3)

**Per-`BridgedStraightStmt` framework** — REMAINING LONG POLE (~2–4 weeks
standalone). For each of ~20 statement constructors in
`NativePreservableStraightStmt`, prove that IR-side execution and
native-generated execution are observationally equivalent on storage slots
and events. Until shipped, D1/D2/E6/E7 strengthening blocked behind the
`hOnlyEmpty : preStmts = []` narrowing.

**Parallel `_revived` dispatcher continuation provider** — REMAINING. The
`LeaveAwareCallDispatcherContinuation` predicate (EndToEnd.lean:19858) is
required by E2/E4/E6/E7 and F2/F4/F6/F7. Building this is a parallel
copy-modify of `nativeGeneratedCallDispatcherResult_selector_hit_ok_matchesIR_forall_of_compile_ok_supported`
(~700 LoC), but the proof body needs `_revived` semantics threaded through
the dispatcher chain. Estimated 3–7 days standalone; blocked on the per-stmt
observation framework for the user-body preservation discharge of Leave-
ending bodies (the OLD-form provider's NativeBlockPreservesWord fails on
Leave-ending bodies because OLD's `final[name]!` returns `default` for
Checkpoint Leave states — see memory `yul-state-lookup-bracket-vs-lookup`).

**Conflicts**: upstream main absorbed twice (merge commits `60d38ba8` and
`3358dc56`) — currently 0 commits behind upstream/main.
