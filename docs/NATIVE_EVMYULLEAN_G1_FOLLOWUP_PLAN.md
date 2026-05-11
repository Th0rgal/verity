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
2. No opt-in legacy machinery
   (`legacyExecYulFuel`, `EvmYulLeanRetarget.lean`, reference-oracle composition)
   on the proof chain for the supported fragment.
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
