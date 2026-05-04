# IR Storage Type Refactor: `Nat → Nat` ⇒ `Nat → UInt256`

Tracking the structural refactor that originally targeted the retrieve-hit and
store-hit compatibility sub-bridges of the SimpleStorage native dispatcher.
The public native SimpleStorage path has since moved to the direct native-vs-IR
`simpleStorageNativeCallDispatcherMatchBridge_of_per_case` splitter, with
`simpleStorageNativeRetrieveHitMatchBridge_proved` and
`simpleStorageNativeStoreHitMatchBridge_proved` discharging those cases.

## Why this exists

The first executable instantiation of the native dispatcher bridge discharged
the selector-miss compatibility bridge but left retrieve-hit and store-hit
fuel-wrapper bridges as explicit hypotheses on the public theorem
`simpleStorage_endToEnd_native_evmYulLean`. That historical fuel-wrapper route
has been removed for SimpleStorage: the public native theorem consumes direct
match proofs for selector miss, retrieve hit, and store hit.

Those two cases cannot be discharged inside the current public theorem
signature because of a type-level mismatch:

- The Verity proof oracle `interpretYulRuntimeEvmYulLean` reads
  from `IRState.storage : Nat → Nat` (see
  [`Compiler/Proofs/IRGeneration/IRInterpreter.lean`](../Compiler/Proofs/IRGeneration/IRInterpreter.lean)).
  The carrier is unbounded.
- The native path executes against EVMYulLean's `SharedState`, whose
  storage carrier is `UInt256`. The native projection
  (`projectStorageFromState` → `extractStorage` → `.toNat` in
  [`EvmYulLeanNativeHarness.lean`](../Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean))
  therefore truncates every observed value by `% UInt256.size`.
- The retrieve-hit return value is computed by `projectHaltReturn` from 32
  bytes the native path wrote with `mstore` of a `UInt256`. The raw
  unbounded value has been destroyed at the `mstore` step and cannot be
  recovered from the returned byte buffer alone.

Adding a pre-state slot-bound hypothesis to the public theorem is rejected
by the transition design (the public hypothesis surface is intentionally
fixed). Routing an "expected return" through `projectResult` would make
the bridge tautological. The only resolution that closes both the
return-value and final-storage gaps without weakening the public theorem
is to bound `IRState.storage` (and the associated read/write paths) by
construction.

## Goal

Change the IR-side storage carrier from `Nat → Nat` to a `UInt256`-typed
carrier, so that:

- `IRState.storage slot` and the EVMYulLean `SharedState` storage slot
  agree on every observable slot up to a coercion that is provably
  injective on the IR side.
- The retrieve-hit `mstore` chain on the native side and the layer-3
  oracle's storage read produce the same 32 bytes / `UInt256` payload by
  reducing through a single bounded representation.
- The selector-miss bridge and any non-storage bridges remain unaffected.

## Non-goals

- Changing the EVMYulLean fork's storage representation. The refactor is
  on the IR side only.
- Changing `verity_contract` user-facing surface syntax. Any widening of
  what users can write should land in separate PRs.
- Touching transient storage / memory unless the same gap is observable
  there (memory is internally `mstore`-driven and already `UInt256`-flat
  in the byte buffer; transient storage is currently untouched by the
  failing bridges).

## Phased plan

The refactor is invasive enough that it must land in well-scoped phases.
Each phase ships independently, with `lake build` and `make check` green
at every step.

### Phase 0 — type alias and adapter surface

Introduce a typed alias `IRStorageWord` (initially `:= Nat`) with
canonical injection/projection helpers and migrate existing
`IRState.storage : Nat → Nat` consumers to call those helpers without
changing semantics. This is a no-op rename that makes Phase 1 a single
internal-type swap.

Deliverables:
- `Compiler/Proofs/IRGeneration/IRStorageWord.lean` — defines
  `IRStorageWord`, `IRStorageWord.ofNat`, `IRStorageWord.toNat`,
  `IRStorageWord.toUInt256`, plus the obvious round-trip lemmas.
- Migrate every direct `IRState.storage` field access through the new
  helpers; keep the underlying carrier `Nat` so no proof has to change.

Exit criteria: `lake build` clean; `simpleStorage_endToEnd_native_evmYulLean`
still has both `hRetrieveHit` and `hStoreHit` premises.

Status:
- Helper module `IRStorageWord.lean` landed (commit `5de766e2`).
- `IRState.storage` field retyped to `Nat → IRStorageWord` so the
  signature is already in the Phase-1-ready shape; with the current
  `abbrev IRStorageWord := Nat` this is rfl-identical to `Nat → Nat`,
  so no callsite needed updating.
- The "route every read/write through `IRStorageWord.ofNat` /
  `IRStorageWord.toNat`" deliverable is intentionally folded into
  Phase 1: under `abbrev` the routing is a no-op rename, and routing
  only becomes semantically meaningful once the abbrev is removed.

### Phase 1 — flip the carrier to `UInt256`

Change `IRStorageWord` from `Nat` to `UInt256` (or a structurally
equivalent bounded record). Audit every site that produced an unbounded
value into storage and add the (already-true on the supported fragment)
masking step. Update the IR interpreter's `sload`/`sstore` semantics to
go through the typed helpers.

Deliverables:
- Updated `IRStorageWord` with canonical `UInt256` representation.
- `IRInterpreter` updates so that every value entering / leaving the
  storage carrier is `UInt256`-bounded.
- Audit log of every former `Nat → Nat` callsite, listed in this doc.

Exit criteria: `lake build` clean; every existing per-contract spec
proof in `Contracts/<Name>/Proofs/` still passes (no spec regressions).

### Phase 2 — discharge retrieve hit

With storage values bounded by construction on the IR side, the native
projection's `% UInt256.size` truncation becomes the identity on the
relevant slot. The retrieve-hit return-value chain reduces because the
`mstore`'d native bytes and the IR-oracle return word agree.

Deliverables:
- Historical compatibility proof:
  `simpleStorageNativeRetrieveHitMatchBridge_proved`.
- Public native direct proof:
  `simpleStorageNativeRetrieveHitMatchBridge_proved`.
- `simpleStorage_endToEnd_native_evmYulLean` consumes the direct per-case
  splitter without a retrieve-hit premise.

Status: complete for the public native theorem. The compatibility proof remains
only for the generic fuel-wrapper/reference-oracle cleanup.

### Phase 3 — discharge store hit

Same argument as Phase 2 for the store-hit case: the written value
flows through bounded storage and the re-read of any other materialized
observable slot agrees. The calldata round-trip was already 32-byte
bounded, so the writeback case becomes mechanical.

Deliverables:
- Historical compatibility proof:
  `simpleStorageNativeStoreHitMatchBridge_proved`.
- Public native direct proof:
  `simpleStorageNativeStoreHitMatchBridge_proved`.
- `simpleStorage_endToEnd_native_evmYulLean` consumes the direct per-case
  splitter without a store-hit premise.

Status: complete for the public native theorem. The compatibility proof remains
only for the generic fuel-wrapper/reference-oracle cleanup.

### Phase 4 — generalize and retire the per-case bridge surface

Replace the per-contract SimpleStorage direct-match family with a generic,
dispatcher-shape-driven bridge so future contracts inherit discharge
automatically. The older non-`Match` SimpleStorage bridge family is
compatibility-only and should disappear with the generic
fuel-wrapper/reference-oracle cleanup.

Deliverables:
- Generic `nativeCallDispatcherBridge_of_typed_storage` lemma over the
  supported lowered-dispatcher fragment.
- `simpleStorage_endToEnd_native_evmYulLean` re-derived from the generic
  surface; no SimpleStorage-specific bridge file remains beyond the test
  harness.

## Acceptance signals

- `simpleStorage_endToEnd_native_evmYulLean` has no `hRetrieveHit` or
  `hStoreHit` premise and consumes
  `simpleStorageNativeCallDispatcherMatchBridge_of_per_case`.
- `PrintAxioms` includes the direct match proofs for the public native theorem;
  compatibility bridge proofs may remain only while the generic
  fuel-wrapper/reference-oracle family remains.
- `Contracts/SimpleStorage/Proofs/` spec theorems are unchanged.
- A second contract (e.g. Counter) lifts to the native theorem under the
  generic Phase-4 surface without contract-specific bridge code.

## Risks and rollback

- **Spec drift.** Phase 1's flip changes the IR storage carrier; any
  spec proof that implicitly relied on `Nat`-shaped storage must be
  updated. Mitigation: keep Phase 0's helper surface stable so spec
  proofs only see the helper API.
- **Performance.** `UInt256` arithmetic in the IR interpreter is heavier
  than `Nat` arithmetic for `decide`-style proof automation. Mitigation:
  expose `simp` lemmas that re-export bounded results as `Nat` only at
  the spec boundary.
- **Rollback.** Phase 0 is a pure rename; Phase 1 is the only
  destructive step. If Phase 1 hits an unexpected proof regression that
  cannot be repaired in the same PR, revert the Phase 1 commit and keep
  the helper surface in place for a later attempt.

## Out-of-scope follow-ups

- Memory carrier typing. Memory is currently `Nat → Nat` for similar
  reasons and benefits from the same treatment, but the failing bridges
  do not depend on it.
- Transient storage carrier typing. Same caveat.
- EVMYulLean fork changes. The refactor stays on the Verity side.

## See also

- [`NATIVE_EVMYULLEAN_TRANSITION.md`](NATIVE_EVMYULLEAN_TRANSITION.md)
  — the parent transition plan and the per-case bridge status section.
- [`Compiler/Proofs/EndToEnd.lean`](../Compiler/Proofs/EndToEnd.lean)
  — `simpleStorage_endToEnd_native_evmYulLean` and the
  `simpleStorageNative*Bridge` family.
- [`Compiler/Proofs/IRGeneration/IRInterpreter.lean`](../Compiler/Proofs/IRGeneration/IRInterpreter.lean)
  — the current `IRState.storage : Nat → Nat` definition.
