# IR Storage Refactor — Phase 1 Plan

Phase 1 of [`IR_STORAGE_UINT256_REFACTOR.md`](IR_STORAGE_UINT256_REFACTOR.md): flip
`IRStorageWord` from its Phase-0 `abbrev := Nat` surface to a `UInt256`-backed
representation, and audit every former `Nat → Nat` callsite that flowed through
`IRState.storage`.

This file is the working scaffold for the Phase 1 PR. It is intentionally a
plan-only document so the PR opens against a green build; the actual carrier
flip lands in subsequent commits on this branch.

## Entry state

- `Compiler/Proofs/IRGeneration/IRStorageWord.lean` defines
  `abbrev IRStorageWord := Nat` plus `ofNat` / `toNat` / `toUInt256` helpers
  and round-trip lemmas (PR #1753, Phase 0).
- `IRState.storage : Nat → IRStorageWord` is rfl-identical to `Nat → Nat`
  under the abbrev, so the Phase 0 retype required no callsite changes.
- The public theorem `simpleStorage_endToEnd_native_evmYulLean` retains
  `hRetrieveHit` and `hStoreHit` as explicit hypotheses (#1743 commit
  `fe63b826`).

## Phase 1 deliverables

1. Replace `abbrev IRStorageWord := Nat` with a structurally-bounded
   representation — preferred form: `def IRStorageWord := UInt256` (or
   a single-field structure wrapping `UInt256` if `def` opacity proves
   awkward in proof contexts).
2. Update `IRStorageWord.ofNat` / `toNat` so that `ofNat n = ofNat (n % UInt256.size)`
   holds definitionally on the new carrier; expose the masking lemma.
3. Update the IR interpreter `sload` / `sstore` semantics in
   `Compiler/Proofs/IRGeneration/IRInterpreter.lean` to read and write through
   the typed helpers rather than treating the carrier as raw `Nat`.
4. Audit log (table below) — every callsite that used to touch
   `IRState.storage : Nat → Nat` must be inspected, marked `safe` (no value
   semantics affected) or `migrate` (needs an explicit `ofNat` / `toNat` call),
   and its outcome recorded.
5. Confirm `lake build` clean and every existing per-contract spec proof in
   `Contracts/<Name>/Proofs/` still passes (no spec regressions).

## Audit log

| Callsite | File:Line | Treatment | Notes |
|----------|-----------|-----------|-------|
| `IRStorageWord` carrier | `Compiler/Proofs/IRGeneration/IRStorageWord.lean` | migrate | Flipped from `abbrev := Nat` to `@[reducible] def := UInt256`. Added `OfNat`, `Inhabited` instances and reproved round-trip lemmas (`toNat_ofNat = n % UInt256.size`, `ofNat_toNat = w`, `toNat_lt_size`). |
| `abstractStoreMappingEntry` | `Compiler/Proofs/MappingSlot.lean:83` | migrate | Wraps `value : Nat` via `IRStorageWord.ofNat` inside the helper; simp lemma `abstractStoreMappingEntry_eq` updated to match. |
| `abstractStoreStorageOrMapping` | `Compiler/Proofs/MappingSlot.lean:95` | migrate | Wraps `value : Nat` via `IRStorageWord.ofNat`; simp lemma `abstractStoreStorageOrMapping_eq` updated. |
| `evalBuiltinCallWithContext` (sload) | `Compiler/Proofs/YulGeneration/ReferenceOracle/Builtins.lean:58` | migrate | Projects `abstractLoadStorageOrMapping storage slot : IRStorageWord` back to `Nat` via `.toNat` for the `Option Nat` return. |
| `evalBuiltinCallViaEvmYulLean` (sload) | `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanAdapter.lean:1064` | migrate | Same `.toNat` projection on the EVMYulLean adapter sload branch. |
| `IRInterpreter.evalIRStatementWithBackend` | `Compiler/Proofs/IRGeneration/IRInterpreter.lean` | safe | All `state.storage` reads go through `abstractLoadStorageOrMapping`, all writes go through `abstractStoreStorageOrMapping` / `abstractStoreMappingEntry`, so the helper-internal wrapping covers every callsite without changes here. Initial-state literal `fun _ => 0` continues to elaborate via the `OfNat IRStorageWord 0` instance. |
| `EvmYulLeanBridgeLemmas` | `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean` | safe | Builtin-equivalence lemmas thread `storage : Nat → IRStorageWord` as a parameter but never inspect the value; survive carrier flip without edits. |
| Per-contract specs `Contracts/*/Proofs/` | (across the tree) | safe | Spec-side proofs reason over `IRState`/`abstractLoad…` API surface; no callsite touches the raw carrier. `lake build` + `make check` (600 tests) clean post-flip. |

## Risks tracked from the parent doc

- Spec drift on `decide`-style spec proofs that pattern-matched on raw `Nat`
  storage values. Mitigation: keep helper API stable, expose `Nat`-shaped
  re-exports at the spec boundary if needed.
- `UInt256` arithmetic is heavier than `Nat` for kernel reduction. If a
  benchmark regresses, expose dedicated `simp` lemmas before relaxing the
  carrier.

## Exit criteria

- `IRStorageWord` is no longer an `abbrev` for `Nat`.
- `lake build` clean.
- `make check` clean.
- Every `Contracts/*/Proofs/` spec theorem unchanged (no signature drift).
- Public theorem `simpleStorage_endToEnd_native_evmYulLean` still carries
  `hRetrieveHit` and `hStoreHit` premises — Phase 1 does not yet discharge
  them. That work is Phase 2 / Phase 3.

## Status

Carrier flip implemented. `IRStorageWord` is now `@[reducible] def := UInt256`
with `OfNat` / `Inhabited` instances and the round-trip lemmas restated for the
new carrier. Downstream callsites have been migrated (helpers wrap `Nat → IRStorageWord`
internally; sload sites project via `.toNat`). `lake build` clean, `make check`
green (600 tests). `hRetrieveHit` / `hStoreHit` remain on
`simpleStorage_endToEnd_native_evmYulLean`; their discharge is Phase 2 / Phase 3.
