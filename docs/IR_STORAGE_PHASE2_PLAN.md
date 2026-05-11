# IR Storage Refactor — Phase 2 Plan

Phase 2 of [`IR_STORAGE_UINT256_REFACTOR.md`](IR_STORAGE_UINT256_REFACTOR.md)
originally tracked discharging the retrieve-hit fuel-wrapper bridge after the
`UInt256`-bounded IR storage carrier landed.

Status update: this plan has been superseded for the public native path. The
public `simpleStorage_endToEnd_native_evmYulLean` theorem now consumes the
direct native-vs-IR `simpleStorageNativeRetrieveHitMatchBridge_proved` proof
through `simpleStorageNativeCallDispatcherMatchBridge_of_per_case`. The older
retrieve-hit compatibility theorem has been
removed with the obsolete SimpleStorage fuel-wrapper bridge surface.

This file is the working scaffold for the Phase 2 PR. It is plan-only so the
PR opens against a green build.

## Prerequisite

Phase 1 (#1754) must land first. Phase 2 is a no-op without the bounded carrier
because the storage-modulo gap is what blocks the bridge.

## Why this becomes provable after Phase 1

After Phase 1, every value flowing through `IRState.storage` is `UInt256`-bounded
by construction. That eliminates the two structural blockers documented in the
parent transition note:

1. **Storage-value gap on the projected `finalStorage`.** Native projection
   applies `% UInt256.size`; the IR oracle reads raw `Nat`. Once the IR carrier
   is `UInt256`, the modulo becomes the identity on every observable slot —
   the two sides agree definitionally up to the `IRStorageWord.toNat ∘ ofNat`
   round-trip lemma exposed by Phase 0.
2. **Return-value gap from `mstore` byte buffer.** The retrieve-hit return is
   built by `mstore` of a `UInt256` and re-extracted by `projectHaltReturn` from
   `state.sharedState.H_return`. With the IR oracle's pre-`mstore` value already
   `UInt256`-bounded, the `mstore` step is no longer lossy: the same 32 bytes
   land in the buffer on both sides.

## Phase 2 deliverables

1. Lemma `simpleStorageNativeRetrieveHitMatchBridge_proved` — analogous to the
   direct selector-miss native match proof.
2. Replace the explicit `hRetrieveHit` premise on
   `simpleStorage_endToEnd_native_evmYulLean` with the proved lemma.
3. `PrintAxioms` for the public theorem no longer lists the retrieve-hit
   bridge.
4. `Contracts/SimpleStorage/Proofs/` unchanged.

## Proof obligation outline

The current bridge statement (see `Compiler/Proofs/EndToEnd.lean`) reduces, after
the carrier flip, to:
- The native dispatcher's hit-case body executes the `sload` against
  `SharedState.storage`, returns its `UInt256` payload, `mstore`s it to memory
  at the canonical return offset, and halts with `H_return` covering those 32
  bytes.
- The IR oracle's hit-case path computes the same `UInt256` value via
  `IRStorageWord.toUInt256 ∘ IRState.storage`.
- After Phase 1, both sides reduce to the same `UInt256` and therefore to the
  same projected `Nat`. The bridge closes by `rfl` modulo the round-trip
  lemmas already exported from `IRStorageWord.lean`.

## Risks

- The native side's `mstore`/`H_return` chain still requires byte-level
  alignment lemmas at the `projectHaltReturn` boundary. Those lemmas exist
  for the selector-miss case; the retrieve-hit reuse must match offset and
  length conventions exactly.
- If Phase 1 leaves any spec theorem reading raw `Nat` from storage at the
  spec boundary, the retrieve-hit lemma will need a `toNat`-shape adapter.

## Exit criteria

- `simpleStorageNativeRetrieveHitMatchBridge_proved` lands and is invoked at the
  call site of the former `hRetrieveHit` premise.
- `simpleStorage_endToEnd_native_evmYulLean` no longer carries `hRetrieveHit`.
- `PrintAxioms` reflects the drop.
- `lake build` and `make check` clean.

## Status

Superseded for the public native SimpleStorage theorem. The direct retrieve-hit
proof is `simpleStorageNativeRetrieveHitMatchBridge_proved`; the generic
compatibility cleanup remains tracked in
[`NATIVE_EVMYULLEAN_TRANSITION.md`](NATIVE_EVMYULLEAN_TRANSITION.md).
