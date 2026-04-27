# IR Storage Refactor — Phase 3 Plan

Phase 3 of [`IR_STORAGE_UINT256_REFACTOR.md`](IR_STORAGE_UINT256_REFACTOR.md):
discharge `simpleStorageNativeStoreHitBridge` and drop the `hStoreHit` premise
from `simpleStorage_endToEnd_native_evmYulLean`. After Phase 3, the public
SimpleStorage native theorem has zero remaining bridge premises.

This file is the working scaffold for the Phase 3 PR. It is plan-only so the
PR opens against a green build.

## Prerequisites

- Phase 1 (#1754) — `UInt256`-bounded IR storage carrier.
- Phase 2 (#1755) — retrieve-hit bridge proved and `hRetrieveHit` removed.

## Why this becomes provable after Phase 1

The store-hit case has two distinct read paths and one write path:

1. **The sstore-written slot.** Calldata round-trip is unconditionally bounded
   to 32 bytes by the lowered dispatcher, so the WRITTEN value was already
   `UInt256`-bounded; no Phase 1 dependency for that arm.
2. **Re-read of any other materialized observable slot.** This is the same
   gap as Phase 2 — Phase 1's carrier flip closes it.
3. **Storage-state agreement after the write.** The native side mutates
   `SharedState.storage` at slot index `s`; the IR oracle mutates
   `IRState.storage` at the same index. Once both carriers are `UInt256`,
   the post-state functional extensionality argument over slots reduces
   identically on both sides.

## Phase 3 deliverables

1. Lemma `simpleStorageNativeStoreHitBridge_proved` — mirrors the Phase 2
   retrieve-hit lemma, with the additional sstore mutation argument.
2. Replace the explicit `hStoreHit` premise on
   `simpleStorage_endToEnd_native_evmYulLean` with the proved lemma.
3. `PrintAxioms` for the public theorem reports no remaining bridge premises
   beyond the trusted EVMYulLean builtin axioms.
4. `simpleStorageNativeCallDispatcherBridge_of_per_case` is the only
   surviving dispatcher surface and is fully closed.
5. `Contracts/SimpleStorage/Proofs/` unchanged.

## Proof obligation outline

After Phases 1 and 2, the store-hit bridge reduces to:

- The native dispatcher's hit-case body executes `sstore(slot, calldata-word)`
  on `SharedState.storage`, then halts. `H_return` is empty for the store
  case.
- The IR oracle's hit-case path applies the same functional update to
  `IRState.storage`.
- After Phase 1, both carriers are `UInt256`; the functional update agrees on
  every slot index by `Function.update`-style reasoning.
- The empty `H_return` matches trivially.

## Risks

- The `Function.update`-style equality proof requires decidable equality on
  the slot index. `Nat` provides it; the bounded carrier does not change the
  index type, only the value type — so this should remain mechanical.
- Any spec theorem that explicitly observes `IRState.storage` after a write
  may need a `Function.update_eq` rewrite at the spec boundary. Phase 1's
  audit log should already enumerate these sites.

## Exit criteria

- `simpleStorageNativeStoreHitBridge_proved` lands and is invoked at the
  call site of the former `hStoreHit` premise.
- `simpleStorage_endToEnd_native_evmYulLean` has zero remaining bridge
  premises.
- `PrintAxioms` reflects the drop.
- `lake build` and `make check` clean.

## After Phase 3

Phase 4 — generalize the per-case bridge surface to a dispatcher-shape-driven
generic so a second contract (e.g. Counter) lifts to the native theorem
without per-contract bridge code. That is intentionally out of scope for this
PR.

## Status

Plan-only. Implementation depends on Phases 1 (#1754) and 2 (#1755) landing
first.
