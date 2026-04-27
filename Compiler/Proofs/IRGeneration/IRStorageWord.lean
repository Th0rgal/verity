/-
  IRStorageWord: typed-storage helper surface for the IR storage carrier.

  This module is **Phase 0** of the IR storage type refactor described in
  `docs/IR_STORAGE_UINT256_REFACTOR.md`. It introduces a type alias plus
  canonical injection / projection helpers and round-trip lemmas, *without*
  changing the underlying carrier or any existing callsite.

  Phase 0 goals (this PR):
  - introduce `IRStorageWord`, currently `Nat`-backed,
  - introduce `IRStorageWord.ofNat`, `IRStorageWord.toNat`, and
    `IRStorageWord.toUInt256`,
  - prove the obvious round-trip lemmas so future migrations can use them.

  Phase 1 (follow-up PR):
  - flip `IRStorageWord` to a `UInt256`-backed representation,
  - migrate `IRState.storage : Nat → Nat` to use this helper surface,
  - audit every site that produced an unbounded value into storage.

  Phase 2 / Phase 3:
  - discharge `simpleStorageNativeRetrieveHitBridge` and
    `simpleStorageNativeStoreHitBridge` by reduction through the bounded
    carrier, then drop the corresponding hypotheses from
    `simpleStorage_endToEnd_native_evmYulLean`.

  The full plan and acceptance signals live in
  `docs/IR_STORAGE_UINT256_REFACTOR.md`.
-/

import EvmYul.UInt256

namespace Compiler.Proofs.IRGeneration

open EvmYul

/-- The carrier of a single IR storage slot value.

    Phase 0: `IRStorageWord := Nat`. This is the current behavior of
    `IRState.storage`, exposed through a typed alias so Phase 1 can swap
    the representation without touching callsites.

    Phase 1 will redefine this as a `UInt256`-backed bounded type.

    Treat this as opaque from callers: always go through `ofNat` /
    `toNat` / `toUInt256` rather than relying on the alias being `Nat`. -/
abbrev IRStorageWord : Type := Nat

namespace IRStorageWord

/-- Inject a `Nat` value into `IRStorageWord`.

    Phase 0: identity. Phase 1: `% UInt256.size`. -/
@[inline] def ofNat (n : Nat) : IRStorageWord := n

/-- Project an `IRStorageWord` back to `Nat`.

    Phase 0: identity. Phase 1: `UInt256.toNat`. -/
@[inline] def toNat (w : IRStorageWord) : Nat := w

/-- Project an `IRStorageWord` to the EVMYulLean `UInt256` representation.

    This is the projection used by the native state bridge. Phase 0
    truncates the underlying `Nat` by `% UInt256.size` exactly as
    `UInt256.ofNat` does today; Phase 1 will make this projection lossless
    by construction. -/
@[inline] def toUInt256 (w : IRStorageWord) : UInt256 := UInt256.ofNat w

/-! ## Round-trip lemmas

    These hold in Phase 0 by definitional equality and are stated up
    front so Phase 1's flip can preserve them as the migration contract. -/

@[simp] theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n := rfl

@[simp] theorem ofNat_toNat (w : IRStorageWord) : ofNat w.toNat = w := rfl

end IRStorageWord

end Compiler.Proofs.IRGeneration
