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

    Phase 1: `IRStorageWord := UInt256`. The carrier is a `UInt256`
    bounded by `UInt256.size = 2^256` by construction, exposed through
    a `@[reducible] def` so existing callsites that referred to
    `IRStorageWord` as a function codomain continue to elaborate.

    Treat this as opaque from callers: always go through `ofNat` /
    `toNat` / `toUInt256` rather than relying on the carrier being any
    particular numeric type. -/
@[reducible] def IRStorageWord : Type := UInt256

namespace IRStorageWord

/-- Inject a `Nat` value into `IRStorageWord` by reducing modulo
    `UInt256.size`. -/
@[inline] def ofNat (n : Nat) : IRStorageWord := UInt256.ofNat n

/-- Project an `IRStorageWord` back to `Nat`. The result is bounded by
    `UInt256.size` (see `toNat_lt_size`). -/
@[inline] def toNat (w : IRStorageWord) : Nat := UInt256.toNat w

/-- Project an `IRStorageWord` to the EVMYulLean `UInt256` representation.

    Lossless: with the Phase 1 carrier this is the identity. -/
@[inline] def toUInt256 (w : IRStorageWord) : UInt256 := w

/-- `OfNat` instance so storage initial values like `fun _ => 0`
    elaborate as `IRStorageWord`. -/
instance instOfNat (n : Nat) : OfNat IRStorageWord n := ⟨ofNat n⟩

instance : Inhabited IRStorageWord := ⟨ofNat 0⟩

/-! ## Round-trip lemmas -/

@[simp] theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n % UInt256.size := rfl

@[simp] theorem ofNat_toNat (w : IRStorageWord) : ofNat w.toNat = w := by
  cases w with
  | mk v =>
    cases v with
    | mk val isLt =>
      show UInt256.ofNat val = ⟨⟨val, isLt⟩⟩
      apply congrArg UInt256.mk
      apply Fin.ext
      show val % UInt256.size = val
      exact Nat.mod_eq_of_lt isLt

/-- Every `IRStorageWord` value is bounded by `UInt256.size`. -/
theorem toNat_lt_size (w : IRStorageWord) : w.toNat < UInt256.size := by
  cases w with
  | mk v => exact v.isLt

end IRStorageWord

/-- The carrier of an IR storage slot key.

    EVM storage is keyed by 256-bit words. Keeping IR storage keyed by raw
    `Nat` lets distinct IR slots alias when projected through EVMYulLean's
    `UInt256` storage map. `IRStorageSlot` makes that modulo behavior part of
    the IR model instead of a theorem-level precondition. -/
@[reducible] def IRStorageSlot : Type := UInt256

namespace IRStorageSlot

/-- Inject a `Nat` slot into the bounded storage-key carrier by reducing modulo
    `UInt256.size`. -/
@[inline] def ofNat (n : Nat) : IRStorageSlot := UInt256.ofNat n

/-- Project an `IRStorageSlot` back to `Nat`. -/
@[inline] def toNat (slot : IRStorageSlot) : Nat := UInt256.toNat slot

/-- Project an `IRStorageSlot` to the EVMYulLean `UInt256` representation. -/
@[inline] def toUInt256 (slot : IRStorageSlot) : UInt256 := slot

instance instOfNat (n : Nat) : OfNat IRStorageSlot n := ⟨ofNat n⟩

instance : Inhabited IRStorageSlot := ⟨ofNat 0⟩

@[simp] theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n % UInt256.size := rfl

@[simp] theorem toUInt256_ofNat (n : Nat) : (ofNat n).toUInt256 = UInt256.ofNat n := rfl

@[simp] theorem ofNat_toNat (slot : IRStorageSlot) : ofNat slot.toNat = slot := by
  cases slot with
  | mk v =>
    cases v with
    | mk val isLt =>
      show UInt256.ofNat val = ⟨⟨val, isLt⟩⟩
      apply congrArg UInt256.mk
      apply Fin.ext
      show val % UInt256.size = val
      exact Nat.mod_eq_of_lt isLt

theorem toNat_lt_size (slot : IRStorageSlot) : slot.toNat < UInt256.size := by
  cases slot with
  | mk v => exact v.isLt

theorem eq_of_toNat_eq {a b : IRStorageSlot} (h : a.toNat = b.toNat) : a = b := by
  rw [← ofNat_toNat a, ← ofNat_toNat b, h]

theorem toNat_ne_of_ne {a b : IRStorageSlot} (h : a ≠ b) : a.toNat ≠ b.toNat := by
  intro hnat
  exact h (eq_of_toNat_eq hnat)

end IRStorageSlot

end Compiler.Proofs.IRGeneration
