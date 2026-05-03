/-
  EvmYulLeanStateBridge: Type-level scaffolding for the Phase 2 state bridge
  between Verity's `YulState` and EVMYulLean's `SharedState .Yul`.

  This module defines the conversion functions needed to translate between
  Verity's flat execution state and EVMYulLean's account-map–based state.
  The conversion covers:

  1. **Variable bindings**: `List (String × Nat)` ↔ `VarStore` (Finmap)
  2. **Storage**: `Nat → Nat` ↔ `Storage` (RBMap UInt256 UInt256)
  3. **Execution environment**: flat fields ↔ `ExecutionEnv .Yul`
  4. **Block information**: flat fields ↔ `BlockHeader`

  Phase 2 proof obligations (tracked in issue #1722):
  - Round-trip lemma: `fromSharedState (toSharedState s) = s` for observable fields
  - Storage read commutation: `sload` in EVMYulLean = Verity's storage lookup
  - Storage write commutation: `sstore` in EVMYulLean = Verity's storage update
  - Environment field extraction: `caller`/`address`/`timestamp`/etc. agree

  Design constraints:
  - Verity's `storage : Nat → Nat` is infinite-domain; EVMYulLean's `Storage`
    is finite (RBMap). The bridge only observes slots that were written.
  - Verity has no account model; EVMYulLean has `AccountMap`. The bridge
    creates a minimal single-account state.
  - Verity's calldata is `List Nat` (32-byte words); EVMYulLean's is `ByteArray`.
    The bridge converts between word-level and byte-level representations.
-/

import Compiler.Proofs.YulGeneration.ReferenceOracle.Builtins
import Compiler.Proofs.YulGeneration.ReferenceOracle.State
import EvmYul.Yul.State
import EvmYul.SharedState
import EvmYul.State.Account
import EvmYul.UInt256
import EvmYul.Maps.StorageMap
import Batteries.Data.ByteArray
import Batteries.Data.RBMap.Lemmas

namespace Batteries
namespace RBNode

open RBColor

theorem All.setBlack' {p : α → Prop} {t : RBNode α}
    (h : t.All p) : t.setBlack.All p := by
  cases t <;> simp [setBlack]
  exact h

theorem find?_eq_none_of_all_ne {cut : α → Ordering} {t : RBNode α}
    (h : t.All (fun x => cut x ≠ Ordering.eq)) :
    t.find? cut = none := by
  induction t with
  | nil => rfl
  | node _ l x r ihl ihr =>
      rw [find?]
      split <;> rename_i hc
      · exact ihl h.2.1
      · exact ihr h.2.2
      · exact False.elim (h.1 hc)

theorem del_all_cut_ne {cmp : α → α → Ordering} {cut : α → Ordering}
    [Std.TransCmp cmp] [IsStrictCut cmp cut] :
    ∀ {t : RBNode α}, t.Ordered cmp →
      (t.del cut).All (fun x => cut x ≠ Ordering.eq)
  | nil, _ => by simp [del]
  | node _ a y b, ht => by
      rcases ht with ⟨hay, hyb, ha, hb⟩
      rw [del]
      split <;> rename_i hcut
      · have haAll := del_all_cut_ne (cmp := cmp) (cut := cut) ha
        have hy : cut y ≠ Ordering.eq := by simp [hcut]
        have hbAll : b.All (fun x => cut x ≠ Ordering.eq) := by
          apply hyb.imp
          intro x hyx hxeq
          have hlt : cut x = Ordering.lt := IsCut.lt_trans hyx.1 hcut
          cases hlt.symm.trans hxeq
        cases a with
        | nil =>
            simp [isBlack]
            exact ⟨hy, haAll, hbAll⟩
        | node c _ _ _ =>
            cases c <;> simp [isBlack]
            · exact ⟨hy, haAll, hbAll⟩
            · exact All.balLeft haAll hy hbAll
      · have hbAll := del_all_cut_ne (cmp := cmp) (cut := cut) hb
        have hy : cut y ≠ Ordering.eq := by simp [hcut]
        have haAll : a.All (fun x => cut x ≠ Ordering.eq) := by
          apply hay.imp
          intro x hxy hxeq
          have hgt : cut x = Ordering.gt := IsCut.gt_trans hxy.1 hcut
          cases hgt.symm.trans hxeq
        cases b with
        | nil =>
            simp [isBlack]
            exact ⟨hy, haAll, hbAll⟩
        | node c _ _ _ =>
            cases c <;> simp [isBlack]
            · exact ⟨hy, haAll, hbAll⟩
            · exact All.balRight haAll hy hbAll
      · have haAll : a.All (fun x => cut x ≠ Ordering.eq) := by
          apply hay.imp
          intro x hxy hxeq
          have hx : cmp x y = cut y := IsStrictCut.exact hxeq
          rw [hcut] at hx
          cases hxy.1.symm.trans hx
        have hbAll : b.All (fun x => cut x ≠ Ordering.eq) := by
          apply hyb.imp
          intro x hyx hxeq
          have hx : cmp x y = cut y := IsStrictCut.exact hxeq
          rw [hcut] at hx
          have hxygt : cmp x y = Ordering.gt :=
            Std.OrientedCmp.gt_iff_lt.2 hyx.1
          cases hxygt.symm.trans hx
        exact All.append haAll hbAll

theorem erase_all_cut_ne {cmp : α → α → Ordering} {cut : α → Ordering}
    [Std.TransCmp cmp] [IsStrictCut cmp cut] {t : RBNode α}
    (ht : t.Ordered cmp) :
    (t.erase cut).All (fun x => cut x ≠ Ordering.eq) := by
  unfold erase
  exact All.setBlack' (del_all_cut_ne (cmp := cmp) (cut := cut) ht)

theorem findP?_erase_none {cmp : α → α → Ordering} {cut : α → Ordering}
    [Std.TransCmp cmp] [IsStrictCut cmp cut] (s : RBSet α cmp) :
    (s.erase cut).findP? cut = none := by
  unfold RBSet.erase RBSet.findP?
  rw [find?_eq_none_of_all_ne]
  exact erase_all_cut_ne (cmp := cmp) (cut := cut) s.2.out.1

theorem append_toList (l r : RBNode α) :
    (l.append r).toList = l.toList ++ r.toList := by
  induction l, r using RBNode.append.induct <;>
    simp [RBNode.append, *]
  · rename_i la lx lb rc ry rd ra rx rb h ih
    have ih' := ih
    rw [h] at ih'
    simp at ih'
    calc
      ra.toList ++ rx :: (rb.toList ++ ry :: rd.toList)
          = (ra.toList ++ rx :: rb.toList) ++ ry :: rd.toList := by
              simp [List.append_assoc]
      _ = (lb.toList ++ rc.toList) ++ ry :: rd.toList := by
              rw [ih']
      _ = lb.toList ++ (rc.toList ++ ry :: rd.toList) := by
              simp [List.append_assoc]
  · rename_i la lx lb rc ry rd ra rx rb h ih
    have ih' := ih
    rw [h] at ih'
    simp at ih'
    calc
      ra.toList ++ rx :: (rb.toList ++ ry :: rd.toList)
          = (ra.toList ++ rx :: rb.toList) ++ ry :: rd.toList := by
              simp [List.append_assoc]
      _ = (lb.toList ++ rc.toList) ++ ry :: rd.toList := by
              rw [ih']
      _ = lb.toList ++ (rc.toList ++ ry :: rd.toList) := by
              simp [List.append_assoc]

theorem mem_del_of_mem_ne {cut : α → Ordering}
    {t : RBNode α} {x : α} (hx : x ∈ t) (hcut : cut x ≠ Ordering.eq) :
    x ∈ t.del cut := by
  induction t with
  | nil => cases hx
  | node c a y b iha ihb =>
      simp only [RBNode.del]
      split
      · rename_i hy
        rcases hx with rfl | hx | hx
        · cases hblack : a.isBlack <;>
            rw [← mem_toList] <;>
            simp
        · cases hblack : a.isBlack <;>
            rw [← mem_toList] <;>
            simp [iha hx]
        · cases hblack : a.isBlack <;>
            rw [← mem_toList] <;>
            simp
          · exact Or.inr (Or.inr hx)
          · exact Or.inr (Or.inr hx)
      · rename_i hy
        rcases hx with rfl | hx | hx
        · cases hblack : b.isBlack <;>
            rw [← mem_toList] <;>
            simp
        · cases hblack : b.isBlack <;>
            rw [← mem_toList] <;>
            simp
          · exact Or.inl hx
          · exact Or.inl hx
        · cases hblack : b.isBlack <;>
            rw [← mem_toList] <;>
            simp [ihb hx]
      · rename_i hy
        rcases hx with rfl | hx | hx
        · exact absurd hy hcut
        · rw [← mem_toList]
          simp [append_toList]
          exact Or.inl hx
        · rw [← mem_toList]
          simp [append_toList]
          exact Or.inr hx

theorem mem_of_mem_del {cut : α → Ordering}
    {t : RBNode α} {x : α} (hx : x ∈ t.del cut) :
    x ∈ t := by
  induction t with
  | nil => cases hx
  | node c a y b iha ihb =>
      simp only [RBNode.del] at hx
      split at hx
      · rename_i hy
        cases hblack : a.isBlack
        · rw [← mem_toList] at hx
          simp only [hblack] at hx
          simp at hx
          rcases hx with hx | rfl | hx
          · exact Or.inr (Or.inl (iha hx))
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hx)
        · rw [← mem_toList] at hx
          simp only [hblack] at hx
          simp at hx
          rcases hx with hx | rfl | hx
          · exact Or.inr (Or.inl (iha hx))
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hx)
      · rename_i hy
        cases hblack : b.isBlack
        · rw [← mem_toList] at hx
          simp only [hblack] at hx
          simp at hx
          rcases hx with hx | rfl | hx
          · exact Or.inr (Or.inl hx)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (ihb hx))
        · rw [← mem_toList] at hx
          simp only [hblack] at hx
          simp at hx
          rcases hx with hx | rfl | hx
          · exact Or.inr (Or.inl hx)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (ihb hx))
      · rw [← mem_toList] at hx
        simp [append_toList] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr hx)

theorem mem_erase_of_mem_ne {cut : α → Ordering}
    {t : RBNode α} {x : α} (hx : x ∈ t) (hcut : cut x ≠ Ordering.eq) :
    x ∈ t.erase cut := by
  unfold erase
  rw [← mem_toList]
  simpa using mem_del_of_mem_ne (cut := cut) hx hcut

theorem mem_of_mem_erase {cut : α → Ordering}
    {t : RBNode α} {x : α} (hx : x ∈ t.erase cut) :
    x ∈ t := by
  unfold erase at hx
  rw [← mem_toList] at hx
  exact mem_of_mem_del (cut := cut) (by simpa using hx)

theorem find?_erase_of_ne {cmp : α → α → Ordering}
    {cut eraseCut : α → Ordering} [Std.TransCmp cmp] [IsStrictCut cmp cut]
    (t : RBNode α) (ht : t.Ordered cmp)
    (hNe : ∀ x, cut x = Ordering.eq → eraseCut x ≠ Ordering.eq) :
    (t.erase eraseCut).find? cut = t.find? cut := by
  have htErase : (t.erase eraseCut).Ordered cmp :=
    Ordered.erase (cut := eraseCut) ht
  cases hFind : t.find? cut with
  | none =>
      by_contra hneq
      have hsome : ∃ x, (t.erase eraseCut).find? cut = some x := by
        cases h : (t.erase eraseCut).find? cut with
        | none =>
            exfalso
            exact hneq h
        | some x => exact ⟨x, rfl⟩
      rcases hsome with ⟨x, hx⟩
      have hxMem : x ∈ t :=
        mem_of_mem_erase (cut := eraseCut)
          (find?_some_mem hx)
      have hxEq : cut x = Ordering.eq := find?_some_eq_eq hx
      have hxOld : t.find? cut = some x :=
        (Ordered.find?_some ht).2 ⟨hxMem, hxEq⟩
      rw [hFind] at hxOld
      cases hxOld
  | some x =>
      have hxMem : x ∈ t := find?_some_mem hFind
      have hxEq : cut x = Ordering.eq := find?_some_eq_eq hFind
      exact (Ordered.find?_some htErase).2
        ⟨mem_erase_of_mem_ne (cut := eraseCut) hxMem
          (hNe x hxEq), hxEq⟩

end RBNode

namespace RBMap

theorem find?_erase_self {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (m : RBMap α β cmp) (k : α) :
    (m.erase k).find? k = none := by
  unfold RBMap.find? RBMap.findEntry? RBMap.erase
  rw [RBNode.findP?_erase_none]
  rfl

theorem find?_erase_of_ne {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (m : RBMap α β cmp) {k k' : α} (hNe : cmp k' k ≠ Ordering.eq) :
    (m.erase k).find? k' = m.find? k' := by
  unfold RBMap.find? RBMap.findEntry? RBMap.erase RBSet.erase RBSet.findP?
  rw [RBNode.find?_erase_of_ne (cmp := Ordering.byKey Prod.fst cmp)
    (cut := fun y : α × β => cmp k' y.1)
    (eraseCut := fun y : α × β => cmp k y.1) m.1 m.2.out.1]
  intro y hy
  intro hErase
  have hKey : cmp k' k = Ordering.eq := by
    have h1 : cmp k' y.1 = Ordering.eq := hy
    have h2 : cmp k y.1 = Ordering.eq := hErase
    exact Std.TransCmp.eq_trans h1 (Std.OrientedCmp.eq_comm.1 h2)
  exact hNe hKey

end RBMap
end Batteries

namespace Compiler.Proofs.YulGeneration.Backends.StateBridge

open Compiler.Proofs.YulGeneration
open Compiler.Proofs.IRGeneration (IRStorageWord IRStorageSlot)
open EvmYul

/-! ## Nat ↔ UInt256 Conversions -/

/-- Convert a Verity Nat value to an EVMYulLean UInt256. -/
abbrev natToUInt256 (n : Nat) : UInt256 := UInt256.ofNat n

/-- Convert an EVMYulLean UInt256 to a Verity Nat value. -/
abbrev uint256ToNat (u : UInt256) : Nat := u.toNat

/-! ## Variable Store Bridge

Verity uses `List (String × Nat)` for variable bindings (most recent first).
EVMYulLean uses `VarStore` which is `Finmap (λ _ : String ↦ UInt256)`.

Key semantic difference: Verity's list-based store allows shadowing (duplicate
keys); `getVar` returns the *first* match. EVMYulLean's Finmap is a map
(unique keys). The bridge takes the most recent binding for each variable. -/

/-- Convert Verity variable bindings to EVMYulLean VarStore.
    Uses foldl so that the first (most recent) binding for each variable wins,
    matching Verity's `getVar` shadowing semantics.

    Note: We use the expanded Finmap type rather than the VarStore abbrev
    throughout this definition because Lean 4's unifier does not always
    unfold abbrevs when matching against Finmap's universe-polymorphic
    structure.  The result is still VarStore-compatible since VarStore is
    a transparent abbreviation. -/
noncomputable def varsToVarStore (vars : List (String × Nat)) :
    Finmap (fun _ : Identifier => Literal) :=
  vars.foldl (init := (∅ : Finmap (fun _ : Identifier => Literal)))
    fun store (name, val) =>
      let id : Identifier := name
      if (Finmap.lookup id store).isSome then store
      else Finmap.insert id (natToUInt256 val) store

/-- Convert EVMYulLean VarStore back to Verity variable bindings.
    Order is not preserved (Finmap has no canonical ordering). -/
noncomputable def varStoreToVars (store : Finmap (fun _ : Identifier => Literal)) :
    List (String × Nat) :=
  store.entries.toList.map fun ⟨name, val⟩ => ((name : String), uint256ToNat val)

/-! ## Storage Bridge

Verity uses `Nat → Nat` (total function, default 0 for unwritten slots).
EVMYulLean uses `Storage` = `RBMap UInt256 UInt256` (finite map, default 0).

The round-trip requires knowing which slots are "observable" — the bridge
can only reconstruct slots that are in the EVMYulLean RBMap. For the
forward direction (Verity → EVMYulLean), we need to know which slots to
project. In practice, this is the set of slots written during execution. -/

/-- Look up a storage slot in EVMYulLean's Storage map, returning 0 for
    unwritten slots (matching Verity's `Nat → Nat` semantics). -/
def storageLookup (s : EvmYul.Storage) (slot : UInt256) : UInt256 :=
  match s.find? slot with
  | some val => val
  | none => ⟨0⟩

/-- Write a storage slot in EVMYulLean's Storage map. -/
def storageWrite (s : EvmYul.Storage) (slot val : UInt256) : EvmYul.Storage :=
  s.insert slot val

/-- Project a finite set of Verity storage slots into an EVMYulLean Storage map.

Nat slot inputs are normalized through `IRStorageSlot.ofNat`, matching the
EVMYulLean `UInt256` key used in the projected map. -/
def projectStorage (storage : IRStorageSlot → IRStorageWord) (slots : List Nat) : EvmYul.Storage :=
  slots.foldl (init := Batteries.RBMap.empty) fun acc slot =>
    let key := natToUInt256 slot
    let val := IRStorageWord.toUInt256 (storage (IRStorageSlot.ofNat slot))
    acc.insert key val

/-! ## Execution Environment Bridge

Maps Verity's flat YulState fields to EVMYulLean's `ExecutionEnv .Yul`. -/

/-- Convert a Verity address (Nat) to an EVMYulLean AccountAddress.
    EVMYulLean's AccountAddress is `Fin (2^160)`. -/
def natToAddress (n : Nat) : AccountAddress :=
  ⟨n % (2 ^ 160), Nat.mod_lt _ (by decide)⟩

/-- Create a minimal EVMYulLean BlockHeader from Verity's block fields.
    Fields not modeled by Verity (e.g. baseFeePerGas, gasLimit) are set to
    default zero values. EVMYulLean derives `blobbasefee()` from
    `excessBlobGas`, so this zero header represents only
    `EvmYul.MIN_BASE_FEE_PER_BLOB_GAS`; the native harness fails closed when a
    selected runtime path reads `blobbasefee()` with any other transaction
    `blobBaseFee`. -/
def mkBlockHeader (state : YulState) : BlockHeader :=
  { parentHash := ⟨0⟩
    ommersHash := ⟨0⟩
    beneficiary := ⟨0, by decide⟩
    stateRoot := ⟨0⟩
    transRoot := ByteArray.empty
    receiptRoot := ByteArray.empty
    logsBloom := ByteArray.empty
    difficulty := 0
    number := state.blockNumber
    gasLimit := 0
    gasUsed := 0
    timestamp := state.blockTimestamp
    extraData := ByteArray.empty
    nonce := ⟨0, by decide⟩
    prevRandao := ⟨0⟩
    baseFeePerGas := 0
    parentBeaconBlockRoot := ByteArray.empty
    withdrawalsRoot := ByteArray.empty
    blobGasUsed := ⟨0, by decide⟩
    excessBlobGas := ⟨0, by decide⟩ }

/-- Convert Verity calldata (List of 32-byte words) to EVMYulLean calldata
    (ByteArray). Each word is encoded as a big-endian 32-byte chunk.
    Prepends the 4-byte function selector. -/
def calldataToByteArray (selector : Nat) (calldata : List Nat) : ByteArray :=
  -- 4 bytes for selector + 32 bytes per word
  let selectorBytes : ByteArray :=
    ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)
  let wordBytes (w : Nat) : ByteArray :=
    ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)
  calldata.foldl (init := selectorBytes) fun acc w => acc ++ wordBytes w

private theorem calldataToByteArray_selectorBytes_size (selector : Nat) :
    (ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)).size = 4 := by
  simp

private theorem calldataToByteArray_wordBytes_size (w : Nat) :
    (ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)).size = 32 := by
  simp

private theorem calldataToByteArray_fold_size
    (wordBytes : Nat → ByteArray)
    (hWord : ∀ w, (wordBytes w).size = 32) :
    ∀ (acc : ByteArray) (calldata : List Nat),
      (calldata.foldl (init := acc) fun acc w => acc ++ wordBytes w).size =
        acc.size + calldata.length * 32 := by
  intro acc calldata
  induction calldata generalizing acc with
  | nil =>
      simp
  | cons w ws ih =>
      simp [List.foldl_cons, ByteArray.size_append, hWord, ih, Nat.add_assoc]
      omega

private theorem byteArray_get?_append_left
    {a b : ByteArray} {i : Nat} (h : i < a.size) :
    (a ++ b).get? i = a.get? i := by
  unfold ByteArray.get?
  split
  · apply congrArg some
    have hEq : (a ++ b)[i] = a[i] := ByteArray.get_append_left h
    convert hEq using 1
  · exact False.elim (by
      rename_i hAppend
      exact hAppend (by
        rw [ByteArray.size_append]
        exact Nat.lt_of_lt_of_le h (Nat.le_add_right a.size b.size)))

private theorem byteArray_get?_append_right
    {a b : ByteArray} {i : Nat} (hle : a.size ≤ i)
    (h : i < (a ++ b).size) :
    (a ++ b).get? i = b.get? (i - a.size) := by
  unfold ByteArray.get?
  split
  · rename_i hget
    have hb : i - a.size < b.size := by
      rw [ByteArray.size_append] at h
      omega
    rw [dif_pos hb]
    apply congrArg some
    have hEq : (a ++ b)[i] = b[i - a.size] :=
      ByteArray.get_append_right hle hget
    convert hEq using 1
  · rename_i hnot
    exact False.elim (hnot h)

private theorem calldataToByteArray_fold_get?_left
    (wordBytes : Nat → ByteArray)
    (hWord : ∀ w, (wordBytes w).size = 32) :
    ∀ (acc : ByteArray) (calldata : List Nat) (i : Nat), i < acc.size →
      (calldata.foldl (init := acc) fun acc w => acc ++ wordBytes w).get? i =
        acc.get? i := by
  intro acc calldata
  induction calldata generalizing acc with
  | nil =>
      intro i h
      rfl
  | cons w ws ih =>
      intro i h
      simp only [List.foldl_cons]
      calc
        (ws.foldl (init := acc ++ wordBytes w) fun acc w => acc ++ wordBytes w).get? i
            = (acc ++ wordBytes w).get? i := by
                apply ih
                rw [ByteArray.size_append, hWord]
                omega
        _ = acc.get? i := byteArray_get?_append_left h

/-- The bridged calldata byte array has the same observable length as Verity's
    `calldatasize`: 4 selector bytes plus 32 bytes per calldata word. -/
theorem calldataToByteArray_size (selector : Nat) (calldata : List Nat) :
    (calldataToByteArray selector calldata).size = 4 + calldata.length * 32 := by
  unfold calldataToByteArray
  let selectorBytes : ByteArray :=
    ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)
  let wordBytes : Nat → ByteArray := fun w =>
    ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)
  have hSel : selectorBytes.size = 4 := by
    simp [selectorBytes]
  have hWord : ∀ w, (wordBytes w).size = 32 := by
    intro w
    simp [wordBytes]
  have hFold := calldataToByteArray_fold_size wordBytes hWord selectorBytes calldata
  simpa [selectorBytes, wordBytes, hSel] using hFold

@[simp] theorem calldataToByteArray_selectorByte0 (selector : Nat) (calldata : List Nat) :
    (calldataToByteArray selector calldata).get? 0 =
      some (UInt8.ofNat (selector / 2^24 % 256)) := by
  unfold calldataToByteArray
  let selectorBytes : ByteArray :=
    ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)
  let wordBytes : Nat → ByteArray := fun w =>
    ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)
  have hWord : ∀ w, (wordBytes w).size = 32 := by intro w; simp [wordBytes]
  rw [calldataToByteArray_fold_get?_left wordBytes hWord]
  · unfold ByteArray.get?
    split
    · apply congrArg some
      simp [ByteArray.get]
    · simp at *
  · simp

@[simp] theorem calldataToByteArray_selectorByte1 (selector : Nat) (calldata : List Nat) :
    (calldataToByteArray selector calldata).get? 1 =
      some (UInt8.ofNat (selector / 2^16 % 256)) := by
  unfold calldataToByteArray
  let selectorBytes : ByteArray :=
    ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)
  let wordBytes : Nat → ByteArray := fun w =>
    ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)
  have hWord : ∀ w, (wordBytes w).size = 32 := by intro w; simp [wordBytes]
  rw [calldataToByteArray_fold_get?_left wordBytes hWord]
  · unfold ByteArray.get?
    split
    · apply congrArg some
      simp [ByteArray.get]
    · simp at *
  · simp

@[simp] theorem calldataToByteArray_selectorByte2 (selector : Nat) (calldata : List Nat) :
    (calldataToByteArray selector calldata).get? 2 =
      some (UInt8.ofNat (selector / 2^8 % 256)) := by
  unfold calldataToByteArray
  let selectorBytes : ByteArray :=
    ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)
  let wordBytes : Nat → ByteArray := fun w =>
    ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)
  have hWord : ∀ w, (wordBytes w).size = 32 := by intro w; simp [wordBytes]
  rw [calldataToByteArray_fold_get?_left wordBytes hWord]
  · unfold ByteArray.get?
    split
    · apply congrArg some
      simp [ByteArray.get]
    · simp at *
  · simp

@[simp] theorem calldataToByteArray_selectorByte3 (selector : Nat) (calldata : List Nat) :
    (calldataToByteArray selector calldata).get? 3 =
      some (UInt8.ofNat (selector % 256)) := by
  unfold calldataToByteArray
  let selectorBytes : ByteArray :=
    ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)
  let wordBytes : Nat → ByteArray := fun w =>
    ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)
  have hWord : ∀ w, (wordBytes w).size = 32 := by intro w; simp [wordBytes]
  rw [calldataToByteArray_fold_get?_left wordBytes hWord]
  · unfold ByteArray.get?
    split
    · apply congrArg some
      simp [ByteArray.get]
    · simp at *
  · simp

/-- Byte-level projection for the first ABI argument word in bridged calldata.
    This is the offset-4 calldata analogue of the selector byte lemmas above:
    byte `4 + i` is the `i`th big-endian byte of the first 32-byte argument. -/
theorem calldataToByteArray_arg0Byte
    (selector arg : Nat) (rest : List Nat) (i : Nat) (hi : i < 32) :
    (calldataToByteArray selector (arg :: rest)).get? (4 + i) =
      some (UInt8.ofNat (arg / 2 ^ ((31 - i) * 8) % 256)) := by
  unfold calldataToByteArray
  let selectorBytes : ByteArray :=
    ByteArray.ofFn fun i : Fin 4 =>
      match i.1 with
      | 0 => UInt8.ofNat (selector / 2^24 % 256)
      | 1 => UInt8.ofNat (selector / 2^16 % 256)
      | 2 => UInt8.ofNat (selector / 2^8 % 256)
      | _ => UInt8.ofNat (selector % 256)
  let wordBytes : Nat → ByteArray := fun w =>
    ByteArray.ofFn fun i : Fin 32 =>
      UInt8.ofNat (w / 2^((31 - i.1) * 8) % 256)
  have hWord : ∀ w, (wordBytes w).size = 32 := by
    intro w
    simp [wordBytes]
  have hAccSize : (selectorBytes ++ wordBytes arg).size = 36 := by
    rw [ByteArray.size_append]
    simp [selectorBytes, wordBytes]
  simp only [List.foldl_cons]
  rw [calldataToByteArray_fold_get?_left wordBytes hWord]
  · rw [byteArray_get?_append_right]
    · unfold ByteArray.get?
      split
      · apply congrArg some
        simp [ByteArray.get]
      · rename_i hge
        exact False.elim (hge (by simp; omega))
    · simp
    · rw [hAccSize]
      omega
  · rw [hAccSize]
    omega

/-! ## Full State Conversion

The main bridge functions that convert between Verity's YulState and
EVMYulLean's Yul execution state. -/

/-- Convert Verity's YulState to an EVMYulLean SharedState.
    Requires the set of observable storage slots for projection. -/
def toSharedState (state : YulState) (observableSlots : List Nat) :
    SharedState .Yul :=
  let addr := natToAddress state.thisAddress
  let storage := projectStorage state.storage observableSlots
  let emptyCode : Yul.Ast.contractCode .Yul := Inhabited.default
  let account : Account .Yul :=
    { nonce := ⟨0⟩
      balance := ⟨0⟩
      storage := storage
      code := emptyCode
      tstorage := Batteries.RBMap.empty }
  let accountMap : AccountMap .Yul :=
    (Batteries.RBMap.empty).insert addr account
  let execEnv : ExecutionEnv .Yul :=
    { codeOwner := addr
      sender := natToAddress state.sender
      source := natToAddress state.sender
      weiValue := natToUInt256 state.msgValue
      calldata := calldataToByteArray state.selector state.calldata
      code := emptyCode
      gasPrice := 0
      header := mkBlockHeader state
      depth := 0
      perm := false
      blobVersionedHashes := [] }
  { -- State τ fields
    accountMap := accountMap
    σ₀ := Batteries.RBMap.empty
    totalGasUsedInBlock := 0
    transactionReceipts := #[]
    substate := Inhabited.default
    executionEnv := execEnv
    blocks := #[]
    genesisBlockHeader := mkBlockHeader state
    createdAccounts := Batteries.RBSet.empty
    -- MachineState fields
    gasAvailable := ⟨0⟩
    activeWords := ⟨0⟩
    memory := ByteArray.empty
    returnData := ByteArray.empty
    H_return := ByteArray.empty }

/-- Extract observable storage from an EVMYulLean state for the contract
    at the given address. Returns the Verity-style storage function.

The bounded IR slot is already the EVM storage key, so extraction is lossless
with respect to the IR storage domain. -/
def extractStorage (sharedState : SharedState .Yul) (addr : AccountAddress) :
    IRStorageSlot → IRStorageWord :=
  fun slot =>
    match sharedState.accountMap.find? addr with
    | some account =>
      match account.storage.find? (IRStorageSlot.toUInt256 slot) with
      | some val => val
      | none => 0
    | none => 0

/-! ## Environment Field Bridge Proofs

These theorems prove that Verity's `legacyEvalBuiltinCallWithContext` agrees with the
corresponding field extraction from the EVMYulLean state constructed by
`toSharedState`. Each theorem connects a stateful builtin's Verity semantics
to the state bridge.

The proof pattern is uniform:
1. Unfold the Verity builtin to `some (field % evmModulus)`
2. Unfold the bridge to `natToUInt256 field`
3. Show `uint256ToNat (natToUInt256 field) = field % UInt256.size = field % evmModulus`
   since `UInt256.size = evmModulus`. -/

/-- The `callvalue` builtin reads `msgValue` from Verity's state.
    The state bridge stores `natToUInt256 state.msgValue` in `execEnv.weiValue`.
    These agree modulo `evmModulus`. -/
theorem callvalue_bridge (state : YulState) (observableSlots : List Nat) :
    legacyEvalBuiltinCallWithContext state.storage state.sender state.msgValue
      state.thisAddress state.blockTimestamp state.blockNumber state.chainId
      state.blobBaseFee state.selector state.calldata "callvalue" [] =
    some (uint256ToNat (toSharedState state observableSlots).executionEnv.weiValue) := by
  simp [legacyEvalBuiltinCallWithContext, toSharedState, uint256ToNat, natToUInt256,
    UInt256.toNat, UInt256.ofNat, Id.run, evmModulus, UInt256.size]

/-- The `timestamp` builtin reads `blockTimestamp` from Verity's state.
    The state bridge stores `state.blockTimestamp` in the block header's
    `timestamp` field. EVMYulLean converts this to `UInt256.ofNat`. -/
theorem timestamp_bridge (state : YulState) (observableSlots : List Nat) :
    legacyEvalBuiltinCallWithContext state.storage state.sender state.msgValue
      state.thisAddress state.blockTimestamp state.blockNumber state.chainId
      state.blobBaseFee state.selector state.calldata "timestamp" [] =
    some (uint256ToNat (UInt256.ofNat
      (toSharedState state observableSlots).executionEnv.header.timestamp)) := by
  simp [legacyEvalBuiltinCallWithContext, toSharedState, mkBlockHeader, uint256ToNat,
    UInt256.toNat, UInt256.ofNat, Id.run, evmModulus, UInt256.size]

/-- The `number` builtin reads `blockNumber` from Verity's state.
    The state bridge stores `state.blockNumber` in the block header's
    `number` field. EVMYulLean converts this to `UInt256.ofNat`. -/
theorem number_bridge (state : YulState) (observableSlots : List Nat) :
    legacyEvalBuiltinCallWithContext state.storage state.sender state.msgValue
      state.thisAddress state.blockTimestamp state.blockNumber state.chainId
      state.blobBaseFee state.selector state.calldata "number" [] =
    some (uint256ToNat (UInt256.ofNat
      (toSharedState state observableSlots).executionEnv.header.number)) := by
  simp [legacyEvalBuiltinCallWithContext, toSharedState, mkBlockHeader, uint256ToNat,
    UInt256.toNat, UInt256.ofNat, Id.run, evmModulus, UInt256.size]

/-- The `calldatasize` builtin reads the size of the current calldata payload.
    The state bridge encodes Verity calldata as 4 selector bytes followed by
    one 32-byte word per calldata element. Both sides reduce the observable
    length into the `UInt256` word domain, so the bridge agrees even when the
    byte length wraps modulo `2^256`. -/
theorem calldatasize_bridge (state : YulState) (observableSlots : List Nat) :
    legacyEvalBuiltinCallWithContext state.storage state.sender state.msgValue
      state.thisAddress state.blockTimestamp state.blockNumber state.chainId
      state.blobBaseFee state.selector state.calldata "calldatasize" [] =
    some (uint256ToNat (UInt256.ofNat
      (toSharedState state observableSlots).executionEnv.calldata.size)) := by
  simp [legacyEvalBuiltinCallWithContext, toSharedState, uint256ToNat, UInt256.toNat,
    UInt256.ofNat, Id.run, UInt256.size, calldataToByteArray_size]

set_option maxHeartbeats 8000000 in
/-- The `caller` builtin reads `sender` from Verity's state.
    The state bridge stores `natToAddress state.sender` in `execEnv.source`.
    EVMYulLean's CALLER extracts `source` as `UInt256.ofNat (Fin.val source)`.

    Since `natToAddress n = ⟨n % 2^160, _⟩`, the EVMYulLean side returns
    `UInt256.ofNat (n % 2^160)`. Verity returns `sender` (no modular reduction
    in `legacyEvalBuiltinCallWithContext`). Agreement requires the hypothesis that
    `sender < evmModulus` (it's an Ethereum address, so `< 2^160 < 2^256`). -/
theorem caller_bridge (state : YulState) (observableSlots : List Nat)
    (hSender : state.sender < 2 ^ 160) :
    legacyEvalBuiltinCallWithContext state.storage state.sender state.msgValue
      state.thisAddress state.blockTimestamp state.blockNumber state.chainId
      state.blobBaseFee state.selector state.calldata "caller" [] =
    some (uint256ToNat (UInt256.ofNat
      (toSharedState state observableSlots).executionEnv.source.val)) := by
  simp [legacyEvalBuiltinCallWithContext, toSharedState, natToAddress,
    uint256ToNat, UInt256.toNat, UInt256.ofNat, Id.run, UInt256.size]
  omega

set_option maxHeartbeats 8000000 in
/-- The `address` builtin reads `thisAddress` from Verity's state.
    The state bridge stores `natToAddress state.thisAddress` in `execEnv.codeOwner`.
    EVMYulLean's ADDRESS extracts `codeOwner` as `UInt256.ofNat (Fin.val codeOwner)`.

    Agreement requires `thisAddress < 2^160` (valid Ethereum address). -/
theorem address_bridge (state : YulState) (observableSlots : List Nat)
    (hAddr : state.thisAddress < 2 ^ 160) :
    legacyEvalBuiltinCallWithContext state.storage state.sender state.msgValue
      state.thisAddress state.blockTimestamp state.blockNumber state.chainId
      state.blobBaseFee state.selector state.calldata "address" [] =
    some (uint256ToNat (UInt256.ofNat
      (toSharedState state observableSlots).executionEnv.codeOwner.val)) := by
  simp [legacyEvalBuiltinCallWithContext, toSharedState, natToAddress,
    uint256ToNat, UInt256.toNat, UInt256.ofNat, Id.run, evmModulus, UInt256.size]
  omega

/-! ## Storage Bridge Proofs -/

/-- The derived `Ord` for `UInt256` generates
    `compare (mk a) (mk b) = Ordering.then (compare a b) .eq`
    rather than `compare a b` directly. This helper reduces the
    `Ordering.then` wrapper so we can delegate to `Fin`'s instances. -/
private theorem ordering_then_eq (o : Ordering) : o.then .eq = o := by
  cases o <;> rfl

/-- The derived `Ord` on `UInt256` (a single-field structure wrapping `Fin`)
    satisfies `compare (mk a) (mk b) = compare a b` on `Fin UInt256.size`.

    Lean 4's `deriving Ord` generates `Ordering.then (compare a b) .eq`,
    which we reduce via `ordering_then_eq`. -/
private theorem UInt256_compare_eq_fin (a b : Fin UInt256.size) :
    @compare UInt256 _ (UInt256.mk a) (UInt256.mk b) = @compare (Fin UInt256.size) _ a b := by
  -- The derived Ord generates: Ordering.then (compare a b) .eq
  -- We reduce this to compare a b by simplifying the Ordering.then wrapper.
  -- Use `change` to assert the definitional form, then apply ordering_then_eq.
  change (compare a b).then .eq = compare a b
  exact ordering_then_eq _

/-- `TransCmp` instance for `UInt256`'s derived `compare`.
    `UInt256` derives `Ord` which compares via the `Fin` field.
    `Fin n` has `TransOrd` and `LawfulEqOrd` in Lean 4's Std library.

    We bridge the derived Ord (which wraps in `Ordering.then ... .eq`)
    to `Fin`'s `TransCmp` instance. -/
instance instTransCmpUInt256 : Std.TransCmp (α := UInt256) compare where
  eq_swap {a b} := by
    cases a with | mk va => cases b with | mk vb =>
    simp only [UInt256_compare_eq_fin]
    exact Std.OrientedCmp.eq_swap
  isLE_trans {a b c} hab hbc := by
    cases a with | mk va => cases b with | mk vb => cases c with | mk vc =>
    simp only [UInt256_compare_eq_fin] at hab hbc ⊢
    exact Std.TransCmp.isLE_trans hab hbc

/-- `compare` on `UInt256` returning `.eq` implies equality.
    Proved by reducing to `Fin`'s compare and using `LawfulEqOrd`. -/
theorem UInt256_eq_of_compare_eq {u v : UInt256}
    (h : compare u v = Ordering.eq) : u = v := by
  cases u with | mk uv =>
  cases v with | mk vv =>
  rw [UInt256_compare_eq_fin] at h
  have heq : uv = vv := Std.LawfulEqCmp.eq_of_compare h
  subst heq
  rfl

/-- `natToUInt256` is injective on values below `UInt256.size`.
    Since `UInt256.ofNat n = ⟨⟨n % size, _⟩⟩`, when `n < size` we have
    `n % size = n`, so the Fin value is exactly `n`. -/
theorem natToUInt256_injective {a b : Nat}
    (ha : a < UInt256.size) (hb : b < UInt256.size)
    (h : natToUInt256 a = natToUInt256 b) : a = b := by
  -- Unfold the full chain to expose the modular arithmetic
  have hval : a % UInt256.size = b % UInt256.size := by
    have := congrArg (fun u => u.val.val) h
    simpa [natToUInt256, UInt256.ofNat, Id.run, Fin.ofNat] using this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hval

/-- Distinct in-range Nats map to UInt256s with `compare ≠ .eq`. -/
theorem compare_natToUInt256_ne {a b : Nat}
    (ha : a < UInt256.size) (hb : b < UInt256.size) (hab : a ≠ b) :
    compare (natToUInt256 a) (natToUInt256 b) ≠ Ordering.eq := by
  intro heq
  exact hab (natToUInt256_injective ha hb (UInt256_eq_of_compare_eq heq))

/-- Helper: folding inserts over a list of slots that does NOT contain `slot`
    preserves whatever `find?` value the accumulator had for `natToUInt256 slot`. -/
theorem foldl_insert_find_not_mem (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (slot : Nat) (hNotMem : slot ∉ slots)
    (hRange : ∀ s ∈ slots, s < UInt256.size)
    (hSlotRange : slot < UInt256.size)
    (acc : EvmYul.Storage) :
    (slots.foldl (fun m s => m.insert (natToUInt256 s) (IRStorageWord.toUInt256 (storage (IRStorageSlot.ofNat s)))) acc).find?
      (natToUInt256 slot) = acc.find? (natToUInt256 slot) := by
  induction slots generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hNotMemTl : slot ∉ tl := fun h => hNotMem (List.mem_cons_of_mem _ h)
    have hne : hd ≠ slot := fun h => hNotMem (h ▸ List.mem_cons_self)
    have hd_range : hd < UInt256.size := hRange hd (List.mem_cons_self)
    rw [ih hNotMemTl (fun s hs => hRange s (List.mem_cons_of_mem _ hs))]
    exact Batteries.RBMap.find?_insert_of_ne _
      (compare_natToUInt256_ne hSlotRange hd_range (Ne.symm hne))

/-- Helper: after folding a suffix of slots into an accumulator, if `slot`
    is in that suffix, then the accumulated map contains the right value.

    This generalizes `storageLookup_projectStorage` to work with any
    accumulator (not just `empty`), which is needed for the induction. -/
theorem foldl_insert_find (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (slot : Nat) (hSlot : slot ∈ slots)
    (hRange : ∀ s ∈ slots, s < UInt256.size)
    (acc : EvmYul.Storage) :
    (slots.foldl (fun m s => m.insert (natToUInt256 s) (IRStorageWord.toUInt256 (storage (IRStorageSlot.ofNat s)))) acc).find?
      (natToUInt256 slot) = some (IRStorageWord.toUInt256 (storage (IRStorageSlot.ofNat slot))) := by
  induction slots generalizing acc with
  | nil => exact absurd hSlot List.not_mem_nil
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hSlot with
    | inl heq =>
      subst heq
      by_cases hmem : slot ∈ tl
      · -- slot also appears later in tl; the last insert wins with same value
        exact ih hmem (fun s hs => hRange s (List.mem_cons_of_mem _ hs)) _
      · -- slot not in tl: the fold over tl preserves the inserted value
        have hSlotRange : slot < UInt256.size := hRange slot (List.mem_cons_self)
        rw [foldl_insert_find_not_mem storage tl slot hmem
          (fun s hs => hRange s (List.mem_cons_of_mem _ hs)) hSlotRange]
        exact Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self
    | inr hmem =>
      exact ih hmem (fun s hs => hRange s (List.mem_cons_of_mem _ hs)) _

/-- Equal projected EVM storage keys denote equal bounded IR storage slots. -/
theorem IRStorageSlot_ofNat_eq_of_natToUInt256_eq {a b : Nat}
    (h : natToUInt256 a = natToUInt256 b) :
    IRStorageSlot.ofNat a = IRStorageSlot.ofNat b := by
  simpa [natToUInt256, IRStorageSlot.ofNat] using h

/-- Folding projected storage slots preserves an already-correct lookup for a
    bounded target key. Any later Nat alias for the same EVM key writes the same
    bounded IR slot value, so no Nat range/injectivity hypothesis is needed. -/
theorem foldl_insert_preserves_find_projected_value
    (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (slot : Nat) (acc : EvmYul.Storage)
    (hAcc :
      acc.find? (natToUInt256 slot) =
        some (IRStorageWord.toUInt256 (storage (IRStorageSlot.ofNat slot)))) :
    (slots.foldl (fun m s =>
        m.insert (natToUInt256 s)
          (IRStorageWord.toUInt256 (storage (IRStorageSlot.ofNat s)))) acc).find?
      (natToUInt256 slot) =
        some (IRStorageWord.toUInt256 (storage (IRStorageSlot.ofNat slot))) := by
  induction slots generalizing acc with
  | nil => exact hAcc
  | cons hd tl ih =>
      simp only [List.foldl_cons]
      by_cases hcmp : compare (natToUInt256 slot) (natToUInt256 hd) = Ordering.eq
      · have hkey : natToUInt256 slot = natToUInt256 hd :=
          UInt256_eq_of_compare_eq hcmp
        have hslot : IRStorageSlot.ofNat hd = IRStorageSlot.ofNat slot :=
          (IRStorageSlot_ofNat_eq_of_natToUInt256_eq hkey.symm)
        apply ih
        rw [Batteries.RBMap.find?_insert_of_eq _ hcmp]
        simp [hslot]
      · apply ih
        rw [Batteries.RBMap.find?_insert_of_ne _ hcmp]
        exact hAcc

/-- Helper: after folding a suffix of Nat slots into an accumulator, if `slot`
    appears in that suffix, then the accumulated projected map contains the
    bounded value for `slot`.

    Unlike `foldl_insert_find`, this form intentionally has no Nat range
    hypothesis. Distinct Nat slots that alias modulo 2^256 map to the same
    `IRStorageSlot`, so a later aliased insert writes the same value. -/
theorem foldl_insert_find_projected (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (slot : Nat) (hSlot : slot ∈ slots)
    (acc : EvmYul.Storage) :
    (slots.foldl (fun m s =>
        m.insert (natToUInt256 s)
          (IRStorageWord.toUInt256 (storage (IRStorageSlot.ofNat s)))) acc).find?
      (natToUInt256 slot) =
        some (IRStorageWord.toUInt256 (storage (IRStorageSlot.ofNat slot))) := by
  induction slots generalizing acc with
  | nil => exact absurd hSlot List.not_mem_nil
  | cons hd tl ih =>
      simp only [List.foldl_cons]
      cases List.mem_cons.mp hSlot with
      | inl heq =>
          subst heq
          apply foldl_insert_preserves_find_projected_value
          rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
      | inr hmem =>
          exact ih hmem _

/-- Storage lookup commutes: reading a slot from the projected storage
    yields the same value as reading it from Verity's storage function.

    The `hRange` hypothesis ensures `natToUInt256` is injective on the
    slot list (EVM storage slots are always < 2^256). Without it, two
    distinct Nat slots could collide under modular reduction and the
    last-write-wins semantics of `foldl` would make the theorem false. -/
theorem storageLookup_projectStorage (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (slot : Nat) (hSlot : slot ∈ slots)
    (_hRange : ∀ s ∈ slots, s < UInt256.size) :
    storageLookup (projectStorage storage slots) (natToUInt256 slot) =
      storage (IRStorageSlot.ofNat slot) := by
  simp only [storageLookup, projectStorage]
  rw [foldl_insert_find_projected storage slots slot hSlot]
  rfl

/-- Range-free storage lookup for projected bounded IR storage. -/
theorem storageLookup_projectStorage_projected
    (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (slot : Nat) (hSlot : slot ∈ slots) :
    storageLookup (projectStorage storage slots) (natToUInt256 slot) =
      storage (IRStorageSlot.ofNat slot) := by
  simp only [storageLookup, projectStorage]
  rw [foldl_insert_find_projected storage slots slot hSlot]
  rfl

/-- Nat→UInt256→Nat round-trip for values in range.
    Proof: `ofNat n = ⟨Fin.ofNat _ n⟩ = ⟨⟨n % size, _⟩⟩`, and
    `toNat` extracts `.val.val`, so the goal reduces to `n % size = n`
    which follows from `Nat.mod_eq_of_lt h`. -/
theorem uint256_roundtrip (n : Nat) (h : n < UInt256.size) :
    uint256ToNat (natToUInt256 n) = n := by
  simp only [uint256ToNat, natToUInt256, UInt256.toNat, UInt256.ofNat, Id.run]
  exact Nat.mod_eq_of_lt h

end Compiler.Proofs.YulGeneration.Backends.StateBridge
