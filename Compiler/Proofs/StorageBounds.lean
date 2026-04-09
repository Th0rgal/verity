import Verity.Core

/-!
# Storage Bounds Lemmas for Dynamic Arrays

Standalone mathematical facts about dynamic array operations defined in
`SourceSemantics.lean`. These lemmas support widening `SupportedBodyStateInterface`
to admit `storageArrayLength` and `storageArrayElement` reads into the proven
fragment.

## Key results

- `storageArray_element_val_lt`: each `Uint256` element has `.val < 2^256`
- `storageArraySetAt_length`: `storageArraySetAt` preserves list length
- `storageArrayDropLast_length`: `storageArrayDropLast?` decreases length by 1
- `writeStorageArray_other_slot`: `writeStorageArray` is a frame-preserving update
-/

namespace Compiler.Proofs.StorageBounds

open Verity.Core

/-! ### Element bounds -/

theorem storageArray_element_val_lt (elem : Uint256) :
    elem.val < UINT256_MODULUS :=
  elem.isLt

theorem storageArray_element_bounded (arr : List Uint256) (i : Nat)
    (hi : i < arr.length) :
    arr[i].val < UINT256_MODULUS :=
  arr[i].isLt

/-! ### storageArraySetAt -/

/-- Mirrors the private definition in `SourceSemantics.lean`. -/
def storageArraySetAt : List Uint256 → Nat → Uint256 → Option (List Uint256)
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, idx + 1, value => do
      let updatedRest ← storageArraySetAt rest idx value
      some (head :: updatedRest)

theorem storageArraySetAt_length (arr : List Uint256) (idx : Nat) (val : Uint256)
    (arr' : List Uint256) (h : storageArraySetAt arr idx val = some arr') :
    arr'.length = arr.length := by
  induction arr generalizing idx arr' with
  | nil => simp [storageArraySetAt] at h
  | cons head rest ih =>
    cases idx with
    | zero =>
      simp [storageArraySetAt] at h
      subst h; simp
    | succ idx' =>
      simp [storageArraySetAt, bind, Option.bind] at h
      split at h
      · simp at h
      · rename_i updatedRest heq
        simp at h; subst h
        simp [ih idx' updatedRest heq]

/-! ### storageArrayDropLast? -/

/-- Mirrors the private definition in `SourceSemantics.lean`. -/
def storageArrayDropLast? : List Uint256 → Option (List Uint256)
  | [] => none
  | [_] => some []
  | head :: rest => do
      let updatedRest ← storageArrayDropLast? rest
      some (head :: updatedRest)

theorem storageArrayDropLast_length (arr : List Uint256) (arr' : List Uint256)
    (h : storageArrayDropLast? arr = some arr') :
    arr'.length + 1 = arr.length := by
  induction arr generalizing arr' with
  | nil => simp [storageArrayDropLast?] at h
  | cons head rest ih =>
    match rest with
    | [] => simp [storageArrayDropLast?] at h; subst h; simp
    | r :: rs =>
      simp [storageArrayDropLast?, bind, Option.bind] at h
      split at h
      · simp at h
      · rename_i updatedRest heq
        simp at h; subst h
        have := ih updatedRest heq
        simp_all [List.length_cons]

/-! ### writeStorageArray frame lemma -/

/-- Mirrors the private definition in `SourceSemantics.lean`. -/
def writeStorageArray (world : Verity.ContractState) (slot : Nat)
    (values : List Uint256) : Verity.ContractState :=
  { world with
    storageArray := fun s => if s == slot then values else world.storageArray s }

theorem writeStorageArray_same_slot (world : Verity.ContractState) (slot : Nat)
    (values : List Uint256) :
    (writeStorageArray world slot values).storageArray slot = values := by
  simp [writeStorageArray, BEq.beq]

theorem writeStorageArray_other_slot (world : Verity.ContractState) (slot slot' : Nat)
    (values : List Uint256) (h : slot' ≠ slot) :
    (writeStorageArray world slot values).storageArray slot' = world.storageArray slot' := by
  unfold writeStorageArray
  simp
  omega

theorem writeStorageArray_storage_unchanged (world : Verity.ContractState) (slot : Nat)
    (values : List Uint256) :
    (writeStorageArray world slot values).storage = world.storage :=
  rfl

theorem writeStorageArray_events_unchanged (world : Verity.ContractState) (slot : Nat)
    (values : List Uint256) :
    (writeStorageArray world slot values).events = world.events :=
  rfl

end Compiler.Proofs.StorageBounds
