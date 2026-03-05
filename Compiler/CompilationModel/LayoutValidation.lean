import Compiler.CompilationModel.Types
import Compiler.CompilationModel.ValidationHelpers

namespace Compiler.CompilationModel

def firstDuplicateName (names : List String) : Option String :=
  let rec go (seen : List String) : List String → Option String
    | [] => none
    | n :: rest =>
      if seen.contains n then
        some n
      else
        go (n :: seen) rest
  go [] names

def firstDuplicateFunctionParamName
    (fns : List FunctionSpec) : Option (String × String) :=
  let rec goFns : List FunctionSpec → Option (String × String)
    | [] => none
    | fn :: rest =>
        match firstDuplicateName (fn.params.map (·.name)) with
        | some dup => some (fn.name, dup)
        | none => goFns rest
  goFns fns

def firstDuplicateConstructorParamName
    (ctor : Option ConstructorSpec) : Option String :=
  match ctor with
  | none => none
  | some spec => firstDuplicateName (spec.params.map (·.name))

def firstDuplicateEventParamName
    (events : List EventDef) : Option (String × String) :=
  let rec goEvents : List EventDef → Option (String × String)
    | [] => none
    | ev :: rest =>
        match firstDuplicateName (ev.params.map (·.name)) with
        | some dup => some (ev.name, dup)
        | none => goEvents rest
  goEvents events

def dedupNatPreserve (xs : List Nat) : List Nat :=
  let rec go (seen : List Nat) : List Nat → List Nat
    | [] => []
    | x :: rest =>
        if seen.contains x then
          go seen rest
        else
          x :: go (x :: seen) rest
  go [] xs

private def slotAliasForSource (sourceSlot : Nat) (range : SlotAliasRange) : Option Nat :=
  if range.sourceStart <= sourceSlot && sourceSlot <= range.sourceEnd then
    some (range.targetStart + (sourceSlot - range.sourceStart))
  else
    none

private def derivedAliasSlotsForSource (sourceSlot : Nat) (ranges : List SlotAliasRange) : List Nat :=
  dedupNatPreserve (ranges.filterMap (slotAliasForSource sourceSlot))

def applySlotAliasRanges (fields : List Field) (ranges : List SlotAliasRange) : List Field :=
  let rec go (remaining : List Field) (idx : Nat) : List Field :=
    match remaining with
    | [] => []
    | f :: rest =>
        let sourceSlot := f.slot.getD idx
        let derivedAliases := derivedAliasSlotsForSource sourceSlot ranges
        let mergedAliases := dedupNatPreserve (f.aliasSlots ++ derivedAliases)
        ({ f with aliasSlots := mergedAliases } :: go rest (idx + 1))
  go fields 0

private def slotInReservedRange (slot : Nat) (range : ReservedSlotRange) : Bool :=
  range.start <= slot && slot <= range.end_

def firstInvalidReservedRange (ranges : List ReservedSlotRange) :
    Option (Nat × ReservedSlotRange) :=
  ranges.zipIdx.findSome? fun (range, idx) =>
    if range.end_ < range.start then
      some (idx, range)
    else
      none

private def rangesOverlap (a b : ReservedSlotRange) : Bool :=
  a.start <= b.end_ && b.start <= a.end_

def firstReservedRangeOverlap (ranges : List ReservedSlotRange) :
    Option (Nat × ReservedSlotRange × Nat × ReservedSlotRange) :=
  let rec goOuter (remaining : List ReservedSlotRange) (outerIdx : Nat) :
      Option (Nat × ReservedSlotRange × Nat × ReservedSlotRange) :=
    match remaining with
    | [] => none
    | current :: rest =>
        match rest.zipIdx.find? (fun (other, _) => rangesOverlap current other) with
        | some (other, innerOffset) => some (outerIdx, current, outerIdx + innerOffset + 1, other)
        | none => goOuter rest (outerIdx + 1)
  goOuter ranges 0

def firstInvalidSlotAliasRange (ranges : List SlotAliasRange) :
    Option (Nat × SlotAliasRange) :=
  ranges.zipIdx.findSome? fun (range, idx) =>
    if range.sourceEnd < range.sourceStart then
      some (idx, range)
    else
      none

private def slotAliasSourcesOverlap (a b : SlotAliasRange) : Bool :=
  a.sourceStart <= b.sourceEnd && b.sourceStart <= a.sourceEnd

def firstSlotAliasSourceOverlap (ranges : List SlotAliasRange) :
    Option (Nat × SlotAliasRange × Nat × SlotAliasRange) :=
  let rec goOuter (remaining : List SlotAliasRange) (outerIdx : Nat) :
      Option (Nat × SlotAliasRange × Nat × SlotAliasRange) :=
    match remaining with
    | [] => none
    | current :: rest =>
        match rest.zipIdx.find? (fun (other, _) => slotAliasSourcesOverlap current other) with
        | some (other, innerOffset) => some (outerIdx, current, outerIdx + innerOffset + 1, other)
        | none => goOuter rest (outerIdx + 1)
  goOuter ranges 0

def firstReservedSlotWriteConflict (fields : List Field)
    (ranges : List ReservedSlotRange) : Option (Nat × String × Nat × ReservedSlotRange) :=
  let rec goFields (remaining : List Field) (idx : Nat) : Option (Nat × String × Nat × ReservedSlotRange) :=
    match remaining with
    | [] => none
    | f :: rest =>
        let writeSlots : List (Nat × String) :=
          (f.slot.getD idx, f.name) ::
            (f.aliasSlots.zipIdx.map (fun (slot, aliasIdx) => (slot, s!"{f.name}.aliasSlots[{aliasIdx}]")))
        match writeSlots.findSome? (fun (slot, ownerName) =>
          match ranges.zipIdx.find? (fun (range, _) => slotInReservedRange slot range) with
          | some (range, rangeIdx) => some (slot, ownerName, rangeIdx, range)
          | none => none) with
        | some conflict => some conflict
        | none => goFields rest (idx + 1)
  goFields fields 0

def firstInvalidPackedBits (fields : List Field) :
    Option (String × PackedBits) :=
  let rec go (remaining : List Field) : Option (String × PackedBits) :=
    match remaining with
    | [] => none
    | f :: rest =>
        match f.packedBits with
        | some packed =>
            if packedBitsValid packed then
              go rest
            else
              some (f.name, packed)
        | none => go rest
  go fields

def firstMappingPackedBits (fields : List Field) :
    Option String :=
  let rec go (remaining : List Field) : Option String :=
    match remaining with
    | [] => none
    | f :: rest =>
        match f.ty, f.packedBits with
        | FieldType.mappingTyped _, some _ => some f.name
        | FieldType.mappingStruct _ _, some _ => some f.name
        | FieldType.mappingStruct2 _ _ _, some _ => some f.name
        | _, _ => go rest
  go fields

/-- Validate struct member definitions within a mappingStruct/mappingStruct2 field.
    Checks: (1) no duplicate member names, (2) packed ranges are valid,
    (3) no conflicting members sharing the same word offset:
        full-word with anything, or overlapping packed ranges. -/
def validateStructMembers (fieldName : String) (members : List StructMember) : Except String Unit := do
  match firstDuplicateName (members.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: struct field '{fieldName}' has duplicate member name '{dup}'"
  | none =>
      pure ()
  for m in members do
    match m.packed with
    | none => pure ()
    | some packed =>
        if !packedBitsValid packed then
          throw s!"Compilation error: struct field '{fieldName}' member '{m.name}' has invalid packed range offset={packed.offset} width={packed.width}. Require 0 < width <= 256, offset < 256, and offset + width <= 256."
  let rec firstSameWordConflict (seen : List StructMember) : List StructMember → Option (StructMember × StructMember)
    | [] => none
    | m :: rest =>
        match seen.find? (fun prev => prev.wordOffset == m.wordOffset && packedSlotsConflict prev.packed m.packed) with
        | some prev => some (prev, m)
        | none => firstSameWordConflict (m :: seen) rest
  match firstSameWordConflict [] members with
  | some (a, b) =>
      throw s!"Compilation error: struct field '{fieldName}' has overlapping/conflicting members '{a.name}' and '{b.name}' at wordOffset {a.wordOffset}."
  | none =>
      pure ()

/-- Find the first struct field with invalid member definitions (if any). -/
def firstInvalidStructField (fields : List Field) : Except String Unit := do
  for f in fields do
    match f.ty with
    | FieldType.mappingStruct _ members => validateStructMembers f.name members
    | FieldType.mappingStruct2 _ _ members => validateStructMembers f.name members
    | _ => pure ()

def firstFieldWriteSlotConflict (fields : List Field) : Option (Nat × String × String) :=
  let rec go (seen : List (Nat × String × Option PackedBits)) (idx : Nat) :
      List Field → Option (Nat × String × String)
    | [] => none
    | f :: rest =>
      let writeSlots : List (Nat × String × Option PackedBits) :=
        (f.slot.getD idx, f.name, f.packedBits) ::
          (f.aliasSlots.zipIdx.map (fun (slot, aliasIdx) =>
            (slot, s!"{f.name}.aliasSlots[{aliasIdx}]", f.packedBits)))
      let rec firstInFieldConflict (seenSlots : List (Nat × String × Option PackedBits)) :
          List (Nat × String × Option PackedBits) → Option (Nat × String × String)
        | [] => none
        | (slot, ownerName, packed) :: tail =>
            match seenSlots.find? (fun entry => entry.1 == slot && packedSlotsConflict entry.2.2 packed) with
            | some (_, prevName, _) => some (slot, prevName, ownerName)
            | none => firstInFieldConflict ((slot, ownerName, packed) :: seenSlots) tail
      match firstInFieldConflict seen writeSlots with
      | some conflict => some conflict
      | none => go (writeSlots.reverse ++ seen) (idx + 1) rest
  go [] 0 fields

end Compiler.CompilationModel
