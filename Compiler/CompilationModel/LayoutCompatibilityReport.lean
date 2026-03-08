import Compiler.CompilationModel.LayoutReport
import Compiler.Json

namespace Compiler.CompilationModel

open Compiler.Json

private def jsonNat (n : Nat) : String :=
  toString n

private def jsonBool (b : Bool) : String :=
  if b then "true" else "false"

private def jsonOption (render : α → String) : Option α → String
  | some value => render value
  | none => "null"

private def mappingKeyTypeString : MappingKeyType → String
  | .address => "address"
  | .uint256 => "uint256"

private def packedBitsJson (packed : PackedBits) : String :=
  jsonObject [
    ("offset", jsonNat packed.offset),
    ("width", jsonNat packed.width)
  ]

private def fieldTypeSummary : FieldType → String
  | .uint256 => "uint256"
  | .address => "address"
  | .mappingTyped (.simple keyType) =>
      s!"mapping({mappingKeyTypeString keyType}=>uint256)"
  | .mappingTyped (.nested outer inner) =>
      s!"mapping({mappingKeyTypeString outer}=>mapping({mappingKeyTypeString inner}=>uint256))"
  | .mappingStruct keyType members =>
      s!"mappingStruct({mappingKeyTypeString keyType};members={members.length})"
  | .mappingStruct2 outer inner members =>
      s!"mappingStruct({mappingKeyTypeString outer},{mappingKeyTypeString inner};members={members.length})"

private structure FieldLayoutInfo where
  name : String
  ty : FieldType
  canonicalSlot : Nat
  effectiveAliasSlots : List Nat
  writeSlots : List Nat
  packedBits : Option PackedBits

private def fieldLayoutInfo (declaredField effectiveField : Field) (idx : Nat) : FieldLayoutInfo :=
  let canonicalSlot := declaredField.slot.getD idx
  let effectiveAliasSlots := effectiveField.aliasSlots
  { name := declaredField.name
    ty := declaredField.ty
    canonicalSlot := canonicalSlot
    effectiveAliasSlots := effectiveAliasSlots
    writeSlots := canonicalSlot :: effectiveAliasSlots
    packedBits := declaredField.packedBits }

private def collectFieldLayouts
    (declaredFields effectiveFields : List Field)
    (idx : Nat := 0) : List FieldLayoutInfo :=
  match declaredFields, effectiveFields with
  | declaredField :: declaredRest, effectiveField :: effectiveRest =>
      fieldLayoutInfo declaredField effectiveField idx ::
        collectFieldLayouts declaredRest effectiveRest (idx + 1)
  | _, _ => []

private def fieldLayouts (spec : CompilationModel) : List FieldLayoutInfo :=
  let effectiveFields := applySlotAliasRanges spec.fields spec.slotAliasRanges
  collectFieldLayouts spec.fields effectiveFields

private def findFieldLayout? (fields : List FieldLayoutInfo) (name : String) : Option FieldLayoutInfo :=
  fields.find? (fun field => field.name == name)

private def overlappingSlots (lhs rhs : List Nat) : List Nat :=
  lhs.foldl
    (fun acc slot =>
      if rhs.elem slot && !(acc.elem slot) then
        acc ++ [slot]
      else
        acc)
    []

private def slotsWithinReservedRanges
    (ranges : List ReservedSlotRange)
    (slots : List Nat) : List Nat :=
  slots.foldl
    (fun acc slot =>
      if ranges.any (fun range => range.start <= slot && slot <= range.end_) then
        if acc.elem slot then acc else acc ++ [slot]
      else
        acc)
    []

private def slotListSummary (slots : List Nat) : String :=
  "[" ++ String.intercalate ", " (slots.map toString) ++ "]"

private def fieldPreserved (baseline candidate : FieldLayoutInfo) : Bool :=
  baseline.ty == candidate.ty &&
    baseline.canonicalSlot == candidate.canonicalSlot &&
    baseline.effectiveAliasSlots == candidate.effectiveAliasSlots &&
    baseline.packedBits == candidate.packedBits

private inductive LayoutCompatibilityChangeKind
  | missingField
  | typeChanged
  | canonicalSlotChanged
  | aliasSlotsChanged
  | packedBitsChanged
  | newFieldOverlapsBaselineWriteSet
  deriving BEq

private structure LayoutCompatibilityChange where
  field : String
  kind : LayoutCompatibilityChangeKind
  baseline : String := ""
  candidate : String := ""

private structure ReservedSlotConsumption where
  field : String
  slots : List Nat

private def compatibilityChanges
    (baseline candidate : CompilationModel) : List LayoutCompatibilityChange :=
  let baselineFields := fieldLayouts baseline
  let candidateFields := fieldLayouts candidate
  let baselineWriteSlots :=
    baselineFields.foldl (fun acc field => acc ++ field.writeSlots) []
  let baselineChanges :=
    baselineFields.foldl
      (fun acc baselineField =>
        match findFieldLayout? candidateFields baselineField.name with
        | none =>
            acc ++ [{
              field := baselineField.name
              kind := .missingField
            }]
        | some candidateField =>
            let acc :=
              if baselineField.ty == candidateField.ty then
                acc
              else
                acc ++ [{
                  field := baselineField.name
                  kind := .typeChanged
                  baseline := fieldTypeSummary baselineField.ty
                  candidate := fieldTypeSummary candidateField.ty
                }]
            let acc :=
              if baselineField.canonicalSlot == candidateField.canonicalSlot then
                acc
              else
                acc ++ [{
                  field := baselineField.name
                  kind := .canonicalSlotChanged
                  baseline := toString baselineField.canonicalSlot
                  candidate := toString candidateField.canonicalSlot
                }]
            let acc :=
              if baselineField.effectiveAliasSlots == candidateField.effectiveAliasSlots then
                acc
              else
                acc ++ [{
                  field := baselineField.name
                  kind := .aliasSlotsChanged
                  baseline := slotListSummary baselineField.effectiveAliasSlots
                  candidate := slotListSummary candidateField.effectiveAliasSlots
                }]
            if baselineField.packedBits == candidateField.packedBits then
              acc
            else
              acc ++ [{
                field := baselineField.name
                kind := .packedBitsChanged
                baseline := jsonOption packedBitsJson baselineField.packedBits
                candidate := jsonOption packedBitsJson candidateField.packedBits
              }])
      []
  let newFieldChanges :=
    candidateFields.foldl
      (fun acc candidateField =>
        match findFieldLayout? baselineFields candidateField.name with
        | some _ => acc
        | none =>
            let overlaps := overlappingSlots candidateField.writeSlots baselineWriteSlots
            if overlaps.isEmpty then
              acc
            else
              acc ++ [{
                field := candidateField.name
                kind := .newFieldOverlapsBaselineWriteSet
                candidate := slotListSummary overlaps
              }])
      []
  baselineChanges ++ newFieldChanges

private def preservedFields
    (baseline candidate : CompilationModel) : List String :=
  let candidateFields := fieldLayouts candidate
  (fieldLayouts baseline).foldl
    (fun acc baselineField =>
      match findFieldLayout? candidateFields baselineField.name with
      | some candidateField =>
          if fieldPreserved baselineField candidateField then
            acc ++ [baselineField.name]
          else
            acc
      | none => acc)
    []

private def addedFields
    (baseline candidate : CompilationModel) : List FieldLayoutInfo :=
  let baselineFields := fieldLayouts baseline
  (fieldLayouts candidate).foldl
    (fun acc candidateField =>
      match findFieldLayout? baselineFields candidateField.name with
      | some _ => acc
      | none => acc ++ [candidateField])
    []

private def reservedSlotConsumption
    (baseline candidate : CompilationModel) : List ReservedSlotConsumption :=
  (addedFields baseline candidate).foldl
    (fun acc candidateField =>
      let consumedSlots := slotsWithinReservedRanges baseline.reservedSlotRanges candidateField.writeSlots
      if consumedSlots.isEmpty then
        acc
      else
        acc ++ [{ field := candidateField.name, slots := consumedSlots }])
    []

private def changeKindString : LayoutCompatibilityChangeKind → String
  | .missingField => "missingField"
  | .typeChanged => "typeChanged"
  | .canonicalSlotChanged => "canonicalSlotChanged"
  | .aliasSlotsChanged => "aliasSlotsChanged"
  | .packedBitsChanged => "packedBitsChanged"
  | .newFieldOverlapsBaselineWriteSet => "newFieldOverlapsBaselineWriteSet"

private def reservedSlotConsumptionJson (entry : ReservedSlotConsumption) : String :=
  jsonObject [
    ("field", jsonString entry.field),
    ("slots", jsonArray (entry.slots.map jsonNat))
  ]

private def changeJson (change : LayoutCompatibilityChange) : String :=
  jsonObject [
    ("field", jsonString change.field),
    ("kind", jsonString (changeKindString change.kind)),
    ("baseline", jsonString change.baseline),
    ("candidate", jsonString change.candidate)
  ]

def emitIncompatibleLayoutChangeLines
    (baseline candidate : CompilationModel) : List String :=
  (compatibilityChanges baseline candidate).map fun change =>
    match change.kind with
    | .missingField =>
        s!"- missing baseline field '{change.field}' in candidate layout"
    | .typeChanged =>
        s!"- field '{change.field}' changed type: {change.baseline} -> {change.candidate}"
    | .canonicalSlotChanged =>
        s!"- field '{change.field}' moved slots: {change.baseline} -> {change.candidate}"
    | .aliasSlotsChanged =>
        s!"- field '{change.field}' changed alias slots: {change.baseline} -> {change.candidate}"
    | .packedBitsChanged =>
        s!"- field '{change.field}' changed packed-bit layout"
    | .newFieldOverlapsBaselineWriteSet =>
        s!"- new field '{change.field}' overlaps baseline write slots {change.candidate}"

/-- Render a machine-readable storage-layout compatibility report comparing a
baseline contract layout to a candidate upgrade layout. -/
def emitLayoutCompatibilityReportJson
    (baseline candidate : CompilationModel) : String :=
  let preserved := preservedFields baseline candidate
  let added := addedFields baseline candidate
  let reservedConsumptionEntries := reservedSlotConsumption baseline candidate
  let incompatibleChanges := compatibilityChanges baseline candidate
  jsonObject [
    ("baselineContract", jsonString baseline.name),
    ("candidateContract", jsonString candidate.name),
    ("compatible", jsonBool incompatibleChanges.isEmpty),
    ("preservedFields", jsonArray (preserved.map jsonString)),
    ("addedFields", jsonArray (added.map (fun field => jsonString field.name))),
    ("reservedSlotConsumption", jsonArray (reservedConsumptionEntries.map reservedSlotConsumptionJson)),
    ("incompatibleChanges", jsonArray (incompatibleChanges.map changeJson))
  ]

end Compiler.CompilationModel
