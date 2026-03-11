import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.LayoutValidation
import Compiler.Json

namespace Compiler.CompilationModel

open Compiler.Json

private def jsonNat (n : Nat) : String :=
  toString n

private def jsonOption (render : α → String) : Option α → String
  | some value => render value
  | none => "null"

private def mappingKeyTypeString : MappingKeyType → String
  | .address => "address"
  | .uint256 => "uint256"

private def mappingKeysJson (keys : List MappingKeyType) : String :=
  jsonArray (keys.map (fun keyType => jsonString (mappingKeyTypeString keyType)))

private def packedBitsJson (packed : PackedBits) : String :=
  jsonObject [
    ("offset", jsonNat packed.offset),
    ("width", jsonNat packed.width)
  ]

private def structMemberJson (member : StructMember) : String :=
  jsonObject [
    ("name", jsonString member.name),
    ("wordOffset", jsonNat member.wordOffset),
    ("packedBits", jsonOption packedBitsJson member.packed)
  ]

private def fieldTypeJson : FieldType → String
  | .uint256 =>
      jsonObject [("kind", jsonString "uint256")]
  | .address =>
      jsonObject [("kind", jsonString "address")]
  | .dynamicArray elemType =>
      jsonObject [
        ("kind", jsonString "dynamicArray"),
        ("elemType", jsonString (paramTypeToSolidityString (storageArrayElemTypeToParamType elemType)))
      ]
  | .mappingTyped mt =>
      jsonObject [
        ("kind", jsonString "mapping"),
        ("keys", mappingKeysJson (mappingTypeKeyTypes mt)),
        ("valueKind", jsonString "uint256")
      ]
  | .mappingStruct keyType members =>
      jsonObject [
        ("kind", jsonString "mappingStruct"),
        ("keys", jsonArray [jsonString (mappingKeyTypeString keyType)]),
        ("members", jsonArray (members.map structMemberJson))
      ]
  | .mappingStruct2 outer inner members =>
      jsonObject [
        ("kind", jsonString "mappingStruct"),
        ("keys", jsonArray [jsonString (mappingKeyTypeString outer), jsonString (mappingKeyTypeString inner)]),
        ("members", jsonArray (members.map structMemberJson))
      ]

private def reservedSlotRangeJson (range : ReservedSlotRange) : String :=
  jsonObject [
    ("start", jsonNat range.start),
    ("end", jsonNat range.end_)
  ]

private def slotAliasRangeJson (range : SlotAliasRange) : String :=
  jsonObject [
    ("sourceStart", jsonNat range.sourceStart),
    ("sourceEnd", jsonNat range.sourceEnd),
    ("targetStart", jsonNat range.targetStart)
  ]

private def fieldJson (declaredField effectiveField : Field) (idx : Nat) : String :=
  let canonicalSlot := declaredField.slot.getD idx
  let effectiveAliasSlots := effectiveField.aliasSlots
  jsonObject [
    ("name", jsonString declaredField.name),
    ("declaredSlot", jsonOption jsonNat declaredField.slot),
    ("canonicalSlot", jsonNat canonicalSlot),
    ("declaredAliasSlots", jsonArray (declaredField.aliasSlots.map jsonNat)),
    ("effectiveAliasSlots", jsonArray (effectiveAliasSlots.map jsonNat)),
    ("writeSlots", jsonArray ((canonicalSlot :: effectiveAliasSlots).map jsonNat)),
    ("type", fieldTypeJson declaredField.ty),
    ("packedBits", jsonOption packedBitsJson declaredField.packedBits)
  ]

/-- Render a machine-readable storage layout report for upgrade/layout auditing. -/
def emitLayoutReportJson (specs : List CompilationModel) : String :=
  jsonObject [
    ("contracts", jsonArray (specs.map contractJson))
  ]
where
  contractJson (spec : CompilationModel) : String :=
    let effectiveFields := applySlotAliasRanges spec.fields spec.slotAliasRanges
    let fieldsJson :=
      (spec.fields.zip effectiveFields).zipIdx.map fun ((declaredField, effectiveField), idx) =>
        fieldJson declaredField effectiveField idx
    jsonObject [
      ("contract", jsonString spec.name),
      ("fields", jsonArray fieldsJson),
      ("reservedSlotRanges", jsonArray (spec.reservedSlotRanges.map reservedSlotRangeJson)),
      ("slotAliasRanges", jsonArray (spec.slotAliasRanges.map slotAliasRangeJson))
    ]

end Compiler.CompilationModel
