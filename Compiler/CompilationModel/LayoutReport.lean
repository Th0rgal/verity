import Compiler.CompilationModel.Types
import Compiler.CompilationModel.LayoutValidation

namespace Compiler.CompilationModel

private def escapeJsonChar (c : Char) : String :=
  match c with
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | _ => String.singleton c

private def escapeJsonString (s : String) : String :=
  s.data.foldl (fun acc c => acc ++ escapeJsonChar c) ""

private def jsonString (s : String) : String :=
  "\"" ++ escapeJsonString s ++ "\""

private def jsonNat (n : Nat) : String :=
  toString n

private def jsonArray (items : List String) : String :=
  "[" ++ String.intercalate "," items ++ "]"

private def jsonObject (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map fun (name, value) => jsonString name ++ ":" ++ value) ++ "}"

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
  | .mappingTyped (.simple keyType) =>
      jsonObject [
        ("kind", jsonString "mapping"),
        ("keys", jsonArray [jsonString (mappingKeyTypeString keyType)]),
        ("valueKind", jsonString "uint256")
      ]
  | .mappingTyped (.nested outer inner) =>
      jsonObject [
        ("kind", jsonString "mapping"),
        ("keys", jsonArray [jsonString (mappingKeyTypeString outer), jsonString (mappingKeyTypeString inner)]),
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
