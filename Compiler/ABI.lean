import Std
import Compiler.CompilationModel
import Compiler.Json

namespace Compiler.ABI

open Compiler.CompilationModel
open Compiler.Json

private def joinJsonFields (fields : List String) : String :=
  String.intercalate ", " fields

private def abiTypeString : ParamType → String
  | .uint256 => "uint256"
  | .int256 => "int256"
  | .uint8 => "uint8"
  | .address => "address"
  | .bool => "bool"
  | .bytes32 => "bytes32"
  | .string => "string"
  | .bytes => "bytes"
  | .tuple _ => "tuple"
  | .array t => abiTypeString t ++ "[]"
  | .fixedArray t n => abiTypeString t ++ "[" ++ toString n ++ "]"
  | .adt _ _ => "tuple"  -- ADTs are ABI-encoded as static tuples
  | .newtypeOf _ baseType => abiTypeString baseType  -- Erased to base type

-- Uses `fieldTypeToParamType` from CompilationModel (shared, not duplicated).
-- Uses `isInteropEntrypointName` from CompilationModel for consistent filtering.

private def functionOutputs (fn : FunctionSpec) : List ParamType :=
  if !fn.returns.isEmpty then
    fn.returns
  else
    match fn.returnType with
    | some ty => [fieldTypeToParamType ty]
    | none => []

mutual
  private partial def abiComponents? : ParamType → Option String
    | .tuple elems =>
        let rendered := elems.map (fun ty => renderParam "" ty none)
        some ("[" ++ String.intercalate ", " rendered ++ "]")
    | .adt _ maxFields =>
        -- ADTs encode as (uint8 tag, uint256 field₀, ..., uint256 fieldₙ)
        let tagComponent := renderParam "tag" .uint8 none
        let fieldComponents := List.range maxFields |>.map fun i =>
          renderParam s!"field{i}" .uint256 none
        some ("[" ++ String.intercalate ", " (tagComponent :: fieldComponents) ++ "]")
    | .newtypeOf _ baseType => abiComponents? baseType
    | .array t => abiComponents? t
    | .fixedArray t _ => abiComponents? t
    | _ => none
  private partial def renderParam (name : String) (ty : ParamType) (indexed : Option Bool) : String :=
    let base := [
      s!"\"name\": {jsonString name}",
      s!"\"type\": {jsonString (abiTypeString ty)}"
    ]
    let withComponents :=
      match abiComponents? ty with
      | some components => base ++ [s!"\"components\": {components}"]
      | none => base
    let allFields :=
      match indexed with
      | some isIndexed => withComponents ++ [s!"\"indexed\": {(if isIndexed then "true" else "false")}"]
      | none => withComponents
    "{" ++ joinJsonFields allFields ++ "}"
end

private def renderFunctionEntry (fn : FunctionSpec) : String :=
  let inputs := fn.params.map (fun p => renderParam p.name p.ty none)
  let outputs := (functionOutputs fn).map (fun ty => renderParam "" ty none)
  let stateMutability := functionStateMutability fn
  "{" ++ joinJsonFields [
    "\"type\": \"function\"",
    s!"\"name\": {jsonString fn.name}",
    s!"\"inputs\": [" ++ String.intercalate ", " inputs ++ "]",
    s!"\"outputs\": [" ++ String.intercalate ", " outputs ++ "]",
    s!"\"stateMutability\": {jsonString stateMutability}"
  ] ++ "}"

private def renderEventEntry (ev : EventDef) : String :=
  let inputs := ev.params.map (fun p => renderParam p.name p.ty (some (p.kind == .indexed)))
  "{" ++ joinJsonFields [
    "\"type\": \"event\"",
    s!"\"name\": {jsonString ev.name}",
    s!"\"inputs\": [" ++ String.intercalate ", " inputs ++ "]",
    "\"anonymous\": false"
  ] ++ "}"

private def renderErrorEntry (err : ErrorDef) : String :=
  let inputs := err.params.map (fun ty => renderParam "" ty none)
  "{" ++ joinJsonFields [
    "\"type\": \"error\"",
    s!"\"name\": {jsonString err.name}",
    s!"\"inputs\": [" ++ String.intercalate ", " inputs ++ "]"
  ] ++ "}"

private def renderConstructorEntry (ctor : ConstructorSpec) : String :=
  let inputs := ctor.params.map (fun p => renderParam p.name p.ty none)
  let stateMutability := if ctor.isPayable then "payable" else "nonpayable"
  "{" ++ joinJsonFields [
    "\"type\": \"constructor\"",
    s!"\"inputs\": [" ++ String.intercalate ", " inputs ++ "]",
    s!"\"stateMutability\": {jsonString stateMutability}"
  ] ++ "}"

/-- Render an ABI entry for a special entrypoint (fallback/receive).
    Uses `isInteropEntrypointName` so this stays in sync with selector filtering.
    Returns `some` for special entrypoints, `none` otherwise (defensive guard
    even though the caller pre-filters via `isInteropEntrypointName`). -/
private def renderSpecialEntry (fn : FunctionSpec) : Option String :=
  if !isInteropEntrypointName fn.name then
    none
  else
    some ("{" ++ joinJsonFields [
      s!"\"type\": {jsonString fn.name}",
      s!"\"stateMutability\": {jsonString (functionStateMutability fn)}"
    ] ++ "}")

def emitContractABIJson (spec : CompilationModel) : String :=
  let ctorEntries :=
    match spec.constructor with
    | some ctor => [renderConstructorEntry ctor]
    | none => []
  let functionEntries := spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name) |>.map renderFunctionEntry
  let specialEntries := (spec.functions.filter (fun fn => !fn.isInternal && isInteropEntrypointName fn.name)).filterMap renderSpecialEntry
  let eventEntries := spec.events.map renderEventEntry
  let errorEntries := spec.errors.map renderErrorEntry
  let entries := ctorEntries ++ functionEntries ++ eventEntries ++ errorEntries ++ specialEntries
  "[\n  " ++ String.intercalate ",\n  " entries ++ "\n]\n"

def writeContractABIFile (outDir : String) (spec : CompilationModel) : IO Unit := do
  IO.FS.createDirAll outDir
  let path := s!"{outDir}/{spec.name}.abi.json"
  IO.FS.writeFile path (emitContractABIJson spec)

/-- Render the storage layout for a contract as a JSON object.
    Includes EIP-7201 namespace when present (#1730, Axis 4 Step 4d).
    The output is a JSON object with `"contract"`, `"storageNamespace"`,
    and `"fields"` keys. -/
def emitContractStorageLayoutJson (spec : CompilationModel) : String :=
  let nsTerm := match spec.storageNamespace with
    | some ns => jsonString (toString ns)
    | none => "null"
  let fieldEntries := renderFields spec.fields 0
  "{" ++ joinJsonFields [
    s!"\"contract\": {jsonString spec.name}",
    s!"\"storageNamespace\": {nsTerm}",
    s!"\"fields\": [{String.intercalate ", " fieldEntries}]"
  ] ++ "}\n"
where
  renderFieldType : FieldType → String
    | .uint256 => "uint256"
    | .address => "address"
    | .dynamicArray elemType => renderStorageArrayElemType elemType ++ "[]"
    | .mappingTyped _ => "mapping"
    | .mappingStruct _ _ => "mapping"
    | .mappingStruct2 _ _ _ => "mapping"
  renderStorageArrayElemType : StorageArrayElemType → String
    | .uint256 => "uint256"
    | .address => "address"
    | .bool => "bool"
    | .uint8 => "uint8"
    | .bytes32 => "bytes32"
  renderFields (fields : List Field) (idx : Nat) : List String :=
    match fields with
    | [] => []
    | f :: rest =>
        let slot := f.slot.getD idx
        let entry := "{" ++ joinJsonFields [
          s!"\"name\": {jsonString f.name}",
          s!"\"slot\": {toString slot}",
          s!"\"type\": {jsonString (renderFieldType f.ty)}"
        ] ++ "}"
        entry :: renderFields rest (idx + 1)

def writeContractStorageLayoutFile (outDir : String) (spec : CompilationModel) : IO Unit := do
  IO.FS.createDirAll outDir
  let path := s!"{outDir}/{spec.name}.storage.json"
  IO.FS.writeFile path (emitContractStorageLayoutJson spec)

end Compiler.ABI
