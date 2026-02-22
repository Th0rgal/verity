import Std
import Compiler.ContractSpec

namespace Compiler.ABI

open Compiler.ContractSpec

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

private def joinJsonFields (fields : List String) : String :=
  String.intercalate ", " fields

private partial def abiTypeString : ParamType → String
  | .uint256 => "uint256"
  | .address => "address"
  | .bool => "bool"
  | .bytes32 => "bytes32"
  | .bytes => "bytes"
  | .tuple _ => "tuple"
  | .array t => abiTypeString t ++ "[]"
  | .fixedArray t n => abiTypeString t ++ "[" ++ toString n ++ "]"

-- Uses `fieldTypeToParamType` from ContractSpec (shared, not duplicated).
-- Uses `isInteropEntrypointName` from ContractSpec for consistent filtering.

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
  let stateMutability := if fn.isPayable then "payable" else "nonpayable"
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
    The caller (`emitContractABIJson`) already filters to `isInteropEntrypointName`
    entries, so this always returns `some` for valid input. -/
private def renderSpecialEntry (fn : FunctionSpec) : Option String :=
  if !isInteropEntrypointName fn.name then
    none
  else
    some ("{" ++ joinJsonFields [
      s!"\"type\": {jsonString fn.name}",
      s!"\"stateMutability\": {jsonString (if fn.isPayable then "payable" else "nonpayable")}"
    ] ++ "}")

def emitContractABIJson (spec : ContractSpec) : String :=
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

def writeContractABIFile (outDir : String) (spec : ContractSpec) : IO Unit := do
  IO.FS.createDirAll outDir
  let path := s!"{outDir}/{spec.name}.abi.json"
  IO.FS.writeFile path (emitContractABIJson spec)

end Compiler.ABI
