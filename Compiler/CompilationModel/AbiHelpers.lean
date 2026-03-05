import Compiler.CompilationModel.Types

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

def bytesFromString (s : String) : List UInt8 :=
  s.toUTF8.data.toList

def chunkBytes32 (bs : List UInt8) : List (List UInt8) :=
  if bs.isEmpty then
    []
  else
    let chunk := bs.take 32
    chunk :: chunkBytes32 (bs.drop 32)
termination_by bs.length
decreasing_by
  simp_wf
  cases bs with
  | nil => simp at *
  | cons head tail => simp; omega

def wordFromBytes (bs : List UInt8) : Nat :=
  let padded := bs ++ List.replicate (32 - bs.length) (0 : UInt8)
  padded.foldl (fun acc b => acc * 256 + b.toNat) 0

def revertWithMessage (message : String) : List YulStmt :=
  let bytes := bytesFromString message
  let len := bytes.length
  let paddedLen := ((len + 31) / 32) * 32
  let header := [
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 36, YulExpr.lit len])
  ]
  let dataStmts :=
    (chunkBytes32 bytes).zipIdx.map fun (chunk, idx) =>
      let offset := 68 + idx * 32
      let word := wordFromBytes chunk
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex word])
  let totalSize := 68 + paddedLen
  header ++ dataStmts ++ [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit totalSize])]

mutual
  def paramTypeToSolidityString : ParamType → String
    | ParamType.uint256 => "uint256"
    | ParamType.uint8 => "uint8"
    | ParamType.address => "address"
    | ParamType.bool => "bool"
    | ParamType.bytes32 => "bytes32"
    | ParamType.tuple ts =>
        "(" ++ String.intercalate "," (paramTypeListToSolidityStrings ts) ++ ")"
    | ParamType.array t => paramTypeToSolidityString t ++ "[]"
    | ParamType.fixedArray t n => paramTypeToSolidityString t ++ "[" ++ toString n ++ "]"
    | ParamType.bytes => "bytes"

  private def paramTypeListToSolidityStrings : List ParamType → List String
    | [] => []
    | ty :: rest => paramTypeToSolidityString ty :: paramTypeListToSolidityStrings rest
end

def eventSignature (eventDef : EventDef) : String :=
  let params := eventDef.params.map (fun p => paramTypeToSolidityString p.ty)
  s!"{eventDef.name}(" ++ String.intercalate "," params ++ ")"

def errorSignature (errorDef : ErrorDef) : String :=
  s!"{errorDef.name}(" ++ String.intercalate "," (errorDef.params.map paramTypeToSolidityString) ++ ")"

def fieldTypeToParamType : FieldType → ParamType
  | FieldType.uint256 => ParamType.uint256
  | FieldType.address => ParamType.address
  | FieldType.mappingTyped _ => ParamType.uint256
  | FieldType.mappingStruct _ _ => ParamType.uint256
  | FieldType.mappingStruct2 _ _ _ => ParamType.uint256

private def resolveReturns (context : String) (legacy : Option ParamType)
    (returns : List ParamType) : Except String (List ParamType) := do
  if returns.isEmpty then
    pure (legacy.map (fun ty => [ty]) |>.getD [])
  else
    match legacy with
    | none => pure returns
    | some ty =>
        if returns == [ty] then
          pure returns
        else
          throw s!"Compilation error: {context} has conflicting return declarations (returnType vs returns)"

def functionReturns (spec : FunctionSpec) : Except String (List ParamType) :=
  resolveReturns s!"function '{spec.name}'"
    (spec.returnType.map fieldTypeToParamType) spec.returns

def externalFunctionReturns (spec : ExternalFunction) : Except String (List ParamType) :=
  resolveReturns s!"external declaration '{spec.name}'" spec.returnType spec.returns

def functionStateMutability (spec : FunctionSpec) : String :=
  if spec.isPure then "pure"
  else if spec.isView then "view"
  else if spec.isPayable then "payable"
  else "nonpayable"

end Compiler.CompilationModel
