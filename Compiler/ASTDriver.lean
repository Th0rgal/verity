/-
  Compiler.ASTDriver: AST-Based Compilation Pipeline

  Compiles `ASTContractSpec` to Yul output files using `ASTCompile` for
  function bodies, reusing the existing `Codegen`/`Linker`/`PrettyPrint`
  infrastructure.

  Pipeline: ASTContractSpec → IRContract → YulObject → .yul file

  This is Phase 4 of issue #364 (Unify EDSL/ContractSpec).
-/

import Std
import Compiler.ASTSpecs
import Compiler.ASTCompile
import Compiler.IR
import Compiler.Codegen
import Compiler.Yul.PrettyPrint
import Compiler.Linker
import Compiler.Hex

namespace Compiler.ASTDriver

open Compiler
open Compiler.Yul
open Compiler.ASTSpecs
open Compiler.ASTCompile (compileStmt)
open Compiler.ContractSpec (ParamType Param genParamLoads paramTypeToSolidityString)
open Compiler.Linker
open Compiler.Hex

/-!
## Selector Computation

Computes Solidity selectors for AST functions using the same keccak256
script as the ContractSpec path.
-/

private def functionSignature (fn : ASTFunctionSpec) : String :=
  let params := fn.params.map (fun p => paramTypeToSolidityString p.ty)
  let paramStr := String.intercalate "," params
  s!"{fn.name}({paramStr})"

private def runKeccak (sigs : List String) : IO (List Nat) := do
  if sigs.isEmpty then
    return []
  let args := #["scripts/keccak256.py"] ++ sigs.toArray
  let result ← IO.Process.output { cmd := "python3", args := args }
  if result.exitCode != 0 then
    throw (IO.userError s!"keccak256.py failed: {result.stderr}")
  let lines := result.stdout.trim.splitOn "\n"
  if lines.length != sigs.length then
    throw (IO.userError s!"keccak256.py returned {lines.length} lines for {sigs.length} signatures: {result.stdout}")
  let selectors := lines.filterMap fun line => parseHexNat? line.trim
  if selectors.length != sigs.length then
    throw (IO.userError s!"Failed to parse selector output: {result.stdout}")
  return selectors

def computeSelectors (spec : ASTContractSpec) : IO (List Nat) := do
  let sigs := spec.functions.map functionSignature
  runKeccak sigs

/-!
## Constructor Compilation

Loads constructor arguments by name (matching AST variable references)
then compiles the constructor body via `ASTCompile.compileStmt`.
-/

/-- Load constructor arguments from end of bytecode, binding them to their
    declared parameter names (not `arg0`, `arg1`, ...) so the AST body can
    reference them directly. -/
private def genConstructorArgLoads (params : List Param) : List YulStmt :=
  if params.isEmpty then []
  else
    let totalBytes := params.length * 32
    let argsOffset := [
      YulStmt.let_ "argsOffset" (YulExpr.call "sub" [
        YulExpr.call "codesize" [], YulExpr.lit totalBytes]),
      YulStmt.expr (YulExpr.call "codecopy" [
        YulExpr.lit 0, YulExpr.ident "argsOffset", YulExpr.lit totalBytes])
    ]
    let loadArgs := params.enum.flatMap fun (idx, param) =>
      let offset := idx * 32
      match param.ty with
      | ParamType.address =>
        [YulStmt.let_ param.name (YulExpr.call "and" [
          YulExpr.call "mload" [YulExpr.lit offset],
          YulExpr.hex ((2^160) - 1)
        ])]
      | _ =>
        [YulStmt.let_ param.name (YulExpr.call "mload" [YulExpr.lit offset])]
    argsOffset ++ loadArgs

mutual
  private partial def sanitizeConstructorStmts : List YulStmt → Except String (List YulStmt)
    | [] => pure []
    | stmt :: rest => do
        let stmt' ← sanitizeConstructorStmt stmt
        let rest' ← sanitizeConstructorStmts rest
        pure (stmt' ++ rest')

  private partial def sanitizeConstructorStmt (stmt : YulStmt) : Except String (List YulStmt) := do
    match stmt with
    | .expr (.call "stop" []) =>
      -- Constructor `Unit` should fall through to deploy epilogue, not halt EVM execution.
      pure []
    | .expr (.call "return" _args) =>
      throw "Constructor AST must not return runtime data directly"
    | .if_ cond body =>
      return [YulStmt.if_ cond (← sanitizeConstructorStmts body)]
    | .for_ init cond post body =>
      return [YulStmt.for_ (← sanitizeConstructorStmts init) cond (← sanitizeConstructorStmts post)
        (← sanitizeConstructorStmts body)]
    | .switch expr cases default =>
      let cases' ← cases.mapM fun (tag, caseBody) => do
        pure (tag, (← sanitizeConstructorStmts caseBody))
      let default' ← default.mapM sanitizeConstructorStmts
      return [YulStmt.switch expr cases' default']
    | .block body =>
      return [YulStmt.block (← sanitizeConstructorStmts body)]
    | other =>
      pure [other]
end

private def compileConstructor (ctor : Option ASTConstructorSpec) : Except String (List YulStmt) :=
  match ctor with
  | none => return []
  | some spec => do
    let body := compileStmt spec.body
    let body' ← sanitizeConstructorStmts body
    return genConstructorArgLoads spec.params ++ body'

/-!
## AST Spec Validation

Fail fast on malformed AST specs before any code generation work.
-/

private def ensureNonEmpty (kind name : String) : Except String Unit := do
  if name.trim.isEmpty then
    throw s!"{kind} name cannot be empty"

private def validateParamNames (kind : String) (params : List Param) : Except String Unit := do
  for param in params do
    ensureNonEmpty s!"{kind} parameter" param.name
  match findDuplicate (params.map (·.name)) with
  | some dup => throw s!"Duplicate {kind} parameter name: {dup}"
  | none => pure ()

private def validateSpec (spec : ASTContractSpec) : Except String Unit := do
  ensureNonEmpty "Contract" spec.name

  for fn in spec.functions do
    ensureNonEmpty s!"Function in {spec.name}" fn.name
    validateParamNames s!"function {fn.name}" fn.params

  match spec.constructor with
  | some ctor => validateParamNames s!"constructor of {spec.name}" ctor.params
  | none => pure ()

  match findDuplicate (spec.functions.map (·.name)) with
  | some dup => throw s!"Duplicate function name in {spec.name}: {dup}"
  | none => pure ()

private def validateAllSpecs (specs : List ASTContractSpec) : Except String Unit := do
  match findDuplicate (specs.map (·.name)) with
  | some dup => throw s!"Duplicate contract name in AST specs: {dup}"
  | none => pure ()

private def validateSelectorUniqueness (specName : String) (selectors : List Nat) : Except String Unit := do
  let selectorHex := selectors.map natToHex
  match findDuplicate selectorHex with
  | some dup => throw s!"Duplicate selector in {specName}: {dup}"
  | none => pure ()

/-!
## Function Compilation

For each external function:
1. Generate ABI calldata loading (reuses `ContractSpec.genParamLoads`)
2. Compile function body via `ASTCompile.compileStmt`
3. Package as `IRFunction`
-/

private def compileFunction (selector : Nat) (fn : ASTFunctionSpec) : IRFunction :=
  let paramLoads := genParamLoads fn.params
  let bodyStmts := compileStmt fn.body
  { name := fn.name
    selector := selector
    params := fn.params.map Compiler.ContractSpec.Param.toIRParam
    ret := match fn.returnType with
      | .uint256 => IRType.uint256
      | .address => IRType.address
      | .unit => IRType.unit
    body := paramLoads ++ bodyStmts }

/-!
## Contract Compilation

Assembles an `IRContract` from an `ASTContractSpec`, then uses the
existing `Codegen.emitYul` → `Yul.render` pipeline for output.
-/

def compileSpec (spec : ASTContractSpec) (selectors : List Nat) : Except String IRContract := do
  validateSpec spec
  if spec.functions.length != selectors.length then
    throw s!"Selector count mismatch for {spec.name}: {selectors.length} selectors for {spec.functions.length} functions"
  validateSelectorUniqueness spec.name selectors
  let functions := (spec.functions.zip selectors).map fun (fn, sel) =>
    compileFunction sel fn
  return {
    name := spec.name
    deploy := (← compileConstructor spec.constructor)
    functions := functions
    usesMapping := spec.usesMapping
  }

/-!
## Driver

Top-level entry point that compiles all AST-based contracts.
-/

private def orThrow (r : Except String Unit) : IO Unit :=
  match r with
  | .error err => throw (IO.userError err)
  | .ok () => pure ()

private def writeContract (outDir : String) (contract : IRContract) (libraryPaths : List String) (verbose : Bool) : IO Unit := do
  let yulObj := emitYul contract

  let libraries ← libraryPaths.mapM fun path => do
    if verbose then
      IO.println s!"  Loading library: {path}"
    loadLibrary path

  let allLibFunctions := libraries.flatten

  if !allLibFunctions.isEmpty then
    orThrow (validateNoDuplicateNames allLibFunctions)
    orThrow (validateNoNameCollisions yulObj allLibFunctions)
  orThrow (validateExternalReferences yulObj allLibFunctions)
  if !allLibFunctions.isEmpty then
    orThrow (validateCallArity yulObj allLibFunctions)

  let text ←
    if allLibFunctions.isEmpty then
      pure (Yul.render yulObj)
    else
      match renderWithLibraries yulObj allLibFunctions with
      | .error err => throw (IO.userError err)
      | .ok rendered => pure rendered

  let path := s!"{outDir}/{contract.name}.yul"
  IO.FS.writeFile path text

def compileAllAST (outDir : String) (verbose : Bool := false) (libraryPaths : List String := []) : IO Unit := do
  IO.FS.createDirAll outDir

  if verbose then
    IO.println "Using unified AST compilation path"
    IO.println ""

  orThrow (validateAllSpecs ASTSpecs.allSpecs)

  for spec in ASTSpecs.allSpecs do
    let selectors ← computeSelectors spec
    match compileSpec spec selectors with
    | .ok contract =>
      writeContract outDir contract libraryPaths verbose
      if verbose then
        IO.println s!"✓ Compiled {contract.name} (AST path)"
    | .error err =>
      throw (IO.userError err)

  if verbose then
    IO.println ""
    IO.println "AST compilation complete!"
    IO.println s!"Generated {ASTSpecs.allSpecs.length} contracts in {outDir}"

end Compiler.ASTDriver
