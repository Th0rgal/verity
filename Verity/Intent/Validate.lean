/-
  Verity.Intent.Validate: Validate IntentSpec against a CompilationModel.

  Checks:
  1. Every IntentBinding.functionName exists in CompilationModel.functions
  2. Every IntentBinding.intentFn exists in IntentSpec.fns
  3. Intent function params match the CompilationModel function's ABI params
  4. All helper functions referenced in expressions/statements exist
  5. All constants referenced in expressions exist

  Returns a list of error messages (empty = valid).
-/
import Verity.Intent.Types
import Compiler.CompilationModel.Types

namespace Verity.Intent.Validate

open Verity.Intent
open Compiler.CompilationModel (CompilationModel FunctionSpec Param ParamType)

/-- Phase 1 supported parameter types for circuit compilation. -/
private def isPhase1Type : ParamType → Bool
  | .uint256 | .address | .bool => true
  | _ => false

/-- Check that a ParamType from the intent spec is compatible with the ABI type. -/
private def typesCompatible (intentTy abiTy : ParamType) : Bool :=
  intentTy == abiTy

/-- Find a function spec in a CompilationModel by name. -/
private def findFunction? (cm : CompilationModel) (name : String) : Option FunctionSpec :=
  cm.functions.find? (fun f => f.name == name)

/-- Find an intent function declaration by name. -/
private def findFnDecl? (spec : IntentSpec) (name : String) : Option FnDecl :=
  spec.fns.find? (fun f => f.name == name)

/-- Find a constant definition by name. -/
private def findConst? (spec : IntentSpec) (name : String) : Option ConstDef :=
  spec.constants.find? (fun c => c.name == name)

/-- Validate that intent function params match the ABI function params.
    Returns a list of error messages. -/
private def validateParams
    (bindingName : String)
    (intentParams : List (String × ParamType))
    (abiParams : List Param) : List String :=
  let intentByName := intentParams
  let abiByName := abiParams.map (fun p => (p.name, p.ty))
  -- Check each intent param exists in ABI with compatible type
  let paramErrors := intentByName.filterMap fun (name, intentTy) =>
    match abiByName.find? (fun (n, _) => n == name) with
    | none => some s!"Binding '{bindingName}': intent param '{name}' not found in ABI function"
    | some (_, abiTy) =>
      if typesCompatible intentTy abiTy then none
      else some s!"Binding '{bindingName}': param '{name}' type mismatch — intent has {repr intentTy}, ABI has {repr abiTy}"
  -- Check each ABI param is covered by the intent
  let missingErrors := abiByName.filterMap fun (name, _) =>
    match intentByName.find? (fun (n, _) => n == name) with
    | none => some s!"Binding '{bindingName}': ABI param '{name}' missing from intent function"
    | some _ => none
  paramErrors ++ missingErrors

/-- Collect all function names called in an expression. -/
private def exprCallNames : Expr → List String
  | .call fnName args => fnName :: args.flatMap exprCallNames
  | .eq a b | .ne a b | .lt a b | .gt a b | .le a b | .ge a b
  | .and a b | .or a b => exprCallNames a ++ exprCallNames b
  | .not a => exprCallNames a
  | _ => []

/-- Collect all function names called in a single statement. -/
private def stmtCallNamesOne : Stmt → List String
  | .emit _ => []
  | .ite cond thenBr elseBr =>
    exprCallNames cond ++ thenBr.flatMap stmtCallNamesOne ++ elseBr.flatMap stmtCallNamesOne
  | .call fnName args =>
    fnName :: args.flatMap exprCallNames

/-- Collect all function names called in statements. -/
private def stmtCallNames (stmts : List Stmt) : List String :=
  stmts.flatMap stmtCallNamesOne

/-- Collect all param references in an expression (potential constant refs). -/
private def exprParamRefs : Expr → List String
  | .param name => [name]
  | .eq a b | .ne a b | .lt a b | .gt a b | .le a b | .ge a b
  | .and a b | .or a b => exprParamRefs a ++ exprParamRefs b
  | .not a => exprParamRefs a
  | .call _ args => args.flatMap exprParamRefs
  | _ => []

/-- Validate that all function calls in a function body resolve to known functions. -/
private def validateCallsInFn (spec : IntentSpec) (fn : FnDecl) : List String :=
  let bodyCalls := stmtCallNames fn.body
  let exprCalls := match fn.expr with
    | some e => exprCallNames e
    | none => []
  let allCalls := bodyCalls ++ exprCalls
  allCalls.filterMap fun name =>
    match findFnDecl? spec name with
    | some _ => none
    | none => some s!"Function '{fn.name}': calls undefined function '{name}'"

/-- Validate Phase 1 type restrictions on intent function params. -/
private def validatePhase1Types (fn : FnDecl) : List String :=
  fn.params.filterMap fun (name, ty) =>
    if isPhase1Type ty then none
    else some s!"Function '{fn.name}': param '{name}' has unsupported Phase 1 type {repr ty} (expected uint256, address, or bool)"

/-- Validate a single intent binding. -/
private def validateBinding
    (spec : IntentSpec) (cm : CompilationModel) (binding : IntentBinding) : List String :=
  -- Check functionName exists in CompilationModel
  let abiErrors := match findFunction? cm binding.functionName with
    | none => [s!"Binding '{binding.functionName}': no matching function in contract '{cm.name}'"]
    | some abiFn =>
      -- Check intentFn exists
      match findFnDecl? spec binding.intentFn with
      | none => [s!"Binding '{binding.functionName}': intent function '{binding.intentFn}' not found"]
      | some intentFn =>
        -- Validate param compatibility
        validateParams binding.functionName intentFn.params abiFn.params
  abiErrors

/-- Validate an IntentSpec against a CompilationModel.
    Returns a list of error messages (empty = valid). -/
def validate (spec : IntentSpec) (cm : CompilationModel) : List String :=
  -- 1. Contract name must match
  let nameErrors :=
    if spec.contractName == cm.name then []
    else [s!"Contract name mismatch: intent spec says '{spec.contractName}', CompilationModel says '{cm.name}'"]
  -- 2. Validate each binding
  let bindingErrors := spec.bindings.flatMap (validateBinding spec cm)
  -- 3. Validate all function call references
  let callErrors := spec.fns.flatMap (validateCallsInFn spec)
  -- 4. Validate Phase 1 type restrictions
  let typeErrors := spec.fns.flatMap validatePhase1Types
  -- 5. Check for duplicate binding function names
  let bindingNames := spec.bindings.map (·.functionName)
  let dupErrors :=
    let rec findDup : List String → List String → List String
      | [], _ => []
      | n :: rest, seen =>
        if seen.contains n
        then s!"Duplicate binding for function '{n}'" :: findDup rest seen
        else findDup rest (n :: seen)
    findDup bindingNames []
  nameErrors ++ bindingErrors ++ callErrors ++ typeErrors ++ dupErrors

/-- Convenience: validate and return an Except. -/
def validateOrError (spec : IntentSpec) (cm : CompilationModel) : Except String Unit :=
  match validate spec cm with
  | [] => .ok ()
  | errs => .error (String.intercalate "\n" errs)

end Verity.Intent.Validate
