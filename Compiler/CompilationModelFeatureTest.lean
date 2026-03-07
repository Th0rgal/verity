import Compiler.CompilationModel

namespace Compiler.CompilationModelFeatureTest

open Compiler
open Compiler.CompilationModel

private def expectTrue (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"✗ {label}")
  IO.println s!"✓ {label}"

private def contains (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then true
  else
    let rec go : List Char → Bool
      | [] => false
      | c :: cs =>
        if (c :: cs).take n.length == n then true
        else go cs
    go h

private def selectorCount (spec : CompilationModel) : Nat :=
  (spec.functions.filter (fun fn => !fn.isInternal && fn.name != "fallback" && fn.name != "receive")).length

private def selectorsFor (spec : CompilationModel) : List Nat :=
  List.range (selectorCount spec)

private def expectCompileErrorContains (label : String)
    (spec : CompilationModel) (needle : String) : IO Unit := do
  match Compiler.CompilationModel.compile spec (selectorsFor spec) with
  | .ok _ =>
      throw (IO.userError s!"✗ {label}: expected compile failure")
  | .error msg =>
      expectTrue label (contains msg needle)

private def selectorSmokeSpec : CompilationModel := {
  name := "SelectorSmoke"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.setStorage "value" (Expr.param "next"),
        Stmt.stop
      ]
    },
    { name := "load"
      params := []
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.storage "value")]
    }
  ]
}

private def reservedParamSpec : CompilationModel := {
  name := "ReservedParam"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "__has_selector", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.setStorage "value" (Expr.param "__has_selector"),
        Stmt.stop
      ]
    }
  ]
}

private def reservedLocalBinderSpec : CompilationModel := {
  name := "ReservedLocalBinder"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.letVar "__has_selector" (Expr.param "next"),
        Stmt.setStorage "value" (Expr.localVar "__has_selector"),
        Stmt.stop
      ]
    }
  ]
}

#eval! do
  let compiled :=
    match Compiler.CompilationModel.compile selectorSmokeSpec (selectorsFor selectorSmokeSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "local CompilationModel smoke spec compiles with deterministic selectors" compiled

  -- Regression: selector mismatch must fail closed.
  let mismatchRejected :=
    match Compiler.CompilationModel.compile selectorSmokeSpec [] with
    | .ok _ => false
    | .error msg => contains msg "Selector count mismatch"
  expectTrue "selector mismatch is rejected with deterministic diagnostic" mismatchRejected
  expectCompileErrorContains
    "reserved compiler prefix is rejected in function parameters"
    reservedParamSpec
    "function parameter '__has_selector' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in local binders"
    reservedLocalBinderSpec
    "local binder '__has_selector' uses reserved compiler prefix '__'"

end Compiler.CompilationModelFeatureTest
