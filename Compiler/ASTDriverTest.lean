import Compiler.ASTDriver
import Compiler.ASTSpecs
import Compiler.Yul.PrettyPrint
import Verity.AST

/- Regression tests for AST driver constructor handling. -/
namespace Compiler.ASTDriverTest

open Compiler.ASTDriver
open Compiler.ASTSpecs
open Verity.AST

/-- Render deploy statements to a single string for assertions. -/
private def renderDeploy (stmts : List Yul.YulStmt) : String :=
  String.intercalate "\n" (Yul.ppStmts 0 stmts)

/-- Check that a string contains a substring. -/
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

/-- Assert that rendered output contains expected substrings. -/
private def assertContains (label rendered : String) (needles : List String) : IO Unit := do
  for needle in needles do
    if !contains rendered needle then
      throw (IO.userError s!"✗ {label}: missing '{needle}' in:\n{rendered}")
  IO.println s!"✓ {label}"

/-- Assert that rendered output does not contain forbidden substrings. -/
private def assertNotContains (label rendered : String) (needles : List String) : IO Unit := do
  for needle in needles do
    if contains rendered needle then
      throw (IO.userError s!"✗ {label}: unexpected '{needle}' in:\n{rendered}")
  IO.println s!"✓ {label}"

private def zeroSelectors (spec : ASTContractSpec) : List Nat :=
  List.replicate spec.functions.length 0

#eval! do
  match compileSpec ownedSpec (zeroSelectors ownedSpec) with
  | .error err =>
    throw (IO.userError s!"✗ owned constructor compile failed: {err}")
  | .ok ir =>
    let rendered := renderDeploy ir.deploy
    assertContains "Owned.deploy has constructor side effects" rendered ["sstore(0, initialOwner)"]
    assertNotContains "Owned.deploy strips constructor stop()" rendered ["stop()"]

#eval! do
  match compileSpec simpleTokenSpec (zeroSelectors simpleTokenSpec) with
  | .error err =>
    throw (IO.userError s!"✗ simpleToken constructor compile failed: {err}")
  | .ok ir =>
    let rendered := renderDeploy ir.deploy
    assertContains "SimpleToken.deploy has constructor side effects" rendered ["sstore(0", "sstore(2"]
    assertNotContains "SimpleToken.deploy strips constructor stop()" rendered ["stop()"]

private def badConstructorReturnSpec : ASTContractSpec := {
  name := "BadConstructorReturn"
  constructor := some {
    params := []
    body := Stmt.ret (Expr.lit 0)
  }
  functions := []
}

#eval! do
  match compileSpec badConstructorReturnSpec [] with
  | .error err =>
    if contains err "must not return runtime data directly" then
      IO.println "✓ Constructor return(...) rejected in deploy path"
    else
      throw (IO.userError s!"✗ unexpected constructor error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected constructor return(...) to be rejected")

end Compiler.ASTDriverTest
