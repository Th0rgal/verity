/-
  Compiler.ASTCompileTest: Smoke tests for the unified AST compiler

  Validates that `ASTCompile.compileStmt` produces the expected Yul
  for each contract function's AST definition. This serves as a
  regression test during the migration from ContractSpec to unified AST.
-/

import Compiler.ASTCompile
import Verity.AST.SimpleStorage
import Verity.AST.Counter
import Verity.AST.Owned
import Verity.AST.OwnedCounter
import Verity.AST.Ledger
import Verity.AST.SafeCounter
import Verity.AST.SimpleToken
import Compiler.Yul.PrettyPrint

namespace Compiler.ASTCompileTest

open Compiler.ASTCompile
open Verity.AST

/-- Render a list of Yul statements to a single string for comparison. -/
private def renderStmts (stmts : List Yul.YulStmt) : String :=
  String.intercalate "\n" (Yul.ppStmts 0 stmts)

/-- Check that a string contains a substring (simple implementation). -/
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
private def assertContains (label : String) (rendered : String) (needles : List String) : IO Unit := do
  for needle in needles do
    if !contains rendered needle then
      throw (IO.userError s!"✗ {label}: expected substring '{needle}' not found in:\n{rendered}")
  IO.println s!"✓ {label}"

/-!
## SimpleStorage
-/

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.SimpleStorage.storeAST)
  assertContains "SimpleStorage.store" rendered ["sstore(0, value)", "stop()"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.SimpleStorage.retrieveAST)
  assertContains "SimpleStorage.retrieve" rendered ["sload(0)", "return(0, 32)"]

/-!
## Counter
-/

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.Counter.incrementAST)
  assertContains "Counter.increment" rendered ["sload(0)", "add(current,", "sstore(0"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.Counter.decrementAST)
  assertContains "Counter.decrement" rendered ["sload(0)", "sub(current,", "sstore(0"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.Counter.getCountAST)
  assertContains "Counter.getCount" rendered ["sload(0)", "return(0, 32)"]

/-!
## Owned
-/

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.Owned.constructorAST)
  assertContains "Owned.constructor" rendered ["sstore(0, initialOwner)", "stop()"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.Owned.transferOwnershipAST)
  assertContains "Owned.transferOwnership" rendered ["caller()", "sload(0)", "sstore(0, newOwner)"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.Owned.getOwnerAST)
  assertContains "Owned.getOwner" rendered ["sload(0)", "return(0, 32)"]

/-!
## OwnedCounter
-/

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.OwnedCounter.incrementAST)
  assertContains "OwnedCounter.increment" rendered ["caller()", "sload(0)", "sstore(1"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.OwnedCounter.decrementAST)
  assertContains "OwnedCounter.decrement" rendered ["caller()", "sload(0)", "sstore(1"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.OwnedCounter.getCountAST)
  assertContains "OwnedCounter.getCount" rendered ["sload(1)", "return(0, 32)"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.OwnedCounter.getOwnerAST)
  assertContains "OwnedCounter.getOwner" rendered ["sload(0)", "return(0, 32)"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.OwnedCounter.transferOwnershipAST)
  assertContains "OwnedCounter.transferOwnership" rendered ["caller()", "sload(0)", "sstore(0, newOwner)"]

/-!
## Ledger
-/

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.Ledger.depositAST)
  assertContains "Ledger.deposit" rendered ["mappingSlot", "caller()", "sstore"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.Ledger.withdrawAST)
  -- "Insufficient balance" is ABI-encoded in revertWithMessage (hex), not plain text
  assertContains "Ledger.withdraw" rendered ["mappingSlot", "revert(0,"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.Ledger.getBalanceAST)
  assertContains "Ledger.getBalance" rendered ["mappingSlot", "return(0, 32)"]

/-!
## SafeCounter
-/

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.SafeCounter.incrementAST)
  -- "Overflow" is ABI-encoded in revertWithMessage (hex), not plain text
  assertContains "SafeCounter.increment" rendered ["sload(0)", "add(", "revert(0,"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.SafeCounter.decrementAST)
  -- "Underflow" is ABI-encoded in revertWithMessage (hex), not plain text
  assertContains "SafeCounter.decrement" rendered ["sload(0)", "sub(", "revert(0,"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.SafeCounter.getCountAST)
  assertContains "SafeCounter.getCount" rendered ["sload(0)", "return(0, 32)"]

/-!
## SimpleToken
-/

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.SimpleToken.constructorAST)
  assertContains "SimpleToken.constructor" rendered ["sstore(0,", "sstore(2,"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.SimpleToken.mintAST)
  -- "Not owner" is ABI-encoded in revertWithMessage (hex), not plain text
  assertContains "SimpleToken.mint" rendered ["caller()", "revert(0,", "mappingSlot", "sload(2)"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.SimpleToken.transferAST)
  -- "Insufficient balance" is ABI-encoded in revertWithMessage (hex), not plain text
  assertContains "SimpleToken.transfer" rendered ["mappingSlot", "revert(0,", "__ite_cond"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.SimpleToken.balanceOfAST)
  assertContains "SimpleToken.balanceOf" rendered ["mappingSlot", "return(0, 32)"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.SimpleToken.getTotalSupplyAST)
  assertContains "SimpleToken.getTotalSupply" rendered ["sload(2)", "return(0, 32)"]

#eval! do
  let rendered := renderStmts (compileStmt Verity.AST.SimpleToken.getOwnerAST)
  assertContains "SimpleToken.getOwner" rendered ["sload(0)", "return(0, 32)"]

end Compiler.ASTCompileTest
