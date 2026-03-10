import Compiler.CompilationModel
import Contracts.Common

namespace Compiler.MacroCustomErrorFeatureTest

open Compiler.CompilationModel
open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

namespace MacroCustomErrorUsageSmoke

verity_contract MacroCustomErrorUsage where
  storage
    sentinel : Uint256 := slot 0

  errors
    error NonPositive(Uint256)
    error AmountTooLarge(Uint256, Uint256)

  function requirePositive (amount : Uint256) : Unit := do
    requireError (amount != 0) NonPositive(amount)

  function rejectLarge (amount : Uint256) : Unit := do
    if amount > 100 then
      revert AmountTooLarge(amount, 100)
    else
      pure ()

def requirePositiveModelUsesCustomErrorGuard : Bool :=
  match MacroCustomErrorUsage.requirePositive_modelBody with
  | [Stmt.requireError
        (Expr.logicalNot (Expr.eq (Expr.param "amount") (Expr.literal 0)))
        "NonPositive"
        [Expr.param "amount"],
      Stmt.stop] =>
      true
  | _ => false

example : requirePositiveModelUsesCustomErrorGuard = true := by native_decide

def rejectLargeModelUsesCustomErrorRevert : Bool :=
  match MacroCustomErrorUsage.rejectLarge_modelBody with
  | [Stmt.ite
        (Expr.gt (Expr.param "amount") (Expr.literal 100))
        [Stmt.revertError "AmountTooLarge" [Expr.param "amount", Expr.literal 100]]
        [],
      Stmt.stop] =>
      true
  | _ => false

example : rejectLargeModelUsesCustomErrorRevert = true := by native_decide

def requirePositiveExecutablePreservesSuccess : Bool :=
  match MacroCustomErrorUsage.requirePositive 7 Verity.defaultState with
  | .success () state => state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : requirePositiveExecutablePreservesSuccess = true := by native_decide

def rejectLargeExecutableUsesRuntimeFallback : Bool :=
  match MacroCustomErrorUsage.rejectLarge 101 Verity.defaultState with
  | .revert msg state =>
      msg == "AmountTooLarge(101, 100)" && state.sender == Verity.defaultState.sender
  | .success _ _ => false

example : rejectLargeExecutableUsesRuntimeFallback = true := by native_decide

end MacroCustomErrorUsageSmoke

end Compiler.MacroCustomErrorFeatureTest
