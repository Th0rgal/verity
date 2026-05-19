import Compiler.Codegen
import Compiler.CompilationModel
import Lean
import Verity.Core.Uint256
import Verity.Macro.Translate

namespace Compiler.ByteOpcodeSupportTest

open Compiler
open Compiler.CompilationModel
open Lean
open Lean.Elab.Command
open Lean.Meta

def byteCoreExtractsMostSignificantByte : Bool :=
  ((Verity.Core.Uint256.byte
      (0 : Verity.Core.Uint256)
      (Verity.Core.Uint256.ofNat (0xab * 2 ^ 248)) : Nat) == 0xab)

example : byteCoreExtractsMostSignificantByte = true := by native_decide

def byteCoreExtractsLeastSignificantByte : Bool :=
  ((Verity.Core.Uint256.byte (31 : Verity.Core.Uint256) (0xff : Verity.Core.Uint256) : Nat) == 0xff)

example : byteCoreExtractsLeastSignificantByte = true := by native_decide

def byteCoreReturnsZeroPastWord : Bool :=
  ((Verity.Core.Uint256.byte (32 : Verity.Core.Uint256) (0xff : Verity.Core.Uint256) : Nat) == 0)

example : byteCoreReturnsZeroPastWord = true := by native_decide

def byteExpressionCompilesToYulByte : Bool :=
  match compileExpr [] .calldata (Expr.byte (Expr.param "index") (Expr.param "word")) with
  | .ok (Compiler.Yul.YulExpr.call "byte"
      [Compiler.Yul.YulExpr.ident "index", Compiler.Yul.YulExpr.ident "word"]) => true
  | _ => false

example : byteExpressionCompilesToYulByte = true := by native_decide

def byteExpressionIsPure : Bool :=
  let expr := Expr.byte (Expr.param "index") (Expr.param "word")
  !exprReadsStateOrEnv expr &&
    !exprWritesState expr &&
    !exprContainsCallLike expr &&
    !exprContainsExternalCall expr &&
    !exprMayContainExternalCall expr

example : byteExpressionIsPure = true := by native_decide

run_cmd do
  let indexIdent := mkIdent `index
  let wordIdent := mkIdent `word
  let actualStx ← Verity.Macro.translatePureExpr
    #[] #[] #[]
    #[{ ident := indexIdent, name := "index", ty := Verity.Macro.ValueType.uint256 },
      { ident := wordIdent, name := "word", ty := Verity.Macro.ValueType.uint256 }]
    #[]
    (← `(byte $indexIdent $wordIdent))
  liftTermElabM do
    let expectedStx ← `(
      Compiler.CompilationModel.Expr.byte
        (Compiler.CompilationModel.Expr.param "index")
        (Compiler.CompilationModel.Expr.param "word"))
    let actualExpr ← Lean.Elab.Term.elabTerm actualStx (some (mkConst ``Compiler.CompilationModel.Expr))
    let expectedExpr ← Lean.Elab.Term.elabTerm expectedStx (some (mkConst ``Compiler.CompilationModel.Expr))
    let actualExpr ← instantiateMVars actualExpr
    let expectedExpr ← instantiateMVars expectedExpr
    unless ← isDefEq actualExpr expectedExpr do
      throwError m!"expected byte builtin lowering, got {actualStx}"

end Compiler.ByteOpcodeSupportTest
