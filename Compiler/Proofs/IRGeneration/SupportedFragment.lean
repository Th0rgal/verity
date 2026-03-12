import Compiler.TypedIRCompilerCorrectness

/-!
Scoped proof-layer support witness for statement lists.

`SupportedStmtList` is now a compositional public grammar: it can expose either
the existing generic compile-core / terminal-core statement grammars directly,
or splice in one of the still-legacy residual tails while the remaining
unsupported control-flow / mapping-write shapes are being migrated off the
hardcoded inventory.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Verity.Core.Free

/-- Residual exact-source tails not yet absorbed by the compositional
`SupportedStmtList` grammar. Everything left here still depends on unsupported
contract-surface features such as mapping access or event emission. -/
inductive SupportedStmtLegacyTail (fields : List Field) : Type where
  | rawLogLiterals
      (topics : List Nat) (dataOffset dataSize : Nat)
      (htopics : topics.length ≤ 4)
  | letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop
      (ownerField senderVar ownerVar paramName msg1 msg2 : String) (ownerSlot : Nat)
      (hOwner : findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
      (hne_sv_p : senderVar ≠ paramName)
      (hne_ov_p : ownerVar ≠ paramName)
      (hne_ov_sv : ownerVar ≠ senderVar)
  | letCallerLetStorageAddrReqEqLetStorageAddrReqNeqSetStorageAddrParamStop
      (ownerField targetField senderVar ownerVar targetVar paramName msg1 msg2 : String)
      (ownerSlot targetSlot : Nat)
      (hOwner : findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
      (hTarget : findFieldWithResolvedSlot fields targetField =
        some ({ name := targetField, ty := FieldType.address }, targetSlot))
      (hne_sv_p : senderVar ≠ paramName)
      (hne_ov_p : ownerVar ≠ paramName)
      (hne_ov_sv : ownerVar ≠ senderVar)
      (hne_tv_p : targetVar ≠ paramName)
      (hne_tv_sv : targetVar ≠ senderVar)
      (hne_tv_ov : targetVar ≠ ownerVar)

def SupportedStmtLegacyTail.toStmts
    {fields : List Field} (tail : SupportedStmtLegacyTail fields) : List Stmt :=
  match tail with
  | .rawLogLiterals topics dataOffset dataSize _ =>
      [Stmt.rawLog (topics.map Expr.literal) (Expr.literal dataOffset) (Expr.literal dataSize)]
  | .letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop
      ownerField senderVar ownerVar paramName msg1 msg2 _ _ _ _ _ =>
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar ownerVar (Expr.storage ownerField)
      , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
      , Stmt.require (Expr.logicalNot (Expr.eq (Expr.param paramName) (Expr.localVar ownerVar))) msg2
      , Stmt.setStorage ownerField (Expr.param paramName)
      , Stmt.stop
      ]
  | .letCallerLetStorageAddrReqEqLetStorageAddrReqNeqSetStorageAddrParamStop
      ownerField targetField senderVar ownerVar targetVar paramName msg1 msg2 _ _ _ _ _ _ _ _ _ _ =>
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar ownerVar (Expr.storage ownerField)
      , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
      , Stmt.letVar targetVar (Expr.storage targetField)
      , Stmt.require (Expr.logicalNot (Expr.eq (Expr.param paramName) (Expr.localVar targetVar))) msg2
      , Stmt.setStorage targetField (Expr.param paramName)
      , Stmt.stop
      ]

/-- Proof-layer compositional witness for supported statement lists.

The witness is scoped because the generic compile-core grammars track local name
availability explicitly. Legacy tail-program leaves remain available as a
transitional constructor so existing non-core storage/write shapes continue to
fit under the same body interface while the old fragment inventory is
dismantled. -/
inductive SupportedStmtList (fields : List Field) : List String → List Stmt → Prop where
  | compileCore
      {scope : List String}
      {stmts : List Stmt} :
      FunctionBody.StmtListCompileCore scope stmts →
      SupportedStmtList fields scope stmts
  | terminalCore
      {scope : List String}
      {stmts : List Stmt} :
      FunctionBody.StmtListTerminalCore scope stmts →
      SupportedStmtList fields scope stmts
  | setStorageSingleSlot
      {scope : List String}
      {fieldName : String}
      {value : Expr}
      {slot : Nat} :
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot) →
      SupportedStmtList fields scope [Stmt.setStorage fieldName value]
  | letStorageField
      {scope : List String}
      {tmp : String}
      {fieldName : String}
      {field : Field}
      {slot : Nat} :
      findFieldWithResolvedSlot fields fieldName = some (field, slot) →
      SupportedStmtList fields scope [Stmt.letVar tmp (Expr.storage fieldName)]
  | returnMapping
      {scope : List String}
      {fieldName : String}
      {key : Expr}
      {slot : Nat} :
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope [Stmt.return (Expr.mapping fieldName key)]
  | letMapping
      {scope : List String}
      {tmp : String}
      {fieldName : String}
      {key : Expr}
      {slot : Nat} :
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope [Stmt.letVar tmp (Expr.mapping fieldName key)]
  | letMapping2
      {scope : List String}
      {tmp : String}
      {fieldName : String}
      {key1 key2 : Expr}
      {slot : Nat} :
      FunctionBody.ExprCompileCore key1 →
      FunctionBody.exprBoundNamesInScope key1 scope →
      FunctionBody.ExprCompileCore key2 →
      FunctionBody.exprBoundNamesInScope key2 scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope [Stmt.letVar tmp (Expr.mapping2 fieldName key1 key2)]
  | letMappingUint
      {scope : List String}
      {tmp : String}
      {fieldName : String}
      {key : Expr}
      {slot : Nat} :
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope [Stmt.letVar tmp (Expr.mappingUint fieldName key)]
  | setMappingUintSingle
      {scope : List String}
      {fieldName : String}
      {key value : Expr}
      {slot : Nat} :
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope [Stmt.setMappingUint fieldName key value]
  | setMappingSingle
      {scope : List String}
      {fieldName : String}
      {key value : Expr}
      {slot : Nat} :
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope [Stmt.setMapping fieldName key value]
  | setMapping2Single
      {scope : List String}
      {fieldName : String}
      {key1 key2 value : Expr}
      {slot : Nat} :
      FunctionBody.ExprCompileCore key1 →
      FunctionBody.exprBoundNamesInScope key1 scope →
      FunctionBody.ExprCompileCore key2 →
      FunctionBody.exprBoundNamesInScope key2 scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope [Stmt.setMapping2 fieldName key1 key2 value]
  | requireClause
      {scope : List String}
      (clause : RequireLiteralGuardFamilyClause)
      {rest : List Stmt} :
      SupportedStmtList fields scope rest →
      SupportedStmtList fields scope (clause.toStmt :: rest)
  | ite
      {scope : List String}
      {cond : Expr}
      {thenBranch elseBranch : List Stmt} :
      FunctionBody.ExprCompileCore cond →
      FunctionBody.exprBoundNamesInScope cond scope →
      SupportedStmtList fields scope thenBranch →
      SupportedStmtList fields scope elseBranch →
      SupportedStmtList fields scope [Stmt.ite cond thenBranch elseBranch]
  | append
      {scope : List String}
      {prefix suffix : List Stmt} :
      SupportedStmtList fields scope prefix →
      SupportedStmtList fields (List.foldl stmtNextScope scope prefix) suffix →
      SupportedStmtList fields scope (prefix ++ suffix)
  | legacyTail
      {scope : List String}
      (tail : SupportedStmtLegacyTail fields)
      {rest : List Stmt} :
      SupportedStmtList fields (List.foldl stmtNextScope scope tail.toStmts) rest →
      SupportedStmtList fields scope (tail.toStmts ++ rest)

end Compiler.Proofs.IRGeneration
