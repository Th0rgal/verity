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
contract-surface features such as `ite`, mapping access, or event emission. -/
inductive SupportedStmtLegacyTail (fields : List Field) : Type where
  | rawLogLiterals
      (topics : List Nat) (dataOffset dataSize : Nat)
      (htopics : topics.length ≤ 4)
  | iteEqSetStorageLiterals
      (fieldName : String) (slot : Nat)
      (n m thenVal elseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqSetStorageThenReturnLiteral
      (fieldName : String) (slot : Nat)
      (n m thenVal elseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqReturnThenSetStorageLiteral
      (fieldName : String) (slot : Nat)
      (n m thenVal elseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqReturnLiterals
      (n m thenVal elseVal : Nat)
  | iteEqThenIteEqReturnLiterals
      (n m p q thenVal elseVal outerElseVal : Nat)
  | iteEqThenIteEqSetStorageLiteralsThenReturnLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqThenIteEqReturnLiteralsThenSetStorageLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseWriteVal outerElseRetVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | returnMappingCaller
      (fieldName : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
  | letMappingParamReturnLocal
      (fieldName paramName tmp : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
  | letMapping2ParamsReturnLocal
      (fieldName p1 p2 tmp : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
      (hp : p1 ≠ p2)
  | letCallerSetMapping2Stop
      (fieldName senderVar p1 p2 : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
      (h1 : senderVar ≠ p2) (h2 : senderVar ≠ p1) (h3 : p2 ≠ p1)
      (h4 : p1 ≠ p2) (h5 : p1 ≠ senderVar) (h6 : p2 ≠ senderVar)
  | letMappingUintParamReturnLocal
      (fieldName paramName tmp : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
  | setMappingUintParamsStop
      (fieldName p1 p2 : String) (slot : Nat)
      (hSlot : findFieldSlot fields fieldName = some slot)
      (hp : p1 ≠ p2)
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
  | letCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop
      (ownerField mappingField senderVar ownerVar currentVar keyParam : String)
      (ownerSlot mappingSlot : Nat) (writeVal : Nat) (msg1 msg2 : String)
      (hOwner : findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
      (hMapping : findFieldSlot fields mappingField = some mappingSlot)
      (hne_sv_kp : senderVar ≠ keyParam)
      (hne_ov_kp : ownerVar ≠ keyParam)
      (hne_ov_sv : ownerVar ≠ senderVar)
      (hne_cv_kp : currentVar ≠ keyParam)
  | letCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop
      (ownerField mappingField senderVar ownerVar currentVar keyParam : String)
      (ownerSlot mappingSlot : Nat) (bound writeVal : Nat) (msg1 msg2 msg3 : String)
      (hOwner : findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot))
      (hMapping : findFieldSlot fields mappingField = some mappingSlot)
      (hne_sv_kp : senderVar ≠ keyParam)
      (hne_ov_kp : ownerVar ≠ keyParam)
      (hne_ov_sv : ownerVar ≠ senderVar)
      (hne_cv_kp : currentVar ≠ keyParam)
  | letCallerLetMapping2IteParamReqSetMapping2Stop
      (mappingField senderVar currentVar authParam boolParam msg1 msg2 : String) (mappingSlot : Nat)
      (hMapping : findFieldSlot fields mappingField = some mappingSlot)
      (hne_sv_bp : senderVar ≠ boolParam)
      (hne_sv_ap : senderVar ≠ authParam)
      (hne_cv_bp : currentVar ≠ boolParam)
      (hne_cv_ap : currentVar ≠ authParam)
      (hne_cv_sv : currentVar ≠ senderVar)
      (hne_bp_ap : boolParam ≠ authParam)

def SupportedStmtLegacyTail.toStmts
    {fields : List Field} (tail : SupportedStmtLegacyTail fields) : List Stmt :=
  match tail with
  | .rawLogLiterals topics dataOffset dataSize _ =>
      [Stmt.rawLog (topics.map Expr.literal) (Expr.literal dataOffset) (Expr.literal dataSize)]
  | .iteEqSetStorageLiterals fieldName _ n m thenVal elseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.setStorage fieldName (Expr.literal thenVal)]
          [Stmt.setStorage fieldName (Expr.literal elseVal)]]
  | .iteEqSetStorageThenReturnLiteral fieldName _ n m thenVal elseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.setStorage fieldName (Expr.literal thenVal)]
          [Stmt.return (Expr.literal elseVal)]]
  | .iteEqReturnThenSetStorageLiteral fieldName _ n m thenVal elseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.return (Expr.literal thenVal)]
          [Stmt.setStorage fieldName (Expr.literal elseVal)]]
  | .iteEqReturnLiterals n m thenVal elseVal =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.return (Expr.literal thenVal)]
          [Stmt.return (Expr.literal elseVal)]]
  | .iteEqThenIteEqReturnLiterals n m p q thenVal elseVal outerElseVal =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.return (Expr.literal thenVal)]
            [Stmt.return (Expr.literal elseVal)]]
          [Stmt.return (Expr.literal outerElseVal)]]
  | .iteEqThenIteEqSetStorageLiteralsThenReturnLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.setStorage fieldName (Expr.literal thenVal)]
            [Stmt.setStorage fieldName (Expr.literal elseVal)]]
          [Stmt.return (Expr.literal outerElseVal)]]
  | .iteEqThenIteEqReturnLiteralsThenSetStorageLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.return (Expr.literal thenVal)]
            [Stmt.return (Expr.literal elseVal)]]
          [Stmt.setStorage fieldName (Expr.literal outerElseVal)]]
  | .iteEqThenIteEqReturnLiteralsThenSetStorageLiteralThenReturnLiteral
      fieldName _ n m p q thenVal elseVal outerElseWriteVal outerElseRetVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.return (Expr.literal thenVal)]
            [Stmt.return (Expr.literal elseVal)]]
          [Stmt.setStorage fieldName (Expr.literal outerElseWriteVal),
           Stmt.return (Expr.literal outerElseRetVal)]]
  | .iteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.setStorage fieldName (Expr.literal thenVal)]
            [Stmt.setStorage fieldName (Expr.literal elseVal)]]
          [Stmt.setStorage fieldName (Expr.literal outerElseVal)]]
  | .iteEqThenIteEqSetStorageThenReturnLiteralThenReturnLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.setStorage fieldName (Expr.literal thenVal)]
            [Stmt.return (Expr.literal elseVal)]]
          [Stmt.return (Expr.literal outerElseVal)]]
  | .iteEqThenIteEqSetStorageThenReturnLiteralThenSetStorageLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.setStorage fieldName (Expr.literal thenVal)]
            [Stmt.return (Expr.literal elseVal)]]
          [Stmt.setStorage fieldName (Expr.literal outerElseVal)]]
  | .iteEqThenIteEqReturnThenSetStorageLiteralThenReturnLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.return (Expr.literal thenVal)]
            [Stmt.setStorage fieldName (Expr.literal elseVal)]]
          [Stmt.return (Expr.literal outerElseVal)]]
  | .iteEqThenIteEqReturnThenSetStorageLiteralThenSetStorageLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.return (Expr.literal thenVal)]
            [Stmt.setStorage fieldName (Expr.literal elseVal)]]
          [Stmt.setStorage fieldName (Expr.literal outerElseVal)]]
  | .returnMappingCaller fieldName _ _ =>
      [Stmt.return (Expr.mapping fieldName Expr.caller)]
  | .letMappingParamReturnLocal fieldName paramName tmp _ _ =>
      [ Stmt.letVar tmp (Expr.mapping fieldName (Expr.param paramName))
      , Stmt.return (Expr.localVar tmp)
      ]
  | .letMapping2ParamsReturnLocal fieldName p1 p2 tmp _ _ _ =>
      [ Stmt.letVar tmp (Expr.mapping2 fieldName (Expr.param p1) (Expr.param p2))
      , Stmt.return (Expr.localVar tmp)
      ]
  | .letCallerSetMapping2Stop fieldName senderVar p1 p2 _ _ _ _ _ _ _ _ =>
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.setMapping2 fieldName (Expr.localVar senderVar) (Expr.param p1) (Expr.param p2)
      , Stmt.stop
      ]
  | .letMappingUintParamReturnLocal fieldName paramName tmp _ _ =>
      [ Stmt.letVar tmp (Expr.mappingUint fieldName (Expr.param paramName))
      , Stmt.return (Expr.localVar tmp)
      ]
  | .setMappingUintParamsStop fieldName p1 p2 _ _ _ =>
      [ Stmt.setMappingUint fieldName (Expr.param p1) (Expr.param p2)
      , Stmt.stop
      ]
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
  | .letCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop
      ownerField mappingField senderVar ownerVar currentVar keyParam _ _ writeVal msg1 msg2
      _ _ _ _ _ _ =>
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar ownerVar (Expr.storage ownerField)
      , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
      , Stmt.letVar currentVar (Expr.mapping mappingField (Expr.param keyParam))
      , Stmt.require (Expr.eq (Expr.localVar currentVar) (Expr.literal 0)) msg2
      , Stmt.setMapping mappingField (Expr.param keyParam) (Expr.literal writeVal)
      , Stmt.stop
      ]
  | .letCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop
      ownerField mappingField senderVar ownerVar currentVar keyParam _ _ bound writeVal msg1 msg2 msg3
      _ _ _ _ _ _ =>
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar ownerVar (Expr.storage ownerField)
      , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
      , Stmt.letVar currentVar (Expr.mappingUint mappingField (Expr.param keyParam))
      , Stmt.require (Expr.eq (Expr.localVar currentVar) (Expr.literal 0)) msg2
      , Stmt.require (Expr.lt (Expr.param keyParam) (Expr.literal bound)) msg3
      , Stmt.setMappingUint mappingField (Expr.param keyParam) (Expr.literal writeVal)
      , Stmt.stop
      ]
  | .letCallerLetMapping2IteParamReqSetMapping2Stop
      mappingField senderVar currentVar authParam boolParam msg1 msg2 _ _ _ _ _ _ _ _ =>
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar currentVar (Expr.mapping2 mappingField (Expr.localVar senderVar) (Expr.param authParam))
      , Stmt.ite (Expr.param boolParam)
          [ Stmt.require (Expr.eq (Expr.localVar currentVar) (Expr.literal 0)) msg1
          , Stmt.setMapping2 mappingField (Expr.localVar senderVar) (Expr.param authParam) (Expr.literal 1) ]
          [ Stmt.require (Expr.logicalNot (Expr.eq (Expr.localVar currentVar) (Expr.literal 0))) msg2
          , Stmt.setMapping2 mappingField (Expr.localVar senderVar) (Expr.param authParam) (Expr.literal 0) ]
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
  | requireClause
      {scope : List String}
      (clause : RequireLiteralGuardFamilyClause)
      {rest : List Stmt} :
      SupportedStmtList fields scope rest →
      SupportedStmtList fields scope (clause.toStmt :: rest)
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
