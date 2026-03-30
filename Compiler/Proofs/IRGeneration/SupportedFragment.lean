import Compiler.TypedIRCompilerCorrectness
import Compiler.Proofs.IRGeneration.ExprCore

/-!
Scoped proof-layer support witness for statement lists.

`SupportedStmtList` is now a compositional public grammar: it can expose either
the existing generic compile-core / terminal-core statement grammars directly,
or admit the remaining non-generic singleton / structured statement shapes
through first-class constructors while the generic-core bridge continues to
grow.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Verity.Core.Free

/-- Scope seen by the tail after compiling a single statement. This matches the
statement-list compiler's `collectStmtNames` update. -/
def stmtNextScope (scope : List String) (stmt : Stmt) : List String :=
  collectStmtNames stmt ++ scope

/-- Proof-layer compositional witness for supported statement lists.

The witness is scoped because the generic compile-core grammars track local name
availability explicitly. The remaining non-generic storage / event shapes are
admitted directly as individual constructors so callers can still compose them
with `requireClause`, `ite`, and `append` under the same body interface. -/
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
  | setStorageAddrSingleSlot
      {scope : List String}
      {fieldName : String}
      {value : Expr}
      {slot : Nat} :
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.address }, slot) →
      SupportedStmtList fields scope [Stmt.setStorageAddr fieldName value]
  | mstoreSingle
      {scope : List String}
      {offset value : Expr} :
      FunctionBody.ExprCompileCore offset →
      FunctionBody.exprBoundNamesInScope offset scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      SupportedStmtList fields scope [Stmt.mstore offset value]
  | tstoreSingle
      {scope : List String}
      {offset value : Expr} :
      FunctionBody.ExprCompileCore offset →
      FunctionBody.exprBoundNamesInScope offset scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      SupportedStmtList fields scope [Stmt.tstore offset value]
  | letStorageField
      {scope : List String}
      {tmp : String}
      {fieldName : String}
      {slot : Nat} :
      findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot) →
      fieldName ∈ scope →
      SupportedStmtList fields scope [Stmt.letVar tmp (Expr.storage fieldName)]
  | letStorageAddrField
      {scope : List String}
      {tmp : String}
      {fieldName : String}
      {slot : Nat} :
      findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.address }, slot) →
      fieldName ∈ scope →
      SupportedStmtList fields scope [Stmt.letVar tmp (Expr.storageAddr fieldName)]
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
  | setMappingChainSingle
      {scope : List String}
      {fieldName : String}
      {keys : List Expr}
      {value : Expr}
      {slot : Nat} :
      (∀ key ∈ keys, FunctionBody.ExprCompileCore key) →
      (∀ key ∈ keys, FunctionBody.exprBoundNamesInScope key scope) →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope [Stmt.setMappingChain fieldName keys value]
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
  | setMappingWordSingle
      {scope : List String}
      {fieldName : String}
      {key value : Expr}
      {wordOffset slot : Nat} :
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope [Stmt.setMappingWord fieldName key wordOffset value]
  | setMappingPackedWordSingle
      {scope : List String}
      {fieldName : String}
      {key value : Expr}
      {wordOffset slot : Nat}
      {packed : PackedBits} :
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      "__compat_value" ∉ scope →
      "__compat_packed" ∉ scope →
      "__compat_slot_word" ∉ scope →
      "__compat_slot_cleared" ∉ scope →
      packedBitsValid packed = true →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope
        [Stmt.setMappingPackedWord fieldName key wordOffset packed value]
  | setStructMemberSingle
      {scope : List String}
      {fieldName memberName : String}
      {key value : Expr}
      {slot wordOffset : Nat}
      {members : List StructMember} :
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      findStructMembers fields fieldName = some members →
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none } →
      SupportedStmtList fields scope [Stmt.setStructMember fieldName key memberName value]
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
  | setMapping2WordSingle
      {scope : List String}
      {fieldName : String}
      {key1 key2 value : Expr}
      {wordOffset slot : Nat} :
      FunctionBody.ExprCompileCore key1 →
      FunctionBody.exprBoundNamesInScope key1 scope →
      FunctionBody.ExprCompileCore key2 →
      FunctionBody.exprBoundNamesInScope key2 scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope [Stmt.setMapping2Word fieldName key1 key2 wordOffset value]
  | setStructMember2Single
      {scope : List String}
      {fieldName memberName : String}
      {key1 key2 value : Expr}
      {slot wordOffset : Nat}
      {members : List StructMember} :
      FunctionBody.ExprCompileCore key1 →
      FunctionBody.exprBoundNamesInScope key1 scope →
      FunctionBody.ExprCompileCore key2 →
      FunctionBody.exprBoundNamesInScope key2 scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      findStructMembers fields fieldName = some members →
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none } →
      SupportedStmtList fields scope [Stmt.setStructMember2 fieldName key1 key2 memberName value]
  | rawLogLiterals
      {scope : List String}
      {topics : List Nat}
      {dataOffset dataSize : Nat} :
      topics.length ≤ 4 →
      SupportedStmtList fields scope
        [Stmt.rawLog (topics.map Expr.literal) (Expr.literal dataOffset) (Expr.literal dataSize)]
  | letCallerLetStorageReqEqReqNeqSetStorageParamStop
      {scope : List String}
      {ownerField senderVar ownerVar paramName msg1 msg2 : String}
      {ownerSlot : Nat} :
      findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot) →
      senderVar ≠ paramName →
      ownerVar ≠ paramName →
      ownerVar ≠ senderVar →
      SupportedStmtList fields scope
        [ Stmt.letVar senderVar Expr.caller
        , Stmt.letVar ownerVar (Expr.storage ownerField)
        , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
        , Stmt.require
            (Expr.logicalNot (Expr.eq (Expr.param paramName) (Expr.localVar ownerVar))) msg2
        , Stmt.setStorage ownerField (Expr.param paramName)
        , Stmt.stop
        ]
  | letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop
      {scope : List String}
      {ownerField targetField senderVar ownerVar targetVar paramName msg1 msg2 : String}
      {ownerSlot targetSlot : Nat} :
      findFieldWithResolvedSlot fields ownerField =
        some ({ name := ownerField, ty := FieldType.address }, ownerSlot) →
      findFieldWithResolvedSlot fields targetField =
        some ({ name := targetField, ty := FieldType.address }, targetSlot) →
      senderVar ≠ paramName →
      ownerVar ≠ paramName →
      ownerVar ≠ senderVar →
      targetVar ≠ paramName →
      targetVar ≠ senderVar →
      targetVar ≠ ownerVar →
      SupportedStmtList fields scope
        [ Stmt.letVar senderVar Expr.caller
        , Stmt.letVar ownerVar (Expr.storage ownerField)
        , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
        , Stmt.letVar targetVar (Expr.storage targetField)
        , Stmt.require
            (Expr.logicalNot (Expr.eq (Expr.param paramName) (Expr.localVar targetVar))) msg2
        , Stmt.setStorage targetField (Expr.param paramName)
        , Stmt.stop
        ]
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
      {pfx sfx : List Stmt} :
      SupportedStmtList fields scope pfx →
      SupportedStmtList fields (List.foldl stmtNextScope scope pfx) sfx →
      SupportedStmtList fields scope (pfx ++ sfx)

end Compiler.Proofs.IRGeneration
