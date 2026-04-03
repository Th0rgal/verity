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
  | letMappingField
      {scope : List String}
      {tmp : String}
      {fieldName : String}
      {key : Expr}
      {slot : Nat} :
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope [Stmt.letVar tmp (Expr.mapping fieldName key)]
  | letMappingWordField
      {scope : List String}
      {tmp : String}
      {fieldName : String}
      {key : Expr}
      {wordOffset : Nat}
      {slot : Nat} :
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope
        [Stmt.letVar tmp (Expr.mappingWord fieldName key wordOffset)]
  | letMappingUintField
      {scope : List String}
      {tmp : String}
      {fieldName : String}
      {key : Expr}
      {slot : Nat} :
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope [Stmt.letVar tmp (Expr.mappingUint fieldName key)]
  | letMappingPackedWordField
      {scope : List String}
      {tmp : String}
      {fieldName : String}
      {key : Expr}
      {wordOffset : Nat}
      {packed : PackedBits}
      {slot : Nat} :
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope
        [Stmt.letVar tmp (Expr.mappingPackedWord fieldName key wordOffset packed)]
  | letMapping2Field
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
      SupportedStmtList fields scope
        [Stmt.letVar tmp (Expr.mapping2 fieldName key1 key2)]
  | letMapping2WordField
      {scope : List String}
      {tmp : String}
      {fieldName : String}
      {key1 key2 : Expr}
      {wordOffset : Nat}
      {slot : Nat} :
      FunctionBody.ExprCompileCore key1 →
      FunctionBody.exprBoundNamesInScope key1 scope →
      FunctionBody.ExprCompileCore key2 →
      FunctionBody.exprBoundNamesInScope key2 scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope
        [Stmt.letVar tmp (Expr.mapping2Word fieldName key1 key2 wordOffset)]
  | letStructMemberField
      {scope : List String}
      {tmp : String}
      {fieldName : String}
      {key : Expr}
      {memberName : String}
      {slot : Nat} :
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope
        [Stmt.letVar tmp (Expr.structMember fieldName key memberName)]
  | letStructMember2Field
      {scope : List String}
      {tmp : String}
      {fieldName : String}
      {key1 key2 : Expr}
      {memberName : String}
      {slot : Nat} :
      FunctionBody.ExprCompileCore key1 →
      FunctionBody.exprBoundNamesInScope key1 scope →
      FunctionBody.ExprCompileCore key2 →
      FunctionBody.exprBoundNamesInScope key2 scope →
      findFieldSlot fields fieldName = some slot →
      SupportedStmtList fields scope
        [Stmt.letVar tmp (Expr.structMember2 fieldName key1 key2 memberName)]
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
  | requireClause
      {scope : List String}
      (clause : RequireLiteralGuardFamilyClause)
      {rest : List Stmt} :
      SupportedStmtList fields scope rest →
      SupportedStmtList fields scope (clause.toStmt :: rest)
  /-- If-then-else with terminal branches. The branches are required to
  satisfy `StmtListTerminalCore` (i.e. every execution path through each
  branch must end with `return` / `stop` / revert). The underlying
  `compiledStmtStep_ite` proof requires terminality to prevent execution
  from falling through the compiled Yul `if_` blocks. -/
  | iteTerminal
      {scope : List String}
      {cond : Expr}
      {thenBranch elseBranch : List Stmt} :
      FunctionBody.ExprCompileCore cond →
      FunctionBody.exprBoundNamesInScope cond scope →
      FunctionBody.StmtListTerminalCore scope thenBranch →
      FunctionBody.StmtListTerminalCore scope elseBranch →
      SupportedStmtList fields scope [Stmt.ite cond thenBranch elseBranch]
  | append
      {scope : List String}
      {pfx sfx : List Stmt} :
      SupportedStmtList fields scope pfx →
      SupportedStmtList fields (List.foldl stmtNextScope scope pfx) sfx →
      SupportedStmtList fields scope (pfx ++ sfx)

end Compiler.Proofs.IRGeneration
