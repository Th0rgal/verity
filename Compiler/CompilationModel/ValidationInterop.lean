/- 
  Compiler.CompilationModel.ValidationInterop: Interop profile validation
-/
import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.IssueRefs
import Compiler.CompilationModel.SelectorInteropHelpers

namespace Compiler.CompilationModel

def lowLevelCallUnsupportedError (context : String) (name : String) : Except String Unit :=
  throw s!"Compilation error: {context} uses unsupported low-level call '{name}' ({issue586Ref}). Use a verified linked external function wrapper instead of raw call/staticcall/delegatecall/callcode."

def interopBuiltinCallUnsupportedError (context : String) (name : String) : Except String Unit :=
  throw s!"Compilation error: {context} uses unsupported interop builtin call '{name}' ({issue586Ref}). Use a verified linked external wrapper or pass the required value through explicit function parameters."

def unsupportedInteropCallError (context : String) (name : String) : Except String Unit :=
  if isLowLevelCallName name then
    lowLevelCallUnsupportedError context name
  else
    interopBuiltinCallUnsupportedError context name

mutual
def validateInteropExpr (context : String) : Expr → Except String Unit
  | Expr.msgValue =>
      pure ()
  | Expr.call gas target value inOffset inSize outOffset outSize => do
      validateInteropExpr context gas
      validateInteropExpr context target
      validateInteropExpr context value
      validateInteropExpr context inOffset
      validateInteropExpr context inSize
      validateInteropExpr context outOffset
      validateInteropExpr context outSize
  | Expr.staticcall gas target inOffset inSize outOffset outSize => do
      validateInteropExpr context gas
      validateInteropExpr context target
      validateInteropExpr context inOffset
      validateInteropExpr context inSize
      validateInteropExpr context outOffset
      validateInteropExpr context outSize
  | Expr.delegatecall gas target inOffset inSize outOffset outSize => do
      validateInteropExpr context gas
      validateInteropExpr context target
      validateInteropExpr context inOffset
      validateInteropExpr context inSize
      validateInteropExpr context outOffset
      validateInteropExpr context outSize
  | Expr.contractAddress | Expr.chainid | Expr.blobbasefee =>
      pure ()
  | Expr.extcodesize addr =>
      validateInteropExpr context addr
  | Expr.calldatasize =>
      pure ()
  | Expr.calldataload offset =>
      validateInteropExpr context offset
  | Expr.mload offset =>
      validateInteropExpr context offset
  | Expr.tload offset =>
      validateInteropExpr context offset
  | Expr.keccak256 offset size => do
      validateInteropExpr context offset
      validateInteropExpr context size
  | Expr.returndataSize =>
      pure ()
  | Expr.returndataOptionalBoolAt outOffset =>
      validateInteropExpr context outOffset
  | Expr.externalCall name args => do
      if isInteropBuiltinCallName name then
        unsupportedInteropCallError context name
      validateInteropExprList context args
  | Expr.mapping _ key => validateInteropExpr context key
  | Expr.mappingWord _ key _ => validateInteropExpr context key
  | Expr.mappingPackedWord _ key _ _ => validateInteropExpr context key
  | Expr.structMember _ key _ => validateInteropExpr context key
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ => do
      validateInteropExpr context key1
      validateInteropExpr context key2
  | Expr.mappingUint _ key => validateInteropExpr context key
  | Expr.internalCall _ args =>
      validateInteropExprList context args
  | Expr.arrayElement _ index =>
      validateInteropExpr context index
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.sdiv a b | Expr.mod a b | Expr.smod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.sar a b | Expr.signextend a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.sgt a b | Expr.lt a b | Expr.slt a b | Expr.le a b |
    Expr.logicalAnd a b | Expr.logicalOr a b |
    Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b => do
      validateInteropExpr context a
      validateInteropExpr context b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c => do
      validateInteropExpr context a
      validateInteropExpr context b
      validateInteropExpr context c
  | Expr.bitNot a | Expr.logicalNot a =>
      validateInteropExpr context a
  | Expr.ite cond thenVal elseVal => do
      validateInteropExpr context cond
      validateInteropExpr context thenVal
      validateInteropExpr context elseVal
  | _ =>
      pure ()
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

def validateInteropExprList (context : String) : List Expr → Except String Unit
  | [] => pure ()
  | e :: es => do
      validateInteropExpr context e
      validateInteropExprList context es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

def validateInteropStmt (context : String) : Stmt → Except String Unit
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value | Stmt.setStorageAddr _ value |
    Stmt.return value | Stmt.require value _ =>
      validateInteropExpr context value
  | Stmt.requireError cond _ args => do
      validateInteropExpr context cond
      validateInteropExprList context args
  | Stmt.revertError _ args =>
      validateInteropExprList context args
  | Stmt.mstore offset value => do
      validateInteropExpr context offset
      validateInteropExpr context value
  | Stmt.tstore offset value => do
      validateInteropExpr context offset
      validateInteropExpr context value
  | Stmt.calldatacopy destOffset sourceOffset size => do
      validateInteropExpr context destOffset
      validateInteropExpr context sourceOffset
      validateInteropExpr context size
  | Stmt.returndataCopy destOffset sourceOffset size => do
      validateInteropExpr context destOffset
      validateInteropExpr context sourceOffset
      validateInteropExpr context size
  | Stmt.revertReturndata =>
      pure ()
  | Stmt.setMapping _ key value | Stmt.setMappingWord _ key _ value | Stmt.setMappingPackedWord _ key _ _ value | Stmt.setMappingUint _ key value
  | Stmt.setStructMember _ key _ value => do
      validateInteropExpr context key
      validateInteropExpr context value
  | Stmt.setMapping2 _ key1 key2 value | Stmt.setMapping2Word _ key1 key2 _ value
  | Stmt.setStructMember2 _ key1 key2 _ value => do
      validateInteropExpr context key1
      validateInteropExpr context key2
      validateInteropExpr context value
  | Stmt.ite cond thenBranch elseBranch => do
      validateInteropExpr context cond
      validateInteropStmtList context thenBranch
      validateInteropStmtList context elseBranch
  | Stmt.forEach _ count body => do
      validateInteropExpr context count
      validateInteropStmtList context body
  | Stmt.emit _ args =>
      validateInteropExprList context args
  | Stmt.internalCall _ args =>
      validateInteropExprList context args
  | Stmt.internalCallAssign _ _ args =>
      validateInteropExprList context args
  | Stmt.externalCallBind _ _ args =>
      validateInteropExprList context args
  | Stmt.returnValues values =>
      validateInteropExprList context values
  | Stmt.rawLog topics dataOffset dataSize => do
      validateInteropExprList context topics
      validateInteropExpr context dataOffset
      validateInteropExpr context dataSize
  | Stmt.ecm _ args =>
      validateInteropExprList context args
  | _ =>
      pure ()
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def validateInteropStmtList (context : String) : List Stmt → Except String Unit
  | [] => pure ()
  | s :: ss => do
      validateInteropStmt context s
      validateInteropStmtList context ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

def validateInteropFunctionSpec (spec : FunctionSpec) : Except String Unit := do
  spec.body.forM (validateInteropStmt s!"function '{spec.name}'")

def validateInteropExternalSpec (spec : ExternalFunction) : Except String Unit := do
  if isInteropBuiltinCallName spec.name then
    unsupportedInteropCallError s!"external declaration '{spec.name}'" spec.name

def validateInteropConstructorSpec (ctor : Option ConstructorSpec) : Except String Unit := do
  match ctor with
  | none => pure ()
  | some spec =>
      spec.body.forM (validateInteropStmt "constructor")

def validateSpecialEntrypointSpec (spec : FunctionSpec) : Except String Unit := do
  if !isInteropEntrypointName spec.name then
    pure ()
  else
    if spec.isInternal then
      throw s!"Compilation error: function '{spec.name}' cannot be marked internal ({issue586Ref})"
    if !spec.params.isEmpty then
      throw s!"Compilation error: function '{spec.name}' must not declare parameters ({issue586Ref})"
    let returns ← functionReturns spec
    if !returns.isEmpty then
      throw s!"Compilation error: function '{spec.name}' must not return values ({issue586Ref})"
    if spec.name == "receive" && !spec.isPayable then
      throw s!"Compilation error: function 'receive' must be payable ({issue586Ref})"
    if spec.isView || spec.isPure then
      throw s!"Compilation error: function '{spec.name}' cannot be marked view/pure ({issue586Ref})"

end Compiler.CompilationModel
