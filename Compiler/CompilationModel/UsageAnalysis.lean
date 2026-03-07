import Compiler.CompilationModel.Types

namespace Compiler.CompilationModel

mutual
def collectStmtBindNames : Stmt → List String
  | Stmt.letVar name _ => [name]
  | Stmt.ite _ thenBranch elseBranch =>
      collectStmtListBindNames thenBranch ++ collectStmtListBindNames elseBranch
  | Stmt.forEach varName _ body =>
      varName :: collectStmtListBindNames body
  | Stmt.internalCallAssign names _ _ => names
  | Stmt.externalCallBind resultVars _ _ => resultVars
  | Stmt.ecm mod _ => mod.resultVars
  -- Statements that never bind new names.
  | Stmt.assignVar _ _ | Stmt.setStorage _ _ | Stmt.setStorageAddr _ _ | Stmt.return _
  | Stmt.setMapping _ _ _ | Stmt.setMappingWord _ _ _ _ | Stmt.setMappingPackedWord _ _ _ _ _ | Stmt.setMappingUint _ _ _
  | Stmt.setMapping2 _ _ _ _ | Stmt.setMapping2Word _ _ _ _ _
  | Stmt.setStructMember _ _ _ _ | Stmt.setStructMember2 _ _ _ _ _
  | Stmt.require _ _ | Stmt.requireError _ _ _ | Stmt.revertError _ _
  | Stmt.returnValues _ | Stmt.returnArray _ | Stmt.returnBytes _ | Stmt.returnStorageWords _
  | Stmt.mstore _ _ | Stmt.calldatacopy _ _ _ | Stmt.returndataCopy _ _ _ | Stmt.revertReturndata | Stmt.stop
  | Stmt.emit _ _ | Stmt.internalCall _ _ | Stmt.rawLog _ _ _ =>
      []
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def collectStmtListBindNames : List Stmt → List String
  | [] => []
  | stmt :: rest =>
      collectStmtBindNames stmt ++ collectStmtListBindNames rest
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
def exprUsesArrayElement : Expr → Bool
  | Expr.arrayElement _ _ => true
  | Expr.mapping _ key => exprUsesArrayElement key
  | Expr.mappingWord _ key _ => exprUsesArrayElement key
  | Expr.mappingPackedWord _ key _ _ => exprUsesArrayElement key
  | Expr.structMember _ key _ => exprUsesArrayElement key
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ => exprUsesArrayElement key1 || exprUsesArrayElement key2
  | Expr.mappingUint _ key => exprUsesArrayElement key
  | Expr.call gas target value inOffset inSize outOffset outSize =>
      exprUsesArrayElement gas || exprUsesArrayElement target || exprUsesArrayElement value ||
      exprUsesArrayElement inOffset || exprUsesArrayElement inSize ||
      exprUsesArrayElement outOffset || exprUsesArrayElement outSize
  | Expr.staticcall gas target inOffset inSize outOffset outSize =>
      exprUsesArrayElement gas || exprUsesArrayElement target ||
      exprUsesArrayElement inOffset || exprUsesArrayElement inSize ||
      exprUsesArrayElement outOffset || exprUsesArrayElement outSize
  | Expr.delegatecall gas target inOffset inSize outOffset outSize =>
      exprUsesArrayElement gas || exprUsesArrayElement target ||
      exprUsesArrayElement inOffset || exprUsesArrayElement inSize ||
      exprUsesArrayElement outOffset || exprUsesArrayElement outSize
  | Expr.extcodesize addr => exprUsesArrayElement addr
  | Expr.mload offset =>
      exprUsesArrayElement offset
  | Expr.calldataload offset =>
      exprUsesArrayElement offset
  | Expr.keccak256 offset size =>
      exprUsesArrayElement offset || exprUsesArrayElement size
  | Expr.returndataOptionalBoolAt outOffset => exprUsesArrayElement outOffset
  | Expr.externalCall _ args | Expr.internalCall _ args =>
      exprListUsesArrayElement args
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.mod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.lt a b | Expr.le a b |
    Expr.logicalAnd a b | Expr.logicalOr a b |
    Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b =>
      exprUsesArrayElement a || exprUsesArrayElement b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c =>
      exprUsesArrayElement a || exprUsesArrayElement b || exprUsesArrayElement c
  | Expr.bitNot a | Expr.logicalNot a =>
      exprUsesArrayElement a
  | Expr.ite cond thenVal elseVal =>
      exprUsesArrayElement cond || exprUsesArrayElement thenVal || exprUsesArrayElement elseVal
  -- Leaf expressions: no sub-expressions that could contain arrayElement.
  | Expr.literal _ | Expr.param _ | Expr.constructorArg _ | Expr.storage _ | Expr.storageAddr _
  | Expr.caller | Expr.contractAddress | Expr.chainid | Expr.msgValue | Expr.blockTimestamp
  | Expr.calldatasize | Expr.returndataSize | Expr.localVar _ | Expr.arrayLength _ =>
      false
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

def exprListUsesArrayElement : List Expr → Bool
  | [] => false
  | e :: es => exprUsesArrayElement e || exprListUsesArrayElement es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

def stmtUsesArrayElement : Stmt → Bool
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value | Stmt.setStorageAddr _ value |
    Stmt.return value | Stmt.require value _ =>
      exprUsesArrayElement value
  | Stmt.requireError cond _ args =>
      exprUsesArrayElement cond || exprListUsesArrayElement args
  | Stmt.revertError _ args | Stmt.emit _ args | Stmt.returnValues args =>
      exprListUsesArrayElement args
  | Stmt.mstore offset value =>
      exprUsesArrayElement offset || exprUsesArrayElement value
  | Stmt.calldatacopy destOffset sourceOffset size =>
      exprUsesArrayElement destOffset || exprUsesArrayElement sourceOffset || exprUsesArrayElement size
  | Stmt.returndataCopy destOffset sourceOffset size =>
      exprUsesArrayElement destOffset || exprUsesArrayElement sourceOffset || exprUsesArrayElement size
  | Stmt.setMapping _ key value | Stmt.setMappingWord _ key _ value | Stmt.setMappingPackedWord _ key _ _ value | Stmt.setMappingUint _ key value
  | Stmt.setStructMember _ key _ value =>
      exprUsesArrayElement key || exprUsesArrayElement value
  | Stmt.setMapping2 _ key1 key2 value | Stmt.setMapping2Word _ key1 key2 _ value
  | Stmt.setStructMember2 _ key1 key2 _ value =>
      exprUsesArrayElement key1 || exprUsesArrayElement key2 || exprUsesArrayElement value
  | Stmt.ite cond thenBranch elseBranch =>
      exprUsesArrayElement cond || stmtListUsesArrayElement thenBranch || stmtListUsesArrayElement elseBranch
  | Stmt.forEach _ count body =>
      exprUsesArrayElement count || stmtListUsesArrayElement body
  | Stmt.internalCall _ args | Stmt.internalCallAssign _ _ args =>
      exprListUsesArrayElement args
  | Stmt.rawLog topics dataOffset dataSize =>
      exprListUsesArrayElement topics || exprUsesArrayElement dataOffset || exprUsesArrayElement dataSize
  | Stmt.externalCallBind _ _ args =>
      exprListUsesArrayElement args
  | Stmt.ecm _ args =>
      exprListUsesArrayElement args
  -- Leaf statements: no sub-expressions that could contain arrayElement.
  | Stmt.returnArray _ | Stmt.returnBytes _ | Stmt.returnStorageWords _
  | Stmt.revertReturndata | Stmt.stop =>
      false
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def stmtListUsesArrayElement : List Stmt → Bool
  | [] => false
  | s :: ss => stmtUsesArrayElement s || stmtListUsesArrayElement ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

def functionUsesArrayElement (fn : FunctionSpec) : Bool :=
  fn.body.any stmtUsesArrayElement

def constructorUsesArrayElement : Option ConstructorSpec → Bool
  | none => false
  | some ctor => ctor.body.any stmtUsesArrayElement

def contractUsesArrayElement (spec : CompilationModel) : Bool :=
  constructorUsesArrayElement spec.constructor || spec.functions.any functionUsesArrayElement

end Compiler.CompilationModel
