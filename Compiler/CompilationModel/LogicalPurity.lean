import Compiler.CompilationModel.Types
import Compiler.CompilationModel.IssueRefs

namespace Compiler.CompilationModel

def exprContainsCallLike (expr : Expr) : Bool :=
  match expr with
  | Expr.call _ _ _ _ _ _ _ => true
  | Expr.staticcall _ _ _ _ _ _ => true
  | Expr.delegatecall _ _ _ _ _ _ => true
  | Expr.externalCall _ _ | Expr.internalCall _ _ => true
  | Expr.mapping _ key | Expr.mappingWord _ key _ | Expr.mappingPackedWord _ key _ _ | Expr.mappingUint _ key
  | Expr.structMember _ key _ =>
      exprContainsCallLike key
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ =>
      exprContainsCallLike key1 || exprContainsCallLike key2
  | Expr.arrayElement _ index =>
      exprContainsCallLike index
  | Expr.mload offset | Expr.calldataload offset | Expr.extcodesize offset |
    Expr.returndataOptionalBoolAt offset =>
      exprContainsCallLike offset
  | Expr.keccak256 offset size =>
      exprContainsCallLike offset || exprContainsCallLike size
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.mod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.lt a b | Expr.le a b |
    Expr.logicalAnd a b | Expr.logicalOr a b |
    Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b =>
      exprContainsCallLike a || exprContainsCallLike b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c =>
      exprContainsCallLike a || exprContainsCallLike b || exprContainsCallLike c
  | Expr.bitNot a | Expr.logicalNot a =>
      exprContainsCallLike a
  | Expr.ite cond thenVal elseVal =>
      exprContainsCallLike cond || exprContainsCallLike thenVal || exprContainsCallLike elseVal
  | Expr.literal _ | Expr.param _ | Expr.constructorArg _ | Expr.storage _ | Expr.storageAddr _
  | Expr.caller | Expr.contractAddress | Expr.chainid | Expr.msgValue | Expr.blockTimestamp
  | Expr.calldatasize | Expr.returndataSize | Expr.localVar _ | Expr.arrayLength _ =>
      false

def validateLogicalOperandPurity (context : String) (a b : Expr) : Except String Unit := do
  if exprContainsCallLike a || exprContainsCallLike b then
    throw s!"Compilation error: {context} uses Expr.logicalAnd/Expr.logicalOr with call-like operand(s), which are eagerly evaluated ({issue748Ref}). Move call-like expressions into Stmt.letVar/Stmt.ite before combining booleans."

def validateArithDuplicatedOperandPurity (context : String) (duplicated : List Expr) : Except String Unit := do
  if duplicated.any exprContainsCallLike then
    throw s!"Compilation error: {context} uses an arithmetic helper (mulDivUp/wDivUp/min/max) with call-like operand(s) that would be duplicated in Yul output ({issue748Ref}). Move call-like expressions into Stmt.letVar before using them in arithmetic helpers."

mutual
def exprContainsUnsafeLogicalCallLike (expr : Expr) : Bool :=
  match expr with
  | Expr.logicalAnd a b | Expr.logicalOr a b =>
      (exprContainsCallLike a || exprContainsCallLike b) ||
      exprContainsUnsafeLogicalCallLike a || exprContainsUnsafeLogicalCallLike b
  | Expr.mulDivUp a b c =>
      exprContainsCallLike c ||
      exprContainsUnsafeLogicalCallLike a || exprContainsUnsafeLogicalCallLike b || exprContainsUnsafeLogicalCallLike c
  | Expr.wDivUp a b =>
      exprContainsCallLike b ||
      exprContainsUnsafeLogicalCallLike a || exprContainsUnsafeLogicalCallLike b
  | Expr.min a b | Expr.max a b =>
      (exprContainsCallLike a || exprContainsCallLike b) ||
      exprContainsUnsafeLogicalCallLike a || exprContainsUnsafeLogicalCallLike b
  | Expr.call gas target value inOffset inSize outOffset outSize =>
      exprContainsUnsafeLogicalCallLike gas || exprContainsUnsafeLogicalCallLike target ||
      exprContainsUnsafeLogicalCallLike value || exprContainsUnsafeLogicalCallLike inOffset ||
      exprContainsUnsafeLogicalCallLike inSize || exprContainsUnsafeLogicalCallLike outOffset ||
      exprContainsUnsafeLogicalCallLike outSize
  | Expr.mload offset =>
      exprContainsUnsafeLogicalCallLike offset
  | Expr.calldataload offset =>
      exprContainsUnsafeLogicalCallLike offset
  | Expr.keccak256 offset size =>
      exprContainsUnsafeLogicalCallLike offset || exprContainsUnsafeLogicalCallLike size
  | Expr.staticcall gas target inOffset inSize outOffset outSize =>
      exprContainsUnsafeLogicalCallLike gas || exprContainsUnsafeLogicalCallLike target ||
      exprContainsUnsafeLogicalCallLike inOffset || exprContainsUnsafeLogicalCallLike inSize ||
      exprContainsUnsafeLogicalCallLike outOffset || exprContainsUnsafeLogicalCallLike outSize
  | Expr.delegatecall gas target inOffset inSize outOffset outSize =>
      exprContainsUnsafeLogicalCallLike gas || exprContainsUnsafeLogicalCallLike target ||
      exprContainsUnsafeLogicalCallLike inOffset || exprContainsUnsafeLogicalCallLike inSize ||
      exprContainsUnsafeLogicalCallLike outOffset || exprContainsUnsafeLogicalCallLike outSize
  | Expr.externalCall _ args | Expr.internalCall _ args =>
      exprListAnyUnsafeLogicalCallLike args
  | Expr.mapping _ key | Expr.mappingWord _ key _ | Expr.mappingPackedWord _ key _ _ | Expr.mappingUint _ key
  | Expr.structMember _ key _ =>
      exprContainsUnsafeLogicalCallLike key
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ =>
      exprContainsUnsafeLogicalCallLike key1 || exprContainsUnsafeLogicalCallLike key2
  | Expr.arrayElement _ index | Expr.returndataOptionalBoolAt index =>
      exprContainsUnsafeLogicalCallLike index
  | Expr.extcodesize addr =>
      exprContainsUnsafeLogicalCallLike addr
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.mod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.lt a b | Expr.le a b |
    Expr.wMulDown a b =>
      exprContainsUnsafeLogicalCallLike a || exprContainsUnsafeLogicalCallLike b
  | Expr.mulDivDown a b c =>
      exprContainsUnsafeLogicalCallLike a || exprContainsUnsafeLogicalCallLike b || exprContainsUnsafeLogicalCallLike c
  | Expr.bitNot a | Expr.logicalNot a =>
      exprContainsUnsafeLogicalCallLike a
  | Expr.ite cond thenVal elseVal =>
      (exprContainsCallLike cond || exprContainsCallLike thenVal || exprContainsCallLike elseVal) ||
      exprContainsUnsafeLogicalCallLike cond ||
      exprContainsUnsafeLogicalCallLike thenVal ||
      exprContainsUnsafeLogicalCallLike elseVal
  | Expr.literal _ | Expr.param _ | Expr.constructorArg _ | Expr.storage _ | Expr.storageAddr _
  | Expr.caller | Expr.contractAddress | Expr.chainid | Expr.msgValue | Expr.blockTimestamp
  | Expr.calldatasize | Expr.returndataSize | Expr.localVar _ | Expr.arrayLength _ =>
      false
termination_by sizeOf expr
decreasing_by all_goals simp_wf; all_goals omega

def exprListAnyUnsafeLogicalCallLike : List Expr → Bool
  | [] => false
  | e :: es => exprContainsUnsafeLogicalCallLike e || exprListAnyUnsafeLogicalCallLike es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

def stmtContainsUnsafeLogicalCallLike : Stmt → Bool
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value | Stmt.setStorageAddr _ value |
    Stmt.return value | Stmt.require value _ =>
      exprContainsUnsafeLogicalCallLike value
  | Stmt.requireError cond _ args =>
      exprContainsUnsafeLogicalCallLike cond || exprListAnyUnsafeLogicalCallLike args
  | Stmt.revertError _ args | Stmt.emit _ args | Stmt.returnValues args =>
      exprListAnyUnsafeLogicalCallLike args
  | Stmt.returnArray _ | Stmt.returnBytes _ | Stmt.returnStorageWords _ =>
      false
  | Stmt.mstore offset value =>
      exprContainsUnsafeLogicalCallLike offset || exprContainsUnsafeLogicalCallLike value
  | Stmt.calldatacopy destOffset sourceOffset size =>
      exprContainsUnsafeLogicalCallLike destOffset ||
      exprContainsUnsafeLogicalCallLike sourceOffset ||
      exprContainsUnsafeLogicalCallLike size
  | Stmt.returndataCopy destOffset sourceOffset size =>
      exprContainsUnsafeLogicalCallLike destOffset ||
      exprContainsUnsafeLogicalCallLike sourceOffset ||
      exprContainsUnsafeLogicalCallLike size
  | Stmt.revertReturndata | Stmt.stop =>
      false
  | Stmt.setMapping _ key value | Stmt.setMappingWord _ key _ value | Stmt.setMappingPackedWord _ key _ _ value | Stmt.setMappingUint _ key value
  | Stmt.setStructMember _ key _ value =>
      exprContainsUnsafeLogicalCallLike key || exprContainsUnsafeLogicalCallLike value
  | Stmt.setMapping2 _ key1 key2 value | Stmt.setMapping2Word _ key1 key2 _ value
  | Stmt.setStructMember2 _ key1 key2 _ value =>
      exprContainsUnsafeLogicalCallLike key1 ||
      exprContainsUnsafeLogicalCallLike key2 ||
      exprContainsUnsafeLogicalCallLike value
  | Stmt.ite cond thenBranch elseBranch =>
      exprContainsUnsafeLogicalCallLike cond ||
      stmtListAnyUnsafeLogicalCallLike thenBranch ||
      stmtListAnyUnsafeLogicalCallLike elseBranch
  | Stmt.forEach _ count body =>
      exprContainsUnsafeLogicalCallLike count || stmtListAnyUnsafeLogicalCallLike body
  | Stmt.internalCall _ args | Stmt.internalCallAssign _ _ args =>
      exprListAnyUnsafeLogicalCallLike args
  | Stmt.rawLog topics dataOffset dataSize =>
      exprListAnyUnsafeLogicalCallLike topics ||
      exprContainsUnsafeLogicalCallLike dataOffset ||
      exprContainsUnsafeLogicalCallLike dataSize
  | Stmt.externalCallBind _ _ args =>
      exprListAnyUnsafeLogicalCallLike args
  | Stmt.ecm _ args =>
      exprListAnyUnsafeLogicalCallLike args
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def stmtListAnyUnsafeLogicalCallLike : List Stmt → Bool
  | [] => false
  | s :: ss => stmtContainsUnsafeLogicalCallLike s || stmtListAnyUnsafeLogicalCallLike ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

end Compiler.CompilationModel
