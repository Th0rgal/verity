import Compiler.CompilationModel.Types

namespace Compiler.CompilationModel

-- Keep compiler literals aligned with Uint256 semantics (mod 2^256).
def uint256Modulus : Nat := 2 ^ 256

def packedMaskNat (packed : PackedBits) : Nat :=
  if packed.width >= 256 then
    uint256Modulus - 1
  else
    (2 ^ packed.width) - 1

def packedShiftedMaskNat (packed : PackedBits) : Nat :=
  packedMaskNat packed * (2 ^ packed.offset)

def packedBitsValid (packed : PackedBits) : Bool :=
  packed.width > 0 &&
  packed.width <= 256 &&
  packed.offset < 256 &&
  packed.offset + packed.width <= 256

def packedRangesOverlap (a b : PackedBits) : Bool :=
  let aStart := a.offset
  let aEnd := a.offset + a.width
  let bStart := b.offset
  let bEnd := b.offset + b.width
  aStart < bEnd && bStart < aEnd

def packedSlotsConflict (a b : Option PackedBits) : Bool :=
  match a, b with
  | none, _ => true
  | _, none => true
  | some pa, some pb => packedRangesOverlap pa pb

mutual
def collectExprNames : Expr → List String
  | Expr.literal _ => []
  | Expr.param name => [name]
  | Expr.constructorArg _ => []
  | Expr.storage field | Expr.storageAddr field => [field]
  | Expr.mapping field key => field :: collectExprNames key
  | Expr.mappingWord field key _ => field :: collectExprNames key
  | Expr.mappingPackedWord field key _ _ => field :: collectExprNames key
  | Expr.mapping2 field key1 key2 => field :: collectExprNames key1 ++ collectExprNames key2
  | Expr.mapping2Word field key1 key2 _ => field :: collectExprNames key1 ++ collectExprNames key2
  | Expr.mappingUint field key => field :: collectExprNames key
  | Expr.structMember field key _ => field :: collectExprNames key
  | Expr.structMember2 field key1 key2 _ => field :: collectExprNames key1 ++ collectExprNames key2
  | Expr.caller => []
  | Expr.contractAddress => []
  | Expr.chainid => []
  | Expr.extcodesize addr => collectExprNames addr
  | Expr.msgValue => []
  | Expr.blockTimestamp => []
  | Expr.mload offset => collectExprNames offset
  | Expr.keccak256 offset size => collectExprNames offset ++ collectExprNames size
  | Expr.call gas target value inOffset inSize outOffset outSize =>
      collectExprNames gas ++ collectExprNames target ++ collectExprNames value ++
      collectExprNames inOffset ++ collectExprNames inSize ++
      collectExprNames outOffset ++ collectExprNames outSize
  | Expr.staticcall gas target inOffset inSize outOffset outSize =>
      collectExprNames gas ++ collectExprNames target ++ collectExprNames inOffset ++
      collectExprNames inSize ++ collectExprNames outOffset ++ collectExprNames outSize
  | Expr.delegatecall gas target inOffset inSize outOffset outSize =>
      collectExprNames gas ++ collectExprNames target ++ collectExprNames inOffset ++
      collectExprNames inSize ++ collectExprNames outOffset ++ collectExprNames outSize
  | Expr.calldatasize => []
  | Expr.calldataload offset => collectExprNames offset
  | Expr.returndataSize => []
  | Expr.returndataOptionalBoolAt outOffset => collectExprNames outOffset
  | Expr.localVar name => [name]
  | Expr.externalCall name args => name :: collectExprListNames args
  | Expr.internalCall name args => name :: collectExprListNames args
  | Expr.arrayLength name => [name]
  | Expr.arrayElement name index => name :: collectExprNames index
  | Expr.add a b => collectExprNames a ++ collectExprNames b
  | Expr.sub a b => collectExprNames a ++ collectExprNames b
  | Expr.mul a b => collectExprNames a ++ collectExprNames b
  | Expr.div a b => collectExprNames a ++ collectExprNames b
  | Expr.mod a b => collectExprNames a ++ collectExprNames b
  | Expr.bitAnd a b => collectExprNames a ++ collectExprNames b
  | Expr.bitOr a b => collectExprNames a ++ collectExprNames b
  | Expr.bitXor a b => collectExprNames a ++ collectExprNames b
  | Expr.bitNot a => collectExprNames a
  | Expr.shl shift value => collectExprNames shift ++ collectExprNames value
  | Expr.shr shift value => collectExprNames shift ++ collectExprNames value
  | Expr.eq a b => collectExprNames a ++ collectExprNames b
  | Expr.ge a b => collectExprNames a ++ collectExprNames b
  | Expr.gt a b => collectExprNames a ++ collectExprNames b
  | Expr.lt a b => collectExprNames a ++ collectExprNames b
  | Expr.le a b => collectExprNames a ++ collectExprNames b
  | Expr.logicalAnd a b => collectExprNames a ++ collectExprNames b
  | Expr.logicalOr a b => collectExprNames a ++ collectExprNames b
  | Expr.logicalNot a => collectExprNames a
  | Expr.mulDivDown a b c => collectExprNames a ++ collectExprNames b ++ collectExprNames c
  | Expr.mulDivUp a b c => collectExprNames a ++ collectExprNames b ++ collectExprNames c
  | Expr.wMulDown a b => collectExprNames a ++ collectExprNames b
  | Expr.wDivUp a b => collectExprNames a ++ collectExprNames b
  | Expr.min a b => collectExprNames a ++ collectExprNames b
  | Expr.max a b => collectExprNames a ++ collectExprNames b
  | Expr.ite cond thenVal elseVal => collectExprNames cond ++ collectExprNames thenVal ++ collectExprNames elseVal
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals omega

def collectExprListNames : List Expr → List String
  | [] => []
  | expr :: rest => collectExprNames expr ++ collectExprListNames rest
termination_by exprs => sizeOf exprs
decreasing_by
  all_goals simp_wf
  all_goals omega
end

mutual
def collectStmtNames : Stmt → List String
  | Stmt.letVar name value => name :: collectExprNames value
  | Stmt.assignVar name value => name :: collectExprNames value
  | Stmt.setStorage field value | Stmt.setStorageAddr field value => field :: collectExprNames value
  | Stmt.setMapping field key value => field :: collectExprNames key ++ collectExprNames value
  | Stmt.setMappingWord field key _ value => field :: collectExprNames key ++ collectExprNames value
  | Stmt.setMappingPackedWord field key _ _ value => field :: collectExprNames key ++ collectExprNames value
  | Stmt.setMapping2 field key1 key2 value =>
    field :: collectExprNames key1 ++ collectExprNames key2 ++ collectExprNames value
  | Stmt.setMapping2Word field key1 key2 _ value =>
    field :: collectExprNames key1 ++ collectExprNames key2 ++ collectExprNames value
  | Stmt.setMappingUint field key value => field :: collectExprNames key ++ collectExprNames value
  | Stmt.setStructMember field key _ value => field :: collectExprNames key ++ collectExprNames value
  | Stmt.setStructMember2 field key1 key2 _ value =>
    field :: collectExprNames key1 ++ collectExprNames key2 ++ collectExprNames value
  | Stmt.require cond _ => collectExprNames cond
  | Stmt.requireError cond errorName args => errorName :: collectExprNames cond ++ collectExprListNames args
  | Stmt.revertError errorName args => errorName :: collectExprListNames args
  | Stmt.return value => collectExprNames value
  | Stmt.returnValues values => collectExprListNames values
  | Stmt.returnArray name => [name]
  | Stmt.returnBytes name => [name]
  | Stmt.returnStorageWords name => [name]
  | Stmt.mstore offset value => collectExprNames offset ++ collectExprNames value
  | Stmt.calldatacopy destOffset sourceOffset size =>
      collectExprNames destOffset ++ collectExprNames sourceOffset ++ collectExprNames size
  | Stmt.returndataCopy destOffset sourceOffset size =>
      collectExprNames destOffset ++ collectExprNames sourceOffset ++ collectExprNames size
  | Stmt.revertReturndata => []
  | Stmt.stop => []
  | Stmt.ite cond thenBranch elseBranch =>
      collectExprNames cond ++ collectStmtListNames thenBranch ++ collectStmtListNames elseBranch
  | Stmt.forEach varName count body =>
      varName :: collectExprNames count ++ collectStmtListNames body
  | Stmt.emit eventName args => eventName :: collectExprListNames args
  | Stmt.internalCall functionName args => functionName :: collectExprListNames args
  | Stmt.internalCallAssign names functionName args =>
      names ++ functionName :: collectExprListNames args
  | Stmt.rawLog topics dataOffset dataSize =>
      collectExprListNames topics ++ collectExprNames dataOffset ++ collectExprNames dataSize
  | Stmt.externalCallBind resultVars externalName args =>
      resultVars ++ externalName :: collectExprListNames args
  | Stmt.ecm mod args =>
      mod.resultVars ++ collectExprListNames args
termination_by stmt => sizeOf stmt
decreasing_by
  all_goals simp_wf
  all_goals omega

def collectStmtListNames : List Stmt → List String
  | [] => []
  | stmt :: rest => collectStmtNames stmt ++ collectStmtListNames rest
termination_by stmts => sizeOf stmts
decreasing_by
  all_goals simp_wf
  all_goals omega
end

end Compiler.CompilationModel
