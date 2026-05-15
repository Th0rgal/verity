import Compiler.CompilationModel.Types

namespace Compiler.CompilationModel

mutual
def collectStmtBindNames : Stmt → List String
  | Stmt.letVar name _ => [name]
  | Stmt.ite _ thenBranch elseBranch =>
      collectStmtListBindNames thenBranch ++ collectStmtListBindNames elseBranch
  | Stmt.forEach varName _ body =>
      varName :: collectStmtListBindNames body
  | Stmt.unsafeBlock _ body =>
      collectStmtListBindNames body
  | Stmt.matchAdt _ _ branches =>
      collectMatchBranchBindNames branches
  | Stmt.internalCallAssign names _ _ => names
  | Stmt.externalCallBind resultVars _ _ => resultVars
  | Stmt.tryExternalCallBind successVar resultVars _ _ => successVar :: resultVars
  | Stmt.ecm mod _ => mod.resultVars
  -- Statements that never bind new names.
  | Stmt.assignVar _ _ | Stmt.setStorage _ _ | Stmt.setStorageAddr _ _ | Stmt.setStorageWord _ _ _
  | Stmt.storageArrayPush _ _ | Stmt.storageArrayPop _ | Stmt.setStorageArrayElement _ _ _
  | Stmt.return _
  | Stmt.setMapping _ _ _ | Stmt.setMappingWord _ _ _ _ | Stmt.setMappingPackedWord _ _ _ _ _ | Stmt.setMappingUint _ _ _
  | Stmt.setMappingChain _ _ _
  | Stmt.setMapping2 _ _ _ _ | Stmt.setMapping2Word _ _ _ _ _
  | Stmt.setStructMember _ _ _ _ | Stmt.setStructMember2 _ _ _ _ _
  | Stmt.require _ _ | Stmt.requireError _ _ _ | Stmt.revertError _ _
  | Stmt.returnValues _ | Stmt.returnArray _ | Stmt.returnBytes _ | Stmt.returnStorageWords _
  | Stmt.mstore _ _ | Stmt.tstore _ _ | Stmt.calldatacopy _ _ _ | Stmt.returndataCopy _ _ _ | Stmt.revertReturndata | Stmt.stop
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

def collectMatchBranchBindNames : List (String × List String × List Stmt) → List String
  | [] => []
  | (_, varNames, body) :: rest =>
      varNames ++ collectStmtListBindNames body ++ collectMatchBranchBindNames rest
termination_by bs => sizeOf bs
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
def collectStmtAssignedNames : Stmt → List String
  | Stmt.assignVar name _ => [name]
  | Stmt.ite _ thenBranch elseBranch =>
      collectStmtListAssignedNames thenBranch ++ collectStmtListAssignedNames elseBranch
  | Stmt.forEach _ _ body =>
      collectStmtListAssignedNames body
  | Stmt.unsafeBlock _ body =>
      collectStmtListAssignedNames body
  | Stmt.matchAdt _ _ branches =>
      collectMatchBranchAssignedNames branches
  | Stmt.letVar _ _ | Stmt.setStorage _ _ | Stmt.setStorageAddr _ _ | Stmt.setStorageWord _ _ _
  | Stmt.storageArrayPush _ _ | Stmt.storageArrayPop _ | Stmt.setStorageArrayElement _ _ _
  | Stmt.return _
  | Stmt.setMapping _ _ _ | Stmt.setMappingWord _ _ _ _ | Stmt.setMappingPackedWord _ _ _ _ _ | Stmt.setMappingUint _ _ _
  | Stmt.setMappingChain _ _ _
  | Stmt.setMapping2 _ _ _ _ | Stmt.setMapping2Word _ _ _ _ _
  | Stmt.setStructMember _ _ _ _ | Stmt.setStructMember2 _ _ _ _ _
  | Stmt.require _ _ | Stmt.requireError _ _ _ | Stmt.revertError _ _
  | Stmt.returnValues _ | Stmt.returnArray _ | Stmt.returnBytes _ | Stmt.returnStorageWords _
  | Stmt.mstore _ _ | Stmt.tstore _ _ | Stmt.calldatacopy _ _ _ | Stmt.returndataCopy _ _ _ | Stmt.revertReturndata | Stmt.stop
  | Stmt.emit _ _ | Stmt.internalCall _ _ | Stmt.internalCallAssign _ _ _
  | Stmt.rawLog _ _ _ | Stmt.externalCallBind _ _ _ | Stmt.tryExternalCallBind _ _ _ _ | Stmt.ecm _ _ =>
      []
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def collectStmtListAssignedNames : List Stmt → List String
  | [] => []
  | stmt :: rest =>
      collectStmtAssignedNames stmt ++ collectStmtListAssignedNames rest
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega

def collectMatchBranchAssignedNames : List (String × List String × List Stmt) → List String
  | [] => []
  | (_, _, body) :: rest =>
      collectStmtListAssignedNames body ++ collectMatchBranchAssignedNames rest
termination_by bs => sizeOf bs
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
def exprUsesArrayElementKind (includePlain includeWord : Bool) : Expr → Bool
  | Expr.arrayElement _ index | Expr.memoryArrayElement _ index =>
      let nested := exprUsesArrayElementKind includePlain includeWord index
      if nested then true else includePlain
  | Expr.arrayElementWord _ index _ _ =>
      let nested := exprUsesArrayElementKind includePlain includeWord index
      if nested then true else includeWord
  | Expr.arrayElementDynamicWord _ index _ =>
      let nested := exprUsesArrayElementKind includePlain includeWord index
      if nested then true else includeWord
  | Expr.arrayElementDynamicDataOffset _ index =>
      let nested := exprUsesArrayElementKind includePlain includeWord index
      if nested then true else includeWord
  | Expr.arrayElementDynamicMemberDataOffset _ index _ =>
      let nested := exprUsesArrayElementKind includePlain includeWord index
      if nested then true else includeWord
  | Expr.arrayElementDynamicMemberLength _ index _ =>
      let nested := exprUsesArrayElementKind includePlain includeWord index
      if nested then true else includeWord
  | Expr.arrayElementDynamicMemberElement _ index _ innerIndex =>
      let nestedIndex := exprUsesArrayElementKind includePlain includeWord index
      let nestedInner := exprUsesArrayElementKind includePlain includeWord innerIndex
      if nestedIndex || nestedInner then true else includeWord
  | Expr.mapping _ key => exprUsesArrayElementKind includePlain includeWord key
  | Expr.mappingWord _ key _ => exprUsesArrayElementKind includePlain includeWord key
  | Expr.mappingPackedWord _ key _ _ => exprUsesArrayElementKind includePlain includeWord key
  | Expr.mappingChain _ keys => exprListUsesArrayElementKind includePlain includeWord keys
  | Expr.structMember _ key _ => exprUsesArrayElementKind includePlain includeWord key
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ =>
      exprUsesArrayElementKind includePlain includeWord key1 ||
        exprUsesArrayElementKind includePlain includeWord key2
  | Expr.mappingUint _ key => exprUsesArrayElementKind includePlain includeWord key
  | Expr.call gas target value inOffset inSize outOffset outSize =>
      exprUsesArrayElementKind includePlain includeWord gas ||
      exprUsesArrayElementKind includePlain includeWord target ||
      exprUsesArrayElementKind includePlain includeWord value ||
      exprUsesArrayElementKind includePlain includeWord inOffset ||
      exprUsesArrayElementKind includePlain includeWord inSize ||
      exprUsesArrayElementKind includePlain includeWord outOffset ||
      exprUsesArrayElementKind includePlain includeWord outSize
  | Expr.staticcall gas target inOffset inSize outOffset outSize =>
      exprUsesArrayElementKind includePlain includeWord gas ||
      exprUsesArrayElementKind includePlain includeWord target ||
      exprUsesArrayElementKind includePlain includeWord inOffset ||
      exprUsesArrayElementKind includePlain includeWord inSize ||
      exprUsesArrayElementKind includePlain includeWord outOffset ||
      exprUsesArrayElementKind includePlain includeWord outSize
  | Expr.delegatecall gas target inOffset inSize outOffset outSize =>
      exprUsesArrayElementKind includePlain includeWord gas ||
      exprUsesArrayElementKind includePlain includeWord target ||
      exprUsesArrayElementKind includePlain includeWord inOffset ||
      exprUsesArrayElementKind includePlain includeWord inSize ||
      exprUsesArrayElementKind includePlain includeWord outOffset ||
      exprUsesArrayElementKind includePlain includeWord outSize
  | Expr.extcodesize addr => exprUsesArrayElementKind includePlain includeWord addr
  | Expr.mload offset => exprUsesArrayElementKind includePlain includeWord offset
  | Expr.tload offset => exprUsesArrayElementKind includePlain includeWord offset
  | Expr.calldataload offset => exprUsesArrayElementKind includePlain includeWord offset
  | Expr.keccak256 offset size =>
      exprUsesArrayElementKind includePlain includeWord offset ||
        exprUsesArrayElementKind includePlain includeWord size
  | Expr.returndataOptionalBoolAt outOffset =>
      exprUsesArrayElementKind includePlain includeWord outOffset
  | Expr.externalCall _ args | Expr.internalCall _ args =>
      exprListUsesArrayElementKind includePlain includeWord args
  | Expr.storageArrayElement _ index =>
      exprUsesArrayElementKind includePlain includeWord index
  | Expr.dynamicBytesEq _ _ =>
      false
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.sdiv a b
  | Expr.mod a b | Expr.smod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b
  | Expr.sar a b | Expr.signextend a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.sgt a b | Expr.lt a b | Expr.slt a b | Expr.le a b |
    Expr.logicalAnd a b | Expr.logicalOr a b |
    Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b |
    Expr.ceilDiv a b =>
      exprUsesArrayElementKind includePlain includeWord a ||
        exprUsesArrayElementKind includePlain includeWord b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c | Expr.mulDiv512Down a b c | Expr.mulDiv512Up a b c =>
      exprUsesArrayElementKind includePlain includeWord a ||
        exprUsesArrayElementKind includePlain includeWord b ||
        exprUsesArrayElementKind includePlain includeWord c
  | Expr.bitNot a | Expr.logicalNot a =>
      exprUsesArrayElementKind includePlain includeWord a
  | Expr.ite cond thenVal elseVal =>
      exprUsesArrayElementKind includePlain includeWord cond ||
        exprUsesArrayElementKind includePlain includeWord thenVal ||
        exprUsesArrayElementKind includePlain includeWord elseVal
  | Expr.adtConstruct _ _ args => exprListUsesArrayElementKind includePlain includeWord args
  | Expr.adtField _ _ _ _ _ => false
  | Expr.literal _ | Expr.param _ | Expr.constructorArg _ | Expr.storage _ | Expr.storageAddr _
  | Expr.caller | Expr.contractAddress | Expr.chainid | Expr.msgValue | Expr.selfBalance | Expr.blockTimestamp
  | Expr.blockNumber | Expr.blobbasefee
  | Expr.calldatasize | Expr.returndataSize | Expr.localVar _ | Expr.arrayLength _
  | Expr.memoryArrayLength _
  | Expr.storageArrayLength _
  | Expr.paramDynamicHeadWord _ _
  | Expr.paramDynamicStaticComposite _ _
  | Expr.paramDynamicMemberLength _ _
  | Expr.paramDynamicMemberDataOffset _ _
  | Expr.adtTag _ _ =>
      false
  | Expr.paramDynamicMemberElement _ _ innerIndex =>
      exprUsesArrayElementKind includePlain includeWord innerIndex
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

def exprListUsesArrayElementKind (includePlain includeWord : Bool) : List Expr → Bool
  | [] => false
  | e :: es =>
      exprUsesArrayElementKind includePlain includeWord e ||
        exprListUsesArrayElementKind includePlain includeWord es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

def stmtUsesArrayElementKind (includePlain includeWord : Bool) : Stmt → Bool
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value | Stmt.setStorageAddr _ value
  | Stmt.setStorageWord _ _ value |
    Stmt.storageArrayPush _ value |
    Stmt.return value | Stmt.require value _ =>
      exprUsesArrayElementKind includePlain includeWord value
  | Stmt.setStorageArrayElement _ index value =>
      exprUsesArrayElementKind includePlain includeWord index ||
        exprUsesArrayElementKind includePlain includeWord value
  | Stmt.storageArrayPop _ =>
      false
  | Stmt.requireError cond _ args =>
      exprUsesArrayElementKind includePlain includeWord cond ||
        exprListUsesArrayElementKind includePlain includeWord args
  | Stmt.revertError _ args | Stmt.emit _ args | Stmt.returnValues args =>
      exprListUsesArrayElementKind includePlain includeWord args
  | Stmt.mstore offset value =>
      exprUsesArrayElementKind includePlain includeWord offset ||
        exprUsesArrayElementKind includePlain includeWord value
  | Stmt.tstore offset value =>
      exprUsesArrayElementKind includePlain includeWord offset ||
        exprUsesArrayElementKind includePlain includeWord value
  | Stmt.calldatacopy destOffset sourceOffset size =>
      exprUsesArrayElementKind includePlain includeWord destOffset ||
        exprUsesArrayElementKind includePlain includeWord sourceOffset ||
        exprUsesArrayElementKind includePlain includeWord size
  | Stmt.returndataCopy destOffset sourceOffset size =>
      exprUsesArrayElementKind includePlain includeWord destOffset ||
        exprUsesArrayElementKind includePlain includeWord sourceOffset ||
        exprUsesArrayElementKind includePlain includeWord size
  | Stmt.setMapping _ key value | Stmt.setMappingWord _ key _ value | Stmt.setMappingPackedWord _ key _ _ value | Stmt.setMappingUint _ key value
  | Stmt.setStructMember _ key _ value =>
      exprUsesArrayElementKind includePlain includeWord key ||
        exprUsesArrayElementKind includePlain includeWord value
  | Stmt.setMappingChain _ keys value =>
      exprListUsesArrayElementKind includePlain includeWord keys ||
        exprUsesArrayElementKind includePlain includeWord value
  | Stmt.setMapping2 _ key1 key2 value | Stmt.setMapping2Word _ key1 key2 _ value
  | Stmt.setStructMember2 _ key1 key2 _ value =>
      exprUsesArrayElementKind includePlain includeWord key1 ||
        exprUsesArrayElementKind includePlain includeWord key2 ||
        exprUsesArrayElementKind includePlain includeWord value
  | Stmt.ite cond thenBranch elseBranch =>
      exprUsesArrayElementKind includePlain includeWord cond ||
        stmtListUsesArrayElementKind includePlain includeWord thenBranch ||
        stmtListUsesArrayElementKind includePlain includeWord elseBranch
  | Stmt.forEach _ count body =>
      exprUsesArrayElementKind includePlain includeWord count ||
        stmtListUsesArrayElementKind includePlain includeWord body
  | Stmt.unsafeBlock _ body =>
      stmtListUsesArrayElementKind includePlain includeWord body
  | Stmt.matchAdt _ scrutinee branches =>
      exprUsesArrayElementKind includePlain includeWord scrutinee ||
        matchBranchesUseArrayElementKind includePlain includeWord branches
  | Stmt.internalCall _ args | Stmt.internalCallAssign _ _ args =>
      exprListUsesArrayElementKind includePlain includeWord args
  | Stmt.rawLog topics dataOffset dataSize =>
      exprListUsesArrayElementKind includePlain includeWord topics ||
        exprUsesArrayElementKind includePlain includeWord dataOffset ||
        exprUsesArrayElementKind includePlain includeWord dataSize
  | Stmt.externalCallBind _ _ args | Stmt.tryExternalCallBind _ _ _ args =>
      exprListUsesArrayElementKind includePlain includeWord args
  | Stmt.ecm _ args =>
      exprListUsesArrayElementKind includePlain includeWord args
  | Stmt.returnArray _ | Stmt.returnBytes _ | Stmt.returnStorageWords _
  | Stmt.revertReturndata | Stmt.stop =>
      false
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def stmtListUsesArrayElementKind (includePlain includeWord : Bool) : List Stmt → Bool
  | [] => false
  | s :: ss =>
      stmtUsesArrayElementKind includePlain includeWord s ||
        stmtListUsesArrayElementKind includePlain includeWord ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega

def matchBranchesUseArrayElementKind
    (includePlain includeWord : Bool) : List (String × List String × List Stmt) → Bool
  | [] => false
  | (_, _, body) :: rest =>
      stmtListUsesArrayElementKind includePlain includeWord body ||
        matchBranchesUseArrayElementKind includePlain includeWord rest
termination_by bs => sizeOf bs
decreasing_by all_goals simp_wf; all_goals omega
end

attribute [simp] exprUsesArrayElementKind exprListUsesArrayElementKind
  stmtUsesArrayElementKind stmtListUsesArrayElementKind matchBranchesUseArrayElementKind

@[simp] theorem stmtListUsesArrayElementKind_nil (includePlain includeWord : Bool) :
    stmtListUsesArrayElementKind includePlain includeWord [] = false := by
  simp [stmtListUsesArrayElementKind]

@[simp] theorem stmtListUsesArrayElementKind_cons
    (includePlain includeWord : Bool) (s : Stmt) (ss : List Stmt) :
    stmtListUsesArrayElementKind includePlain includeWord (s :: ss) =
      (stmtUsesArrayElementKind includePlain includeWord s ||
        stmtListUsesArrayElementKind includePlain includeWord ss) := by
  simp [stmtListUsesArrayElementKind]

mutual
def exprUsesArrayElement : Expr → Bool
  | Expr.arrayElement _ _ | Expr.memoryArrayElement _ _
  | Expr.arrayElementWord _ _ _ _ | Expr.arrayElementDynamicWord _ _ _
  | Expr.arrayElementDynamicDataOffset _ _
  | Expr.arrayElementDynamicMemberDataOffset _ _ _
  | Expr.arrayElementDynamicMemberLength _ _ _
  | Expr.arrayElementDynamicMemberElement _ _ _ _ =>
      true
  | Expr.mapping _ key | Expr.mappingWord _ key _ | Expr.mappingPackedWord _ key _ _
  | Expr.mappingUint _ key | Expr.structMember _ key _ =>
      exprUsesArrayElement key
  | Expr.mappingChain _ keys => exprListUsesArrayElement keys
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ =>
      exprUsesArrayElement key1 || exprUsesArrayElement key2
  | Expr.call gas target value inOffset inSize outOffset outSize =>
      exprUsesArrayElement gas || exprUsesArrayElement target || exprUsesArrayElement value ||
      exprUsesArrayElement inOffset || exprUsesArrayElement inSize ||
      exprUsesArrayElement outOffset || exprUsesArrayElement outSize
  | Expr.staticcall gas target inOffset inSize outOffset outSize
  | Expr.delegatecall gas target inOffset inSize outOffset outSize =>
      exprUsesArrayElement gas || exprUsesArrayElement target ||
      exprUsesArrayElement inOffset || exprUsesArrayElement inSize ||
      exprUsesArrayElement outOffset || exprUsesArrayElement outSize
  | Expr.extcodesize addr | Expr.mload addr | Expr.tload addr | Expr.calldataload addr
  | Expr.returndataOptionalBoolAt addr | Expr.storageArrayElement _ addr =>
      exprUsesArrayElement addr
  | Expr.keccak256 offset size =>
      exprUsesArrayElement offset || exprUsesArrayElement size
  | Expr.externalCall _ args | Expr.internalCall _ args | Expr.adtConstruct _ _ args =>
      exprListUsesArrayElement args
  | Expr.dynamicBytesEq _ _ | Expr.adtField _ _ _ _ _ =>
      false
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.sdiv a b
  | Expr.mod a b | Expr.smod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b
  | Expr.sar a b | Expr.signextend a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.sgt a b | Expr.lt a b | Expr.slt a b | Expr.le a b |
    Expr.logicalAnd a b | Expr.logicalOr a b |
    Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b |
    Expr.ceilDiv a b =>
      exprUsesArrayElement a || exprUsesArrayElement b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c | Expr.mulDiv512Down a b c | Expr.mulDiv512Up a b c =>
      exprUsesArrayElement a || exprUsesArrayElement b || exprUsesArrayElement c
  | Expr.bitNot a | Expr.logicalNot a =>
      exprUsesArrayElement a
  | Expr.ite cond thenVal elseVal =>
      exprUsesArrayElement cond || exprUsesArrayElement thenVal || exprUsesArrayElement elseVal
  | Expr.literal _ | Expr.param _ | Expr.constructorArg _ | Expr.storage _ | Expr.storageAddr _
  | Expr.caller | Expr.contractAddress | Expr.chainid | Expr.msgValue | Expr.selfBalance | Expr.blockTimestamp
  | Expr.blockNumber | Expr.blobbasefee
  | Expr.calldatasize | Expr.returndataSize | Expr.localVar _ | Expr.arrayLength _
  | Expr.memoryArrayLength _
  | Expr.storageArrayLength _
  | Expr.paramDynamicHeadWord _ _
  | Expr.paramDynamicStaticComposite _ _
  | Expr.paramDynamicMemberLength _ _
  | Expr.paramDynamicMemberDataOffset _ _
  | Expr.adtTag _ _ =>
      false
  | Expr.paramDynamicMemberElement _ _ innerIndex =>
      exprUsesArrayElement innerIndex
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

def exprListUsesArrayElement : List Expr → Bool
  | [] => false
  | e :: es => exprUsesArrayElement e || exprListUsesArrayElement es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

def stmtUsesArrayElement : Stmt → Bool
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value | Stmt.setStorageAddr _ value
  | Stmt.setStorageWord _ _ value | Stmt.storageArrayPush _ value
  | Stmt.return value | Stmt.require value _ =>
      exprUsesArrayElement value
  | Stmt.setStorageArrayElement _ index value =>
      exprUsesArrayElement index || exprUsesArrayElement value
  | Stmt.storageArrayPop _ =>
      false
  | Stmt.requireError cond _ args =>
      exprUsesArrayElement cond || exprListUsesArrayElement args
  | Stmt.revertError _ args | Stmt.emit _ args | Stmt.returnValues args =>
      exprListUsesArrayElement args
  | Stmt.mstore offset value | Stmt.tstore offset value =>
      exprUsesArrayElement offset || exprUsesArrayElement value
  | Stmt.calldatacopy destOffset sourceOffset size
  | Stmt.returndataCopy destOffset sourceOffset size =>
      exprUsesArrayElement destOffset || exprUsesArrayElement sourceOffset || exprUsesArrayElement size
  | Stmt.setMapping _ key value | Stmt.setMappingWord _ key _ value
  | Stmt.setMappingPackedWord _ key _ _ value | Stmt.setMappingUint _ key value
  | Stmt.setStructMember _ key _ value =>
      exprUsesArrayElement key || exprUsesArrayElement value
  | Stmt.setMappingChain _ keys value =>
      exprListUsesArrayElement keys || exprUsesArrayElement value
  | Stmt.setMapping2 _ key1 key2 value | Stmt.setMapping2Word _ key1 key2 _ value
  | Stmt.setStructMember2 _ key1 key2 _ value =>
      exprUsesArrayElement key1 || exprUsesArrayElement key2 || exprUsesArrayElement value
  | Stmt.ite cond thenBranch elseBranch =>
      exprUsesArrayElement cond || stmtListUsesArrayElement thenBranch ||
        stmtListUsesArrayElement elseBranch
  | Stmt.forEach _ count body =>
      exprUsesArrayElement count || stmtListUsesArrayElement body
  | Stmt.unsafeBlock _ body =>
      stmtListUsesArrayElement body
  | Stmt.matchAdt _ scrutinee branches =>
      exprUsesArrayElement scrutinee || matchBranchesUseArrayElement branches
  | Stmt.internalCall _ args | Stmt.internalCallAssign _ _ args =>
      exprListUsesArrayElement args
  | Stmt.rawLog topics dataOffset dataSize =>
      exprListUsesArrayElement topics || exprUsesArrayElement dataOffset || exprUsesArrayElement dataSize
  | Stmt.externalCallBind _ _ args | Stmt.tryExternalCallBind _ _ _ args | Stmt.ecm _ args =>
      exprListUsesArrayElement args
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

def matchBranchesUseArrayElement : List (String × List String × List Stmt) → Bool
  | [] => false
  | (_, _, body) :: rest => stmtListUsesArrayElement body || matchBranchesUseArrayElement rest
termination_by bs => sizeOf bs
decreasing_by all_goals simp_wf; all_goals omega
end

def functionUsesArrayElement (fn : FunctionSpec) : Bool :=
  fn.body.any stmtUsesArrayElement

def constructorUsesArrayElement : Option ConstructorSpec → Bool
  | none => false
  | some ctor => ctor.body.any stmtUsesArrayElement

def contractUsesArrayElement (spec : CompilationModel) : Bool :=
  constructorUsesArrayElement spec.constructor || spec.functions.any functionUsesArrayElement

abbrev exprUsesPlainArrayElement : Expr → Bool :=
  exprUsesArrayElementKind true false

abbrev exprListUsesPlainArrayElement : List Expr → Bool :=
  exprListUsesArrayElementKind true false

abbrev stmtUsesPlainArrayElement : Stmt → Bool :=
  stmtUsesArrayElementKind true false

abbrev stmtListUsesPlainArrayElement : List Stmt → Bool :=
  stmtListUsesArrayElementKind true false

abbrev matchBranchesUsePlainArrayElement : List (String × List String × List Stmt) → Bool :=
  matchBranchesUseArrayElementKind true false

def functionUsesPlainArrayElement (fn : FunctionSpec) : Bool :=
  functionUsesArrayElement fn && fn.body.any stmtUsesPlainArrayElement

def constructorUsesPlainArrayElement : Option ConstructorSpec → Bool
  | none => false
  | some ctor => constructorUsesArrayElement (some ctor) && ctor.body.any stmtUsesPlainArrayElement

def contractUsesPlainArrayElement (spec : CompilationModel) : Bool :=
  contractUsesArrayElement spec &&
    (constructorUsesPlainArrayElement spec.constructor || spec.functions.any functionUsesPlainArrayElement)

abbrev exprUsesArrayElementWord : Expr → Bool :=
  exprUsesArrayElementKind false true

abbrev exprListUsesArrayElementWord : List Expr → Bool :=
  exprListUsesArrayElementKind false true

abbrev stmtUsesArrayElementWord : Stmt → Bool :=
  stmtUsesArrayElementKind false true

abbrev stmtListUsesArrayElementWord : List Stmt → Bool :=
  stmtListUsesArrayElementKind false true

abbrev matchBranchesUseArrayElementWord : List (String × List String × List Stmt) → Bool :=
  matchBranchesUseArrayElementKind false true

def functionUsesArrayElementWord (fn : FunctionSpec) : Bool :=
  functionUsesArrayElement fn && fn.body.any stmtUsesArrayElementWord

def constructorUsesArrayElementWord : Option ConstructorSpec → Bool
  | none => false
  | some ctor => constructorUsesArrayElement (some ctor) && ctor.body.any stmtUsesArrayElementWord

def contractUsesArrayElementWord (spec : CompilationModel) : Bool :=
  contractUsesArrayElement spec &&
    (constructorUsesArrayElementWord spec.constructor || spec.functions.any functionUsesArrayElementWord)

-- Whether the given expression syntactically contains an
-- `Expr.paramDynamicHeadWord` (verity#1832). Plain `def` (not `partial`) so the
-- `SupportedSpec.contractUsesParamDynamicHeadWord_eq_false` proof chain in
-- `SupportedSpec.lean` can simp/unfold each case.
mutual
def exprUsesParamDynamicHeadWord : Expr → Bool
  | Expr.paramDynamicHeadWord _ _
  | Expr.paramDynamicStaticComposite _ _ => true
  | Expr.paramDynamicMemberLength _ _
  | Expr.paramDynamicMemberDataOffset _ _ => true
  | Expr.paramDynamicMemberElement _ _ innerIndex =>
      exprUsesParamDynamicHeadWord innerIndex
  | Expr.mapping _ key | Expr.mappingWord _ key _ | Expr.mappingPackedWord _ key _ _
  | Expr.mappingUint _ key | Expr.structMember _ key _
  | Expr.storageArrayElement _ key | Expr.arrayElement _ key | Expr.memoryArrayElement _ key
  | Expr.arrayElementWord _ key _ _ | Expr.arrayElementDynamicWord _ key _
  | Expr.arrayElementDynamicDataOffset _ key
  | Expr.arrayElementDynamicMemberDataOffset _ key _
  | Expr.arrayElementDynamicMemberLength _ key _ =>
      exprUsesParamDynamicHeadWord key
  | Expr.arrayElementDynamicMemberElement _ key _ innerKey =>
      exprUsesParamDynamicHeadWord key || exprUsesParamDynamicHeadWord innerKey
  | Expr.mappingChain _ keys => exprListUsesParamDynamicHeadWord keys
  | Expr.mapping2 _ k1 k2 | Expr.mapping2Word _ k1 k2 _ | Expr.structMember2 _ k1 k2 _ =>
      exprUsesParamDynamicHeadWord k1 || exprUsesParamDynamicHeadWord k2
  | Expr.call gas target value inOffset inSize outOffset outSize =>
      exprUsesParamDynamicHeadWord gas || exprUsesParamDynamicHeadWord target ||
      exprUsesParamDynamicHeadWord value || exprUsesParamDynamicHeadWord inOffset ||
      exprUsesParamDynamicHeadWord inSize || exprUsesParamDynamicHeadWord outOffset ||
      exprUsesParamDynamicHeadWord outSize
  | Expr.staticcall gas target inOffset inSize outOffset outSize
  | Expr.delegatecall gas target inOffset inSize outOffset outSize =>
      exprUsesParamDynamicHeadWord gas || exprUsesParamDynamicHeadWord target ||
      exprUsesParamDynamicHeadWord inOffset || exprUsesParamDynamicHeadWord inSize ||
      exprUsesParamDynamicHeadWord outOffset || exprUsesParamDynamicHeadWord outSize
  | Expr.extcodesize a | Expr.mload a | Expr.tload a | Expr.calldataload a
  | Expr.returndataOptionalBoolAt a | Expr.bitNot a | Expr.logicalNot a =>
      exprUsesParamDynamicHeadWord a
  | Expr.keccak256 a b =>
      exprUsesParamDynamicHeadWord a || exprUsesParamDynamicHeadWord b
  | Expr.externalCall _ args | Expr.internalCall _ args | Expr.adtConstruct _ _ args =>
      exprListUsesParamDynamicHeadWord args
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.sdiv a b
  | Expr.mod a b | Expr.smod a b
  | Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b
  | Expr.sar a b | Expr.signextend a b
  | Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.sgt a b | Expr.lt a b | Expr.slt a b
  | Expr.le a b | Expr.logicalAnd a b | Expr.logicalOr a b
  | Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b | Expr.ceilDiv a b =>
      exprUsesParamDynamicHeadWord a || exprUsesParamDynamicHeadWord b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c
  | Expr.mulDiv512Down a b c | Expr.mulDiv512Up a b c
  | Expr.ite a b c =>
      exprUsesParamDynamicHeadWord a || exprUsesParamDynamicHeadWord b ||
      exprUsesParamDynamicHeadWord c
  | Expr.literal _ | Expr.param _ | Expr.constructorArg _
  | Expr.storage _ | Expr.storageAddr _
  | Expr.caller | Expr.contractAddress | Expr.chainid | Expr.msgValue | Expr.selfBalance
  | Expr.blockTimestamp | Expr.blockNumber | Expr.blobbasefee
  | Expr.calldatasize | Expr.returndataSize | Expr.localVar _ | Expr.arrayLength _
  | Expr.memoryArrayLength _
  | Expr.storageArrayLength _
  | Expr.dynamicBytesEq _ _
  | Expr.adtTag _ _ | Expr.adtField _ _ _ _ _ =>
      false
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

def exprListUsesParamDynamicHeadWord : List Expr → Bool
  | [] => false
  | e :: es => exprUsesParamDynamicHeadWord e || exprListUsesParamDynamicHeadWord es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
def stmtUsesParamDynamicHeadWord : Stmt → Bool
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value
  | Stmt.setStorageAddr _ value | Stmt.setStorageWord _ _ value
  | Stmt.storageArrayPush _ value | Stmt.return value | Stmt.require value _ =>
      exprUsesParamDynamicHeadWord value
  | Stmt.setStorageArrayElement _ index value =>
      exprUsesParamDynamicHeadWord index || exprUsesParamDynamicHeadWord value
  | Stmt.storageArrayPop _ => false
  | Stmt.requireError cond _ args =>
      exprUsesParamDynamicHeadWord cond || exprListUsesParamDynamicHeadWord args
  | Stmt.revertError _ args | Stmt.emit _ args | Stmt.returnValues args =>
      exprListUsesParamDynamicHeadWord args
  | Stmt.mstore offset value | Stmt.tstore offset value =>
      exprUsesParamDynamicHeadWord offset || exprUsesParamDynamicHeadWord value
  | Stmt.calldatacopy a b c | Stmt.returndataCopy a b c =>
      exprUsesParamDynamicHeadWord a || exprUsesParamDynamicHeadWord b ||
      exprUsesParamDynamicHeadWord c
  | Stmt.setMapping _ k v | Stmt.setMappingWord _ k _ v
  | Stmt.setMappingPackedWord _ k _ _ v | Stmt.setMappingUint _ k v
  | Stmt.setStructMember _ k _ v =>
      exprUsesParamDynamicHeadWord k || exprUsesParamDynamicHeadWord v
  | Stmt.setMappingChain _ keys v =>
      exprListUsesParamDynamicHeadWord keys || exprUsesParamDynamicHeadWord v
  | Stmt.setMapping2 _ k1 k2 v | Stmt.setMapping2Word _ k1 k2 _ v
  | Stmt.setStructMember2 _ k1 k2 _ v =>
      exprUsesParamDynamicHeadWord k1 || exprUsesParamDynamicHeadWord k2 ||
      exprUsesParamDynamicHeadWord v
  | Stmt.ite cond thenBranch elseBranch =>
      exprUsesParamDynamicHeadWord cond ||
        stmtListUsesParamDynamicHeadWord thenBranch ||
        stmtListUsesParamDynamicHeadWord elseBranch
  | Stmt.forEach _ count body =>
      exprUsesParamDynamicHeadWord count || stmtListUsesParamDynamicHeadWord body
  | Stmt.unsafeBlock _ body =>
      stmtListUsesParamDynamicHeadWord body
  | Stmt.matchAdt _ scrutinee branches =>
      exprUsesParamDynamicHeadWord scrutinee || matchBranchesUseParamDynamicHeadWord branches
  | Stmt.internalCall _ args | Stmt.internalCallAssign _ _ args
  | Stmt.externalCallBind _ _ args | Stmt.tryExternalCallBind _ _ _ args
  | Stmt.ecm _ args =>
      exprListUsesParamDynamicHeadWord args
  | Stmt.rawLog topics dataOffset dataSize =>
      exprListUsesParamDynamicHeadWord topics ||
        exprUsesParamDynamicHeadWord dataOffset ||
        exprUsesParamDynamicHeadWord dataSize
  | Stmt.returnArray _ | Stmt.returnBytes _ | Stmt.returnStorageWords _
  | Stmt.revertReturndata | Stmt.stop =>
      false
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def stmtListUsesParamDynamicHeadWord : List Stmt → Bool
  | [] => false
  | s :: ss => stmtUsesParamDynamicHeadWord s || stmtListUsesParamDynamicHeadWord ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega

def matchBranchesUseParamDynamicHeadWord : List (String × List String × List Stmt) → Bool
  | [] => false
  | (_, _, body) :: rest =>
      stmtListUsesParamDynamicHeadWord body || matchBranchesUseParamDynamicHeadWord rest
termination_by bs => sizeOf bs
decreasing_by all_goals simp_wf; all_goals omega
end

def contractUsesParamDynamicHeadWord (spec : CompilationModel) : Bool :=
  (match spec.constructor with
    | none => false
    | some ctor => ctor.body.any stmtUsesParamDynamicHeadWord) ||
  spec.functions.any (fun fn => fn.body.any stmtUsesParamDynamicHeadWord)

-- Whether the given expression syntactically contains an
-- `Expr.mulDiv512Down` or `Expr.mulDiv512Up` (verity#1761).
-- Plain `def` (not `partial`) so the `SupportedSpec.contractUsesMulDiv512_eq_false`
-- proof chain in `SupportedSpec.lean` can simp/unfold each case.
mutual
def exprUsesMulDiv512 : Expr → Bool
  | Expr.mulDiv512Down _ _ _ | Expr.mulDiv512Up _ _ _ => true
  | Expr.mapping _ key | Expr.mappingWord _ key _ | Expr.mappingPackedWord _ key _ _
  | Expr.mappingUint _ key | Expr.structMember _ key _
  | Expr.storageArrayElement _ key | Expr.arrayElement _ key | Expr.memoryArrayElement _ key
  | Expr.arrayElementWord _ key _ _ | Expr.arrayElementDynamicWord _ key _
  | Expr.arrayElementDynamicDataOffset _ key
  | Expr.arrayElementDynamicMemberDataOffset _ key _
  | Expr.arrayElementDynamicMemberLength _ key _ =>
      exprUsesMulDiv512 key
  | Expr.arrayElementDynamicMemberElement _ key _ innerKey =>
      exprUsesMulDiv512 key || exprUsesMulDiv512 innerKey
  | Expr.mappingChain _ keys => exprListUsesMulDiv512 keys
  | Expr.mapping2 _ k1 k2 | Expr.mapping2Word _ k1 k2 _ | Expr.structMember2 _ k1 k2 _ =>
      exprUsesMulDiv512 k1 || exprUsesMulDiv512 k2
  | Expr.call gas target value inOffset inSize outOffset outSize =>
      exprUsesMulDiv512 gas || exprUsesMulDiv512 target || exprUsesMulDiv512 value ||
      exprUsesMulDiv512 inOffset || exprUsesMulDiv512 inSize ||
      exprUsesMulDiv512 outOffset || exprUsesMulDiv512 outSize
  | Expr.staticcall gas target inOffset inSize outOffset outSize
  | Expr.delegatecall gas target inOffset inSize outOffset outSize =>
      exprUsesMulDiv512 gas || exprUsesMulDiv512 target ||
      exprUsesMulDiv512 inOffset || exprUsesMulDiv512 inSize ||
      exprUsesMulDiv512 outOffset || exprUsesMulDiv512 outSize
  | Expr.extcodesize a | Expr.mload a | Expr.tload a | Expr.calldataload a
  | Expr.returndataOptionalBoolAt a | Expr.bitNot a | Expr.logicalNot a =>
      exprUsesMulDiv512 a
  | Expr.keccak256 a b =>
      exprUsesMulDiv512 a || exprUsesMulDiv512 b
  | Expr.externalCall _ args | Expr.internalCall _ args | Expr.adtConstruct _ _ args =>
      exprListUsesMulDiv512 args
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.sdiv a b
  | Expr.mod a b | Expr.smod a b
  | Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b
  | Expr.sar a b | Expr.signextend a b
  | Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.sgt a b | Expr.lt a b | Expr.slt a b
  | Expr.le a b | Expr.logicalAnd a b | Expr.logicalOr a b
  | Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b | Expr.ceilDiv a b =>
      exprUsesMulDiv512 a || exprUsesMulDiv512 b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c | Expr.ite a b c =>
      exprUsesMulDiv512 a || exprUsesMulDiv512 b || exprUsesMulDiv512 c
  | Expr.literal _ | Expr.param _ | Expr.constructorArg _
  | Expr.storage _ | Expr.storageAddr _
  | Expr.caller | Expr.contractAddress | Expr.chainid | Expr.msgValue | Expr.selfBalance
  | Expr.blockTimestamp | Expr.blockNumber | Expr.blobbasefee
  | Expr.calldatasize | Expr.returndataSize | Expr.localVar _ | Expr.arrayLength _
  | Expr.memoryArrayLength _
  | Expr.storageArrayLength _
  | Expr.paramDynamicHeadWord _ _
  | Expr.paramDynamicStaticComposite _ _
  | Expr.paramDynamicMemberLength _ _
  | Expr.paramDynamicMemberDataOffset _ _
  | Expr.dynamicBytesEq _ _
  | Expr.adtTag _ _ | Expr.adtField _ _ _ _ _ =>
      false
  | Expr.paramDynamicMemberElement _ _ innerIndex =>
      exprUsesMulDiv512 innerIndex
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

def exprListUsesMulDiv512 : List Expr → Bool
  | [] => false
  | e :: es => exprUsesMulDiv512 e || exprListUsesMulDiv512 es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
def stmtUsesMulDiv512 : Stmt → Bool
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value
  | Stmt.setStorageAddr _ value | Stmt.setStorageWord _ _ value
  | Stmt.storageArrayPush _ value | Stmt.return value | Stmt.require value _ =>
      exprUsesMulDiv512 value
  | Stmt.setStorageArrayElement _ index value =>
      exprUsesMulDiv512 index || exprUsesMulDiv512 value
  | Stmt.storageArrayPop _ => false
  | Stmt.requireError cond _ args =>
      exprUsesMulDiv512 cond || exprListUsesMulDiv512 args
  | Stmt.revertError _ args | Stmt.emit _ args | Stmt.returnValues args =>
      exprListUsesMulDiv512 args
  | Stmt.mstore offset value | Stmt.tstore offset value =>
      exprUsesMulDiv512 offset || exprUsesMulDiv512 value
  | Stmt.calldatacopy a b c | Stmt.returndataCopy a b c =>
      exprUsesMulDiv512 a || exprUsesMulDiv512 b || exprUsesMulDiv512 c
  | Stmt.setMapping _ k v | Stmt.setMappingWord _ k _ v
  | Stmt.setMappingPackedWord _ k _ _ v | Stmt.setMappingUint _ k v
  | Stmt.setStructMember _ k _ v =>
      exprUsesMulDiv512 k || exprUsesMulDiv512 v
  | Stmt.setMappingChain _ keys v =>
      exprListUsesMulDiv512 keys || exprUsesMulDiv512 v
  | Stmt.setMapping2 _ k1 k2 v | Stmt.setMapping2Word _ k1 k2 _ v
  | Stmt.setStructMember2 _ k1 k2 _ v =>
      exprUsesMulDiv512 k1 || exprUsesMulDiv512 k2 || exprUsesMulDiv512 v
  | Stmt.ite cond thenBranch elseBranch =>
      exprUsesMulDiv512 cond ||
        stmtListUsesMulDiv512 thenBranch ||
        stmtListUsesMulDiv512 elseBranch
  | Stmt.forEach _ count body =>
      exprUsesMulDiv512 count || stmtListUsesMulDiv512 body
  | Stmt.unsafeBlock _ body =>
      stmtListUsesMulDiv512 body
  | Stmt.matchAdt _ scrutinee branches =>
      exprUsesMulDiv512 scrutinee || matchBranchesUseMulDiv512 branches
  | Stmt.internalCall _ args | Stmt.internalCallAssign _ _ args
  | Stmt.externalCallBind _ _ args | Stmt.tryExternalCallBind _ _ _ args
  | Stmt.ecm _ args =>
      exprListUsesMulDiv512 args
  | Stmt.rawLog topics dataOffset dataSize =>
      exprListUsesMulDiv512 topics ||
        exprUsesMulDiv512 dataOffset || exprUsesMulDiv512 dataSize
  | Stmt.returnArray _ | Stmt.returnBytes _ | Stmt.returnStorageWords _
  | Stmt.revertReturndata | Stmt.stop =>
      false
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def stmtListUsesMulDiv512 : List Stmt → Bool
  | [] => false
  | s :: ss => stmtUsesMulDiv512 s || stmtListUsesMulDiv512 ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega

def matchBranchesUseMulDiv512 : List (String × List String × List Stmt) → Bool
  | [] => false
  | (_, _, body) :: rest =>
      stmtListUsesMulDiv512 body || matchBranchesUseMulDiv512 rest
termination_by bs => sizeOf bs
decreasing_by all_goals simp_wf; all_goals omega
end

def contractUsesMulDiv512 (spec : CompilationModel) : Bool :=
  (match spec.constructor with
    | none => false
    | some ctor => ctor.body.any stmtUsesMulDiv512) ||
  spec.functions.any (fun fn => fn.body.any stmtUsesMulDiv512)

private def nestedPlainWithWordIndex : Expr :=
  Expr.arrayElement "plain" (Expr.arrayElementWord "word" (Expr.literal 0) 1 0)

private def nestedWordWithPlainIndex : Expr :=
  Expr.arrayElementWord "word" (Expr.arrayElement "plain" (Expr.literal 0)) 1 0

example : exprUsesPlainArrayElement nestedPlainWithWordIndex = true := by
  native_decide

example : exprUsesArrayElementWord nestedPlainWithWordIndex = true := by
  native_decide

example : exprUsesPlainArrayElement nestedWordWithPlainIndex = true := by
  native_decide

example : exprUsesArrayElementWord nestedWordWithPlainIndex = true := by
  native_decide

mutual
def exprUsesStorageArrayElement : Expr → Bool
  | Expr.storageArrayElement _ _ => true
  | Expr.mapping _ key => exprUsesStorageArrayElement key
  | Expr.mappingWord _ key _ => exprUsesStorageArrayElement key
  | Expr.mappingPackedWord _ key _ _ => exprUsesStorageArrayElement key
  | Expr.mappingChain _ keys => exprListUsesStorageArrayElement keys
  | Expr.structMember _ key _ => exprUsesStorageArrayElement key
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ => exprUsesStorageArrayElement key1 || exprUsesStorageArrayElement key2
  | Expr.mappingUint _ key => exprUsesStorageArrayElement key
  | Expr.call gas target value inOffset inSize outOffset outSize =>
      exprUsesStorageArrayElement gas || exprUsesStorageArrayElement target || exprUsesStorageArrayElement value ||
      exprUsesStorageArrayElement inOffset || exprUsesStorageArrayElement inSize ||
      exprUsesStorageArrayElement outOffset || exprUsesStorageArrayElement outSize
  | Expr.staticcall gas target inOffset inSize outOffset outSize =>
      exprUsesStorageArrayElement gas || exprUsesStorageArrayElement target ||
      exprUsesStorageArrayElement inOffset || exprUsesStorageArrayElement inSize ||
      exprUsesStorageArrayElement outOffset || exprUsesStorageArrayElement outSize
  | Expr.delegatecall gas target inOffset inSize outOffset outSize =>
      exprUsesStorageArrayElement gas || exprUsesStorageArrayElement target ||
      exprUsesStorageArrayElement inOffset || exprUsesStorageArrayElement inSize ||
      exprUsesStorageArrayElement outOffset || exprUsesStorageArrayElement outSize
  | Expr.extcodesize addr => exprUsesStorageArrayElement addr
  | Expr.mload offset => exprUsesStorageArrayElement offset
  | Expr.tload offset => exprUsesStorageArrayElement offset
  | Expr.calldataload offset => exprUsesStorageArrayElement offset
  | Expr.keccak256 offset size => exprUsesStorageArrayElement offset || exprUsesStorageArrayElement size
  | Expr.returndataOptionalBoolAt outOffset => exprUsesStorageArrayElement outOffset
  | Expr.externalCall _ args | Expr.internalCall _ args =>
      exprListUsesStorageArrayElement args
  | Expr.dynamicBytesEq _ _ =>
      false
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.sdiv a b
  | Expr.mod a b | Expr.smod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b
  | Expr.sar a b | Expr.signextend a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.sgt a b | Expr.lt a b | Expr.slt a b | Expr.le a b |
    Expr.logicalAnd a b | Expr.logicalOr a b |
    Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b |
    Expr.ceilDiv a b =>
      exprUsesStorageArrayElement a || exprUsesStorageArrayElement b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c | Expr.mulDiv512Down a b c | Expr.mulDiv512Up a b c =>
      exprUsesStorageArrayElement a || exprUsesStorageArrayElement b || exprUsesStorageArrayElement c
  | Expr.bitNot a | Expr.logicalNot a =>
      exprUsesStorageArrayElement a
  | Expr.ite cond thenVal elseVal =>
      exprUsesStorageArrayElement cond || exprUsesStorageArrayElement thenVal || exprUsesStorageArrayElement elseVal
  | Expr.adtConstruct _ _ args => exprListUsesStorageArrayElement args
  | Expr.adtField _ _ _ _ _ => false
  | Expr.literal _ | Expr.param _ | Expr.constructorArg _ | Expr.storage _ | Expr.storageAddr _
  | Expr.caller | Expr.contractAddress | Expr.chainid | Expr.msgValue | Expr.selfBalance | Expr.blockTimestamp
  | Expr.blockNumber | Expr.blobbasefee
  | Expr.calldatasize | Expr.returndataSize | Expr.localVar _ | Expr.arrayLength _
  | Expr.memoryArrayLength _ | Expr.storageArrayLength _
  | Expr.paramDynamicHeadWord _ _
  | Expr.paramDynamicStaticComposite _ _
  | Expr.paramDynamicMemberLength _ _
  | Expr.paramDynamicMemberDataOffset _ _
  | Expr.adtTag _ _ =>
      false
  | Expr.paramDynamicMemberElement _ _ innerIndex =>
      exprUsesStorageArrayElement innerIndex
  | Expr.arrayElement _ index | Expr.memoryArrayElement _ index
  | Expr.arrayElementWord _ index _ _ | Expr.arrayElementDynamicWord _ index _
  | Expr.arrayElementDynamicDataOffset _ index
  | Expr.arrayElementDynamicMemberDataOffset _ index _
  | Expr.arrayElementDynamicMemberLength _ index _ =>
      exprUsesStorageArrayElement index
  | Expr.arrayElementDynamicMemberElement _ index _ innerIndex =>
      exprUsesStorageArrayElement index || exprUsesStorageArrayElement innerIndex
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

def exprListUsesStorageArrayElement : List Expr → Bool
  | [] => false
  | e :: es => exprUsesStorageArrayElement e || exprListUsesStorageArrayElement es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

def stmtUsesStorageArrayElement : Stmt → Bool
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value | Stmt.setStorageAddr _ value
  | Stmt.setStorageWord _ _ value |
    Stmt.storageArrayPush _ value |
    Stmt.return value | Stmt.require value _ =>
      exprUsesStorageArrayElement value
  | Stmt.setStorageArrayElement _ index value =>
      exprUsesStorageArrayElement index || exprUsesStorageArrayElement value
  | Stmt.storageArrayPop _ =>
      false
  | Stmt.requireError cond _ args =>
      exprUsesStorageArrayElement cond || exprListUsesStorageArrayElement args
  | Stmt.revertError _ args | Stmt.emit _ args | Stmt.returnValues args =>
      exprListUsesStorageArrayElement args
  | Stmt.mstore offset value =>
      exprUsesStorageArrayElement offset || exprUsesStorageArrayElement value
  | Stmt.tstore offset value =>
      exprUsesStorageArrayElement offset || exprUsesStorageArrayElement value
  | Stmt.calldatacopy destOffset sourceOffset size =>
      exprUsesStorageArrayElement destOffset || exprUsesStorageArrayElement sourceOffset || exprUsesStorageArrayElement size
  | Stmt.returndataCopy destOffset sourceOffset size =>
      exprUsesStorageArrayElement destOffset || exprUsesStorageArrayElement sourceOffset || exprUsesStorageArrayElement size
  | Stmt.setMapping _ key value | Stmt.setMappingWord _ key _ value | Stmt.setMappingPackedWord _ key _ _ value | Stmt.setMappingUint _ key value
  | Stmt.setStructMember _ key _ value =>
      exprUsesStorageArrayElement key || exprUsesStorageArrayElement value
  | Stmt.setMappingChain _ keys value =>
      exprListUsesStorageArrayElement keys || exprUsesStorageArrayElement value
  | Stmt.setMapping2 _ key1 key2 value | Stmt.setMapping2Word _ key1 key2 _ value
  | Stmt.setStructMember2 _ key1 key2 _ value =>
      exprUsesStorageArrayElement key1 || exprUsesStorageArrayElement key2 || exprUsesStorageArrayElement value
  | Stmt.ite cond thenBranch elseBranch =>
      exprUsesStorageArrayElement cond || stmtListUsesStorageArrayElement thenBranch || stmtListUsesStorageArrayElement elseBranch
  | Stmt.forEach _ count body =>
      exprUsesStorageArrayElement count || stmtListUsesStorageArrayElement body
  | Stmt.unsafeBlock _ body =>
      stmtListUsesStorageArrayElement body
  | Stmt.matchAdt _ scrutinee branches =>
      exprUsesStorageArrayElement scrutinee ||
        matchBranchesUseStorageArrayElement branches
  | Stmt.internalCall _ args | Stmt.internalCallAssign _ _ args
  | Stmt.externalCallBind _ _ args | Stmt.tryExternalCallBind _ _ _ args =>
      exprListUsesStorageArrayElement args
  | Stmt.rawLog topics dataOffset dataSize =>
      exprListUsesStorageArrayElement topics || exprUsesStorageArrayElement dataOffset || exprUsesStorageArrayElement dataSize
  | Stmt.ecm _ args =>
      exprListUsesStorageArrayElement args
  | Stmt.returnArray _ | Stmt.returnBytes _ | Stmt.returnStorageWords _
  | Stmt.revertReturndata | Stmt.stop =>
      false
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def stmtListUsesStorageArrayElement : List Stmt → Bool
  | [] => false
  | s :: ss => stmtUsesStorageArrayElement s || stmtListUsesStorageArrayElement ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega

def matchBranchesUseStorageArrayElement : List (String × List String × List Stmt) → Bool
  | [] => false
  | (_, _, body) :: rest =>
      stmtListUsesStorageArrayElement body || matchBranchesUseStorageArrayElement rest
termination_by bs => sizeOf bs
decreasing_by all_goals simp_wf; all_goals omega
end

def functionUsesStorageArrayElement (fn : FunctionSpec) : Bool :=
  fn.body.any stmtUsesStorageArrayElement

def constructorUsesStorageArrayElement : Option ConstructorSpec → Bool
  | none => false
  | some ctor => ctor.body.any stmtUsesStorageArrayElement

def contractUsesStorageArrayElement (spec : CompilationModel) : Bool :=
  constructorUsesStorageArrayElement spec.constructor || spec.functions.any functionUsesStorageArrayElement

mutual
def exprUsesDynamicBytesEq : Expr → Bool
  | Expr.dynamicBytesEq _ _ => true
  | Expr.mapping _ key => exprUsesDynamicBytesEq key
  | Expr.mappingWord _ key _ => exprUsesDynamicBytesEq key
  | Expr.mappingPackedWord _ key _ _ => exprUsesDynamicBytesEq key
  | Expr.mappingChain _ keys => exprListUsesDynamicBytesEq keys
  | Expr.structMember _ key _ => exprUsesDynamicBytesEq key
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ =>
      exprUsesDynamicBytesEq key1 || exprUsesDynamicBytesEq key2
  | Expr.mappingUint _ key => exprUsesDynamicBytesEq key
  | Expr.call gas target value inOffset inSize outOffset outSize =>
      exprUsesDynamicBytesEq gas || exprUsesDynamicBytesEq target || exprUsesDynamicBytesEq value ||
      exprUsesDynamicBytesEq inOffset || exprUsesDynamicBytesEq inSize ||
      exprUsesDynamicBytesEq outOffset || exprUsesDynamicBytesEq outSize
  | Expr.staticcall gas target inOffset inSize outOffset outSize =>
      exprUsesDynamicBytesEq gas || exprUsesDynamicBytesEq target ||
      exprUsesDynamicBytesEq inOffset || exprUsesDynamicBytesEq inSize ||
      exprUsesDynamicBytesEq outOffset || exprUsesDynamicBytesEq outSize
  | Expr.delegatecall gas target inOffset inSize outOffset outSize =>
      exprUsesDynamicBytesEq gas || exprUsesDynamicBytesEq target ||
      exprUsesDynamicBytesEq inOffset || exprUsesDynamicBytesEq inSize ||
      exprUsesDynamicBytesEq outOffset || exprUsesDynamicBytesEq outSize
  | Expr.extcodesize addr => exprUsesDynamicBytesEq addr
  | Expr.mload offset | Expr.tload offset => exprUsesDynamicBytesEq offset
  | Expr.calldataload offset => exprUsesDynamicBytesEq offset
  | Expr.keccak256 offset size => exprUsesDynamicBytesEq offset || exprUsesDynamicBytesEq size
  | Expr.returndataOptionalBoolAt outOffset => exprUsesDynamicBytesEq outOffset
  | Expr.externalCall _ args | Expr.internalCall _ args =>
      exprListUsesDynamicBytesEq args
  | Expr.storageArrayElement _ index | Expr.arrayElement _ index | Expr.memoryArrayElement _ index
  | Expr.arrayElementWord _ index _ _ | Expr.arrayElementDynamicWord _ index _
  | Expr.arrayElementDynamicDataOffset _ index
  | Expr.arrayElementDynamicMemberDataOffset _ index _
  | Expr.arrayElementDynamicMemberLength _ index _ => exprUsesDynamicBytesEq index
  | Expr.arrayElementDynamicMemberElement _ index _ innerIndex =>
      exprUsesDynamicBytesEq index || exprUsesDynamicBytesEq innerIndex
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.sdiv a b
  | Expr.mod a b | Expr.smod a b
  | Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b
  | Expr.sar a b | Expr.signextend a b
  | Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.sgt a b | Expr.lt a b | Expr.slt a b | Expr.le a b
  | Expr.logicalAnd a b | Expr.logicalOr a b
  | Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b
  | Expr.ceilDiv a b =>
      exprUsesDynamicBytesEq a || exprUsesDynamicBytesEq b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c | Expr.mulDiv512Down a b c | Expr.mulDiv512Up a b c =>
      exprUsesDynamicBytesEq a || exprUsesDynamicBytesEq b || exprUsesDynamicBytesEq c
  | Expr.bitNot a | Expr.logicalNot a =>
      exprUsesDynamicBytesEq a
  | Expr.ite cond thenVal elseVal =>
      exprUsesDynamicBytesEq cond || exprUsesDynamicBytesEq thenVal || exprUsesDynamicBytesEq elseVal
  | Expr.adtConstruct _ _ args => exprListUsesDynamicBytesEq args
  | Expr.adtField _ _ _ _ _ => false
  | Expr.literal _ | Expr.param _ | Expr.constructorArg _ | Expr.storage _ | Expr.storageAddr _
  | Expr.caller | Expr.contractAddress | Expr.chainid | Expr.msgValue | Expr.selfBalance | Expr.blockTimestamp
  | Expr.blockNumber | Expr.blobbasefee
  | Expr.calldatasize | Expr.returndataSize | Expr.localVar _ | Expr.arrayLength _
  | Expr.memoryArrayLength _ | Expr.storageArrayLength _
  | Expr.paramDynamicHeadWord _ _
  | Expr.paramDynamicStaticComposite _ _
  | Expr.paramDynamicMemberLength _ _
  | Expr.paramDynamicMemberDataOffset _ _
  | Expr.adtTag _ _ =>
      false
  | Expr.paramDynamicMemberElement _ _ innerIndex =>
      exprUsesDynamicBytesEq innerIndex
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

def exprListUsesDynamicBytesEq : List Expr → Bool
  | [] => false
  | e :: es => exprUsesDynamicBytesEq e || exprListUsesDynamicBytesEq es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

def stmtUsesDynamicBytesEq : Stmt → Bool
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value | Stmt.setStorageAddr _ value
  | Stmt.setStorageWord _ _ value
  | Stmt.storageArrayPush _ value
  | Stmt.return value | Stmt.require value _ =>
      exprUsesDynamicBytesEq value
  | Stmt.setStorageArrayElement _ index value =>
      exprUsesDynamicBytesEq index || exprUsesDynamicBytesEq value
  | Stmt.storageArrayPop _ =>
      false
  | Stmt.requireError cond _ args =>
      exprUsesDynamicBytesEq cond || exprListUsesDynamicBytesEq args
  | Stmt.revertError _ args | Stmt.emit _ args | Stmt.returnValues args =>
      exprListUsesDynamicBytesEq args
  | Stmt.mstore offset value | Stmt.tstore offset value =>
      exprUsesDynamicBytesEq offset || exprUsesDynamicBytesEq value
  | Stmt.calldatacopy destOffset sourceOffset size
  | Stmt.returndataCopy destOffset sourceOffset size =>
      exprUsesDynamicBytesEq destOffset || exprUsesDynamicBytesEq sourceOffset || exprUsesDynamicBytesEq size
  | Stmt.setMapping _ key value | Stmt.setMappingWord _ key _ value | Stmt.setMappingPackedWord _ key _ _ value
  | Stmt.setMappingUint _ key value
  | Stmt.setStructMember _ key _ value =>
      exprUsesDynamicBytesEq key || exprUsesDynamicBytesEq value
  | Stmt.setMappingChain _ keys value =>
      exprListUsesDynamicBytesEq keys || exprUsesDynamicBytesEq value
  | Stmt.setMapping2 _ key1 key2 value | Stmt.setMapping2Word _ key1 key2 _ value
  | Stmt.setStructMember2 _ key1 key2 _ value =>
      exprUsesDynamicBytesEq key1 || exprUsesDynamicBytesEq key2 || exprUsesDynamicBytesEq value
  | Stmt.ite cond thenBranch elseBranch =>
      exprUsesDynamicBytesEq cond || stmtListUsesDynamicBytesEq thenBranch || stmtListUsesDynamicBytesEq elseBranch
  | Stmt.forEach _ count body =>
      exprUsesDynamicBytesEq count || stmtListUsesDynamicBytesEq body
  | Stmt.unsafeBlock _ body =>
      stmtListUsesDynamicBytesEq body
  | Stmt.matchAdt _ scrutinee branches =>
      exprUsesDynamicBytesEq scrutinee ||
        matchBranchesUseDynamicBytesEq branches
  | Stmt.internalCall _ args | Stmt.internalCallAssign _ _ args
  | Stmt.externalCallBind _ _ args | Stmt.tryExternalCallBind _ _ _ args
  | Stmt.ecm _ args =>
      exprListUsesDynamicBytesEq args
  | Stmt.rawLog topics dataOffset dataSize =>
      exprListUsesDynamicBytesEq topics || exprUsesDynamicBytesEq dataOffset || exprUsesDynamicBytesEq dataSize
  | Stmt.returnArray _ | Stmt.returnBytes _ | Stmt.returnStorageWords _
  | Stmt.revertReturndata | Stmt.stop =>
      false
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def stmtListUsesDynamicBytesEq : List Stmt → Bool
  | [] => false
  | s :: ss => stmtUsesDynamicBytesEq s || stmtListUsesDynamicBytesEq ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega

def matchBranchesUseDynamicBytesEq : List (String × List String × List Stmt) → Bool
  | [] => false
  | (_, _, body) :: rest =>
      stmtListUsesDynamicBytesEq body || matchBranchesUseDynamicBytesEq rest
termination_by bs => sizeOf bs
decreasing_by all_goals simp_wf; all_goals omega
end

def contractUsesDynamicBytesEq (spec : CompilationModel) : Bool :=
  (spec.constructor.map (fun ctor => ctor.body.any stmtUsesDynamicBytesEq) |>.getD false) ||
    spec.functions.any (fun fn => fn.body.any stmtUsesDynamicBytesEq)

end Compiler.CompilationModel
