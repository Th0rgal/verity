/- 
  Compiler.CompilationModel.ValidationCalls: Call graph and identifier validation
-/
import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.AbiTypeLayout
import Compiler.CompilationModel.DynamicData
import Compiler.CompilationModel.InternalNaming
import Compiler.CompilationModel.IssueRefs
import Compiler.CompilationModel.UsageAnalysis

namespace Compiler.CompilationModel

def reservedExternalNames
    (mappingHelpersRequired arrayHelpersRequired storageArrayHelpersRequired dynamicBytesEqHelpersRequired : Bool) : List String :=
  let mappingHelpers := if mappingHelpersRequired then ["mappingSlot"] else []
  let arrayHelpers :=
    if arrayHelpersRequired then
      [checkedArrayElementCalldataHelperName, checkedArrayElementMemoryHelperName]
    else
      []
  let storageArrayHelpers :=
    if storageArrayHelpersRequired then
      [checkedStorageArrayElementHelperName]
    else
      []
  let dynamicBytesEqHelpers :=
    if dynamicBytesEqHelpersRequired then
      [dynamicBytesEqCalldataHelperName, dynamicBytesEqMemoryHelperName]
    else
      []
  let entrypoints := ["fallback", "receive"]
  (mappingHelpers ++ arrayHelpers ++ storageArrayHelpers ++ dynamicBytesEqHelpers ++ entrypoints).eraseDups

def firstReservedExternalCollision
    (spec : CompilationModel)
    (mappingHelpersRequired arrayHelpersRequired storageArrayHelpersRequired dynamicBytesEqHelpersRequired : Bool) : Option String :=
  (spec.externals.map (·.name)).find? (fun name =>
    name.startsWith internalFunctionPrefix ||
      (reservedExternalNames mappingHelpersRequired arrayHelpersRequired storageArrayHelpersRequired dynamicBytesEqHelpersRequired).contains name)

def firstInternalDynamicParam
    (fns : List FunctionSpec) : Option (String × String × ParamType) :=
  let rec goFns : List FunctionSpec → Option (String × String × ParamType)
    | [] => none
    | fn :: rest =>
        if !fn.isInternal then
          goFns rest
        else
          match fn.params.find? (fun p => isDynamicParamType p.ty) with
          | some p => some (fn.name, p.name, p.ty)
          | none => goFns rest
  goFns fns

def findInternalFunctionByName (functions : List FunctionSpec)
    (callerName calleeName : String) : Except String FunctionSpec := do
  let candidates := functions.filter (fun fn => fn.isInternal && fn.name == calleeName)
  match candidates with
  | [fn] => pure fn
  | [] =>
      throw s!"Compilation error: function '{callerName}' references unknown internal function '{calleeName}' ({issue625Ref})."
  | _ =>
      throw s!"Compilation error: function '{callerName}' references ambiguous internal function '{calleeName}' ({issue625Ref})."

mutual
def validateInternalCallShapesInExpr
    (functions : List FunctionSpec) (callerName : String) : Expr → Except String Unit
  | Expr.internalCall calleeName args => do
      validateInternalCallShapesInExprList functions callerName args
      let callee ← findInternalFunctionByName functions callerName calleeName
      if args.length != callee.params.length then
        throw s!"Compilation error: function '{callerName}' calls internal function '{calleeName}' with {args.length} args, expected {callee.params.length} ({issue625Ref})."
      let returns ← functionReturns callee
      if returns.length != 1 then
        throw s!"Compilation error: function '{callerName}' uses Expr.internalCall '{calleeName}' but callee returns {returns.length} values; use Stmt.internalCallAssign for multi-return calls ({issue625Ref})."
  | Expr.call gas target value inOffset inSize outOffset outSize => do
      validateInternalCallShapesInExpr functions callerName gas
      validateInternalCallShapesInExpr functions callerName target
      validateInternalCallShapesInExpr functions callerName value
      validateInternalCallShapesInExpr functions callerName inOffset
      validateInternalCallShapesInExpr functions callerName inSize
      validateInternalCallShapesInExpr functions callerName outOffset
      validateInternalCallShapesInExpr functions callerName outSize
  | Expr.staticcall gas target inOffset inSize outOffset outSize => do
      validateInternalCallShapesInExpr functions callerName gas
      validateInternalCallShapesInExpr functions callerName target
      validateInternalCallShapesInExpr functions callerName inOffset
      validateInternalCallShapesInExpr functions callerName inSize
      validateInternalCallShapesInExpr functions callerName outOffset
      validateInternalCallShapesInExpr functions callerName outSize
  | Expr.delegatecall gas target inOffset inSize outOffset outSize => do
      validateInternalCallShapesInExpr functions callerName gas
      validateInternalCallShapesInExpr functions callerName target
      validateInternalCallShapesInExpr functions callerName inOffset
      validateInternalCallShapesInExpr functions callerName inSize
      validateInternalCallShapesInExpr functions callerName outOffset
      validateInternalCallShapesInExpr functions callerName outSize
  | Expr.extcodesize addr =>
      validateInternalCallShapesInExpr functions callerName addr
  | Expr.mload offset | Expr.tload offset =>
      validateInternalCallShapesInExpr functions callerName offset
  | Expr.calldataload offset =>
      validateInternalCallShapesInExpr functions callerName offset
  | Expr.keccak256 offset size => do
      validateInternalCallShapesInExpr functions callerName offset
      validateInternalCallShapesInExpr functions callerName size
  | Expr.returndataOptionalBoolAt outOffset =>
      validateInternalCallShapesInExpr functions callerName outOffset
  | Expr.mapping _ key =>
      validateInternalCallShapesInExpr functions callerName key
  | Expr.mappingWord _ key _ =>
      validateInternalCallShapesInExpr functions callerName key
  | Expr.mappingPackedWord _ key _ _ =>
      validateInternalCallShapesInExpr functions callerName key
  | Expr.mappingChain _ keys =>
      validateInternalCallShapesInExprList functions callerName keys
  | Expr.structMember _ key _ =>
      validateInternalCallShapesInExpr functions callerName key
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ => do
      validateInternalCallShapesInExpr functions callerName key1
      validateInternalCallShapesInExpr functions callerName key2
  | Expr.mappingUint _ key =>
      validateInternalCallShapesInExpr functions callerName key
  | Expr.storageArrayElement _ index
  | Expr.arrayElement _ index =>
      validateInternalCallShapesInExpr functions callerName index
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.sdiv a b | Expr.mod a b | Expr.smod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.sar a b | Expr.signextend a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.sgt a b | Expr.lt a b | Expr.slt a b | Expr.le a b |
    Expr.logicalAnd a b | Expr.logicalOr a b |
    Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b => do
      validateInternalCallShapesInExpr functions callerName a
      validateInternalCallShapesInExpr functions callerName b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c => do
      validateInternalCallShapesInExpr functions callerName a
      validateInternalCallShapesInExpr functions callerName b
      validateInternalCallShapesInExpr functions callerName c
  | Expr.bitNot a | Expr.logicalNot a =>
      validateInternalCallShapesInExpr functions callerName a
  | Expr.ite cond thenVal elseVal => do
      validateInternalCallShapesInExpr functions callerName cond
      validateInternalCallShapesInExpr functions callerName thenVal
      validateInternalCallShapesInExpr functions callerName elseVal
  | _ =>
      pure ()
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

def validateInternalCallShapesInExprList
    (functions : List FunctionSpec) (callerName : String) : List Expr → Except String Unit
  | [] => pure ()
  | e :: es => do
      validateInternalCallShapesInExpr functions callerName e
      validateInternalCallShapesInExprList functions callerName es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

def validateInternalCallShapesInStmt
    (functions : List FunctionSpec) (callerName : String) : Stmt → Except String Unit
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value | Stmt.setStorageAddr _ value |
    Stmt.storageArrayPush _ value |
    Stmt.return value | Stmt.require value _ =>
      validateInternalCallShapesInExpr functions callerName value
  | Stmt.setStorageArrayElement _ index value => do
      validateInternalCallShapesInExpr functions callerName index
      validateInternalCallShapesInExpr functions callerName value
  | Stmt.storageArrayPop _ =>
      pure ()
  | Stmt.requireError cond _ args => do
      validateInternalCallShapesInExpr functions callerName cond
      validateInternalCallShapesInExprList functions callerName args
  | Stmt.revertError _ args =>
      validateInternalCallShapesInExprList functions callerName args
  | Stmt.mstore offset value => do
      validateInternalCallShapesInExpr functions callerName offset
      validateInternalCallShapesInExpr functions callerName value
  | Stmt.tstore offset value => do
      validateInternalCallShapesInExpr functions callerName offset
      validateInternalCallShapesInExpr functions callerName value
  | Stmt.calldatacopy destOffset sourceOffset size => do
      validateInternalCallShapesInExpr functions callerName destOffset
      validateInternalCallShapesInExpr functions callerName sourceOffset
      validateInternalCallShapesInExpr functions callerName size
  | Stmt.returndataCopy destOffset sourceOffset size => do
      validateInternalCallShapesInExpr functions callerName destOffset
      validateInternalCallShapesInExpr functions callerName sourceOffset
      validateInternalCallShapesInExpr functions callerName size
  | Stmt.revertReturndata =>
      pure ()
  | Stmt.setMapping _ key value | Stmt.setMappingWord _ key _ value | Stmt.setMappingPackedWord _ key _ _ value | Stmt.setMappingUint _ key value
  | Stmt.setStructMember _ key _ value => do
      validateInternalCallShapesInExpr functions callerName key
      validateInternalCallShapesInExpr functions callerName value
  | Stmt.setMappingChain _ keys value => do
      validateInternalCallShapesInExprList functions callerName keys
      validateInternalCallShapesInExpr functions callerName value
  | Stmt.setMapping2 _ key1 key2 value | Stmt.setMapping2Word _ key1 key2 _ value
  | Stmt.setStructMember2 _ key1 key2 _ value => do
      validateInternalCallShapesInExpr functions callerName key1
      validateInternalCallShapesInExpr functions callerName key2
      validateInternalCallShapesInExpr functions callerName value
  | Stmt.ite cond thenBranch elseBranch => do
      validateInternalCallShapesInExpr functions callerName cond
      validateInternalCallShapesInStmtList functions callerName thenBranch
      validateInternalCallShapesInStmtList functions callerName elseBranch
  | Stmt.forEach _ count body => do
      validateInternalCallShapesInExpr functions callerName count
      validateInternalCallShapesInStmtList functions callerName body
  | Stmt.emit _ args =>
      validateInternalCallShapesInExprList functions callerName args
  | Stmt.returnValues values =>
      validateInternalCallShapesInExprList functions callerName values
  | Stmt.internalCall calleeName args => do
      validateInternalCallShapesInExprList functions callerName args
      let callee ← findInternalFunctionByName functions callerName calleeName
      if args.length != callee.params.length then
        throw s!"Compilation error: function '{callerName}' calls internal function '{calleeName}' with {args.length} args, expected {callee.params.length} ({issue625Ref})."
      let returns ← functionReturns callee
      if !returns.isEmpty then
        throw s!"Compilation error: function '{callerName}' uses Stmt.internalCall '{calleeName}' but callee returns {returns.length} values; use Expr.internalCall for single-return or Stmt.internalCallAssign for multi-return calls ({issue625Ref})."
  | Stmt.internalCallAssign names calleeName args => do
      if names.isEmpty then
        throw s!"Compilation error: function '{callerName}' uses Stmt.internalCallAssign with no target variables ({issue625Ref})."
      let rec firstDuplicateTarget (seen : List String) : List String → Option String
        | [] => none
        | name :: rest =>
            if seen.contains name then
              some name
            else
              firstDuplicateTarget (name :: seen) rest
      match firstDuplicateTarget [] names with
      | some dup =>
          throw s!"Compilation error: function '{callerName}' uses Stmt.internalCallAssign with duplicate target '{dup}' ({issue625Ref})."
      | none =>
          pure ()
      validateInternalCallShapesInExprList functions callerName args
      let callee ← findInternalFunctionByName functions callerName calleeName
      if args.length != callee.params.length then
        throw s!"Compilation error: function '{callerName}' calls internal function '{calleeName}' with {args.length} args, expected {callee.params.length} ({issue625Ref})."
      let returns ← functionReturns callee
      if returns.length != names.length then
        throw s!"Compilation error: function '{callerName}' binds {names.length} values from internal function '{calleeName}', but callee returns {returns.length} ({issue625Ref})."
  | Stmt.rawLog topics dataOffset dataSize => do
      validateInternalCallShapesInExprList functions callerName topics
      validateInternalCallShapesInExpr functions callerName dataOffset
      validateInternalCallShapesInExpr functions callerName dataSize
  | Stmt.externalCallBind _resultVars _ args =>
      validateInternalCallShapesInExprList functions callerName args
  | Stmt.ecm _ args =>
      validateInternalCallShapesInExprList functions callerName args
  | _ =>
      pure ()
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def validateInternalCallShapesInStmtList
    (functions : List FunctionSpec) (callerName : String) : List Stmt → Except String Unit
  | [] => pure ()
  | s :: ss => do
      validateInternalCallShapesInStmt functions callerName s
      validateInternalCallShapesInStmtList functions callerName ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

def validateInternalCallShapesInFunction (functions : List FunctionSpec)
    (spec : FunctionSpec) : Except String Unit := do
  spec.body.forM (validateInternalCallShapesInStmt functions spec.name)

mutual
def validateExternalCallTargetsInExpr
    (externals : List ExternalFunction) (context : String) : Expr → Except String Unit
  | Expr.externalCall name args => do
      match externals.find? (fun ext => ext.name == name) with
      | none =>
          throw s!"Compilation error: {context} references unknown external call target '{name}' ({issue732Ref}). Declare it in spec.externals."
      | some ext =>
          if args.length != ext.params.length then
            throw s!"Compilation error: {context} calls external '{name}' with {args.length} args, but spec.externals declares {ext.params.length} ({issue184Ref})."
          let returns ← externalFunctionReturns ext
          if returns.length != 1 then
            throw s!"Compilation error: {context} uses Expr.externalCall '{name}' but spec.externals declares {returns.length} return values; Expr.externalCall requires exactly 1 ({issue184Ref})."
      validateExternalCallTargetsInExprList externals context args
  | Expr.call gas target value inOffset inSize outOffset outSize => do
      validateExternalCallTargetsInExpr externals context gas
      validateExternalCallTargetsInExpr externals context target
      validateExternalCallTargetsInExpr externals context value
      validateExternalCallTargetsInExpr externals context inOffset
      validateExternalCallTargetsInExpr externals context inSize
      validateExternalCallTargetsInExpr externals context outOffset
      validateExternalCallTargetsInExpr externals context outSize
  | Expr.staticcall gas target inOffset inSize outOffset outSize => do
      validateExternalCallTargetsInExpr externals context gas
      validateExternalCallTargetsInExpr externals context target
      validateExternalCallTargetsInExpr externals context inOffset
      validateExternalCallTargetsInExpr externals context inSize
      validateExternalCallTargetsInExpr externals context outOffset
      validateExternalCallTargetsInExpr externals context outSize
  | Expr.delegatecall gas target inOffset inSize outOffset outSize => do
      validateExternalCallTargetsInExpr externals context gas
      validateExternalCallTargetsInExpr externals context target
      validateExternalCallTargetsInExpr externals context inOffset
      validateExternalCallTargetsInExpr externals context inSize
      validateExternalCallTargetsInExpr externals context outOffset
      validateExternalCallTargetsInExpr externals context outSize
  | Expr.extcodesize addr =>
      validateExternalCallTargetsInExpr externals context addr
  | Expr.mload offset | Expr.tload offset =>
      validateExternalCallTargetsInExpr externals context offset
  | Expr.calldataload offset =>
      validateExternalCallTargetsInExpr externals context offset
  | Expr.keccak256 offset size => do
      validateExternalCallTargetsInExpr externals context offset
      validateExternalCallTargetsInExpr externals context size
  | Expr.returndataOptionalBoolAt outOffset =>
      validateExternalCallTargetsInExpr externals context outOffset
  | Expr.mapping _ key =>
      validateExternalCallTargetsInExpr externals context key
  | Expr.mappingWord _ key _ =>
      validateExternalCallTargetsInExpr externals context key
  | Expr.mappingPackedWord _ key _ _ =>
      validateExternalCallTargetsInExpr externals context key
  | Expr.mappingChain _ keys =>
      validateExternalCallTargetsInExprList externals context keys
  | Expr.structMember _ key _ =>
      validateExternalCallTargetsInExpr externals context key
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ => do
      validateExternalCallTargetsInExpr externals context key1
      validateExternalCallTargetsInExpr externals context key2
  | Expr.mappingUint _ key =>
      validateExternalCallTargetsInExpr externals context key
  | Expr.internalCall _ args =>
      validateExternalCallTargetsInExprList externals context args
  | Expr.storageArrayElement _ index
  | Expr.arrayElement _ index =>
      validateExternalCallTargetsInExpr externals context index
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.sdiv a b | Expr.mod a b | Expr.smod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.sar a b | Expr.signextend a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.sgt a b | Expr.lt a b | Expr.slt a b | Expr.le a b |
    Expr.logicalAnd a b | Expr.logicalOr a b |
    Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b => do
      validateExternalCallTargetsInExpr externals context a
      validateExternalCallTargetsInExpr externals context b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c => do
      validateExternalCallTargetsInExpr externals context a
      validateExternalCallTargetsInExpr externals context b
      validateExternalCallTargetsInExpr externals context c
  | Expr.bitNot a | Expr.logicalNot a =>
      validateExternalCallTargetsInExpr externals context a
  | Expr.ite cond thenVal elseVal => do
      validateExternalCallTargetsInExpr externals context cond
      validateExternalCallTargetsInExpr externals context thenVal
      validateExternalCallTargetsInExpr externals context elseVal
  | _ =>
      pure ()
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

def validateExternalCallTargetsInExprList
    (externals : List ExternalFunction) (context : String) : List Expr → Except String Unit
  | [] => pure ()
  | e :: es => do
      validateExternalCallTargetsInExpr externals context e
      validateExternalCallTargetsInExprList externals context es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

def validateExternalCallTargetsInStmt
    (externals : List ExternalFunction) (context : String) : Stmt → Except String Unit
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value | Stmt.setStorageAddr _ value |
    Stmt.storageArrayPush _ value |
    Stmt.return value | Stmt.require value _ =>
      validateExternalCallTargetsInExpr externals context value
  | Stmt.setStorageArrayElement _ index value => do
      validateExternalCallTargetsInExpr externals context index
      validateExternalCallTargetsInExpr externals context value
  | Stmt.storageArrayPop _ =>
      pure ()
  | Stmt.requireError cond _ args => do
      validateExternalCallTargetsInExpr externals context cond
      validateExternalCallTargetsInExprList externals context args
  | Stmt.revertError _ args =>
      validateExternalCallTargetsInExprList externals context args
  | Stmt.mstore offset value => do
      validateExternalCallTargetsInExpr externals context offset
      validateExternalCallTargetsInExpr externals context value
  | Stmt.tstore offset value => do
      validateExternalCallTargetsInExpr externals context offset
      validateExternalCallTargetsInExpr externals context value
  | Stmt.calldatacopy destOffset sourceOffset size => do
      validateExternalCallTargetsInExpr externals context destOffset
      validateExternalCallTargetsInExpr externals context sourceOffset
      validateExternalCallTargetsInExpr externals context size
  | Stmt.returndataCopy destOffset sourceOffset size => do
      validateExternalCallTargetsInExpr externals context destOffset
      validateExternalCallTargetsInExpr externals context sourceOffset
      validateExternalCallTargetsInExpr externals context size
  | Stmt.revertReturndata =>
      pure ()
  | Stmt.setMapping _ key value | Stmt.setMappingWord _ key _ value | Stmt.setMappingPackedWord _ key _ _ value | Stmt.setMappingUint _ key value
  | Stmt.setStructMember _ key _ value => do
      validateExternalCallTargetsInExpr externals context key
      validateExternalCallTargetsInExpr externals context value
  | Stmt.setMappingChain _ keys value => do
      validateExternalCallTargetsInExprList externals context keys
      validateExternalCallTargetsInExpr externals context value
  | Stmt.setMapping2 _ key1 key2 value | Stmt.setMapping2Word _ key1 key2 _ value
  | Stmt.setStructMember2 _ key1 key2 _ value => do
      validateExternalCallTargetsInExpr externals context key1
      validateExternalCallTargetsInExpr externals context key2
      validateExternalCallTargetsInExpr externals context value
  | Stmt.ite cond thenBranch elseBranch => do
      validateExternalCallTargetsInExpr externals context cond
      validateExternalCallTargetsInStmtList externals context thenBranch
      validateExternalCallTargetsInStmtList externals context elseBranch
  | Stmt.forEach _ count body => do
      validateExternalCallTargetsInExpr externals context count
      validateExternalCallTargetsInStmtList externals context body
  | Stmt.emit _ args =>
      validateExternalCallTargetsInExprList externals context args
  | Stmt.internalCall _ args =>
      validateExternalCallTargetsInExprList externals context args
  | Stmt.internalCallAssign _ _ args =>
      validateExternalCallTargetsInExprList externals context args
  | Stmt.externalCallBind resultVars externalName args => do
      validateExternalCallTargetsInExprList externals context args
      match externals.find? (fun ext => ext.name == externalName) with
      | none =>
          throw s!"Compilation error: {context} uses Stmt.externalCallBind with unknown external function '{externalName}'."
      | some ext => do
          if args.length != ext.params.length then
            throw s!"Compilation error: {context} calls external function '{externalName}' with {args.length} args, expected {ext.params.length}."
          let returns ← externalFunctionReturns ext
          if returns.length != resultVars.length then
            throw s!"Compilation error: {context} binds {resultVars.length} values from external function '{externalName}', but it returns {returns.length}."
          let rec checkDuplicateVars (seen : List String) : List String → Except String Unit
            | [] => pure ()
            | name :: rest =>
                if seen.contains name then
                  throw s!"Compilation error: {context} uses Stmt.externalCallBind with duplicate result variable '{name}'."
                else
                  checkDuplicateVars (name :: seen) rest
          checkDuplicateVars [] resultVars
  | Stmt.returnValues values =>
      validateExternalCallTargetsInExprList externals context values
  | Stmt.rawLog topics dataOffset dataSize => do
      validateExternalCallTargetsInExprList externals context topics
      validateExternalCallTargetsInExpr externals context dataOffset
      validateExternalCallTargetsInExpr externals context dataSize
  | Stmt.ecm _ args =>
      validateExternalCallTargetsInExprList externals context args
  | _ =>
      pure ()
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def validateExternalCallTargetsInStmtList
    (externals : List ExternalFunction) (context : String) : List Stmt → Except String Unit
  | [] => pure ()
  | s :: ss => do
      validateExternalCallTargetsInStmt externals context s
      validateExternalCallTargetsInStmtList externals context ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

def validateExternalCallTargetsInFunction
    (externals : List ExternalFunction) (spec : FunctionSpec) : Except String Unit := do
  spec.body.forM (validateExternalCallTargetsInStmt externals s!"function '{spec.name}'")

def validateExternalCallTargetsInConstructor
    (externals : List ExternalFunction) (ctor : Option ConstructorSpec) : Except String Unit := do
  match ctor with
  | none => pure ()
  | some spec =>
      spec.body.forM (validateExternalCallTargetsInStmt externals "constructor")

mutual
def supportedCustomErrorParamType : ParamType → Bool
  | ParamType.uint256 | ParamType.int256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 | ParamType.bytes | ParamType.string => true
  | ParamType.array elemTy => supportedCustomErrorParamType elemTy
  | ParamType.fixedArray elemTy _ => supportedCustomErrorParamType elemTy
  | ParamType.tuple elemTys => supportedCustomErrorParamTypes elemTys
termination_by ty => sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals omega

def supportedCustomErrorParamTypes : List ParamType → Bool
  | [] => true
  | ty :: tys => supportedCustomErrorParamType ty && supportedCustomErrorParamTypes tys
termination_by tys => sizeOf tys
decreasing_by
  all_goals simp_wf
  all_goals omega
end

def validateErrorDef (err : ErrorDef) : Except String Unit := do
  for ty in err.params do
    if !supportedCustomErrorParamType ty then
      throw s!"Compilation error: custom error '{err.name}' uses unsupported dynamic parameter type {repr ty} ({issue586Ref}). Use uint256/address/bool/bytes32/bytes/string parameters."

def validateEventDef (eventDef : EventDef) : Except String Unit := do
  let indexedCount := eventDef.params.foldl
    (fun acc p => if p.kind == EventParamKind.indexed then acc + 1 else acc)
    0
  if indexedCount > 3 then
    throw s!"Compilation error: event '{eventDef.name}' has {indexedCount} indexed params; max is 3"

def ensureContractIdentifier (kind name : String) : Except String Unit := do
  match Compiler.ensureValidIdentifier kind name with
  | .ok _ => pure ()
  | .error err => throw s!"Compilation error: {err}"

/-- Source identifiers that lower directly to Yul variables must avoid the
compiler-reserved `__` prefix used by dispatch and scratch temporaries. -/
private def ensureNonReservedYulIdentifier (kind name : String) : Except String Unit := do
  if name.startsWith "__" then
    throw s!"Compilation error: {kind} '{name}' uses reserved compiler prefix '__' ({issue756Ref}). Rename it."

def validateFunctionIdentifiers (fn : FunctionSpec) : Except String Unit := do
  ensureContractIdentifier "function" fn.name
  for p in fn.params do
    ensureContractIdentifier "function parameter" p.name
    ensureNonReservedYulIdentifier "function parameter" p.name
  for localName in collectStmtListBindNames fn.body do
    ensureContractIdentifier "local binder" localName
    ensureNonReservedYulIdentifier "local binder" localName

def validateConstructorIdentifiers (ctor : ConstructorSpec) : Except String Unit := do
  for p in ctor.params do
    ensureContractIdentifier "constructor parameter" p.name
    ensureNonReservedYulIdentifier "constructor parameter" p.name
  for localName in collectStmtListBindNames ctor.body do
    ensureContractIdentifier "local binder" localName
    ensureNonReservedYulIdentifier "local binder" localName

def validateIdentifierShapes (spec : CompilationModel) : Except String Unit := do
  ensureContractIdentifier "contract" spec.name
  for field in spec.fields do
    ensureContractIdentifier "field" field.name
    ensureNonReservedYulIdentifier "field" field.name
  for fn in spec.functions do
    validateFunctionIdentifiers fn
  match spec.constructor with
  | none => pure ()
  | some ctor =>
      validateConstructorIdentifiers ctor
  for eventDef in spec.events do
    ensureContractIdentifier "event" eventDef.name
    for p in eventDef.params do
      ensureContractIdentifier "event parameter" p.name
  for err in spec.errors do
    ensureContractIdentifier "custom error" err.name
  for ext in spec.externals do
    ensureContractIdentifier "external declaration" ext.name

end Compiler.CompilationModel
