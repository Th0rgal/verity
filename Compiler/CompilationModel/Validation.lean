/-
  Compiler.CompilationModel.Validation: Validation walkers and shape checks
-/
import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.AbiTypeLayout
import Compiler.CompilationModel.DynamicData
import Compiler.CompilationModel.EcmAxiomCollection
import Compiler.CompilationModel.EventAbiHelpers
import Compiler.CompilationModel.InternalNaming
import Compiler.CompilationModel.IssueRefs
import Compiler.CompilationModel.LayoutValidation
import Compiler.CompilationModel.MappingWrites
import Compiler.CompilationModel.UsageAnalysis
import Compiler.CompilationModel.ValidationHelpers
import Compiler.CompilationModel.SelectorInteropHelpers
import Compiler.CompilationModel.ExpressionCompile

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

def findParamType (params : List Param) (name : String) : Option ParamType :=
  (params.find? (fun p => p.name == name)).map (·.ty)

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
  -- Leaf expressions with no sub-expressions: exhaustive to trigger compiler
  -- errors when new variants are added.
  | Expr.literal _ | Expr.param _ | Expr.constructorArg _ | Expr.storage _
  | Expr.caller | Expr.contractAddress | Expr.chainid | Expr.msgValue | Expr.blockTimestamp
  | Expr.calldatasize | Expr.returndataSize | Expr.localVar _ | Expr.arrayLength _ =>
      false

def validateLogicalOperandPurity (context : String) (a b : Expr) : Except String Unit := do
  if exprContainsCallLike a || exprContainsCallLike b then
    throw s!"Compilation error: {context} uses Expr.logicalAnd/Expr.logicalOr with call-like operand(s), which are eagerly evaluated ({issue748Ref}). Move call-like expressions into Stmt.letVar/Stmt.ite before combining booleans."

/-- Validate that subexpressions duplicated by arithmetic helpers don't contain call-like expressions.
    mulDivUp/wDivUp/min/max inline subexpressions multiple times in the generated Yul,
    so call-like operands would be re-evaluated. -/
def validateArithDuplicatedOperandPurity (context : String) (duplicated : List Expr) : Except String Unit := do
  if duplicated.any exprContainsCallLike then
    throw s!"Compilation error: {context} uses an arithmetic helper (mulDivUp/wDivUp/min/max) with call-like operand(s) that would be duplicated in Yul output ({issue748Ref}). Move call-like expressions into Stmt.letVar before using them in arithmetic helpers."

mutual
def exprContainsUnsafeLogicalCallLike (expr : Expr) : Bool :=
  match expr with
  | Expr.logicalAnd a b | Expr.logicalOr a b =>
      (exprContainsCallLike a || exprContainsCallLike b) ||
      exprContainsUnsafeLogicalCallLike a || exprContainsUnsafeLogicalCallLike b
  -- Arithmetic ops that duplicate subexpressions in Yul output
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
      -- Both branches and cond are eagerly evaluated; cond is duplicated in Yul output
      (exprContainsCallLike cond || exprContainsCallLike thenVal || exprContainsCallLike elseVal) ||
      exprContainsUnsafeLogicalCallLike cond ||
      exprContainsUnsafeLogicalCallLike thenVal ||
      exprContainsUnsafeLogicalCallLike elseVal
  -- Leaf expressions: no sub-expressions to recurse into.
  | Expr.literal _ | Expr.param _ | Expr.constructorArg _ | Expr.storage _
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
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value |
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

partial def staticParamBindingNames (name : String) (ty : ParamType) : List String :=
  match ty with
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      [name]
  | ParamType.fixedArray elemTy n =>
      (List.range n).flatMap (fun i => staticParamBindingNames s!"{name}_{i}" elemTy)
  | ParamType.tuple elemTys =>
      let rec go (tys : List ParamType) (idx : Nat) : List String :=
        match tys with
        | [] => []
        | elemTy :: rest =>
            staticParamBindingNames s!"{name}_{idx}" elemTy ++ go rest (idx + 1)
      go elemTys 0
  | _ => []

def dynamicParamBindingNames (name : String) : List String :=
  [s!"{name}_offset", s!"{name}_length", s!"{name}_data_offset"]

mutual
def isDynamicParamTypeForScope : ParamType → Bool
  | ParamType.uint256 => false
  | ParamType.uint8 => false
  | ParamType.address => false
  | ParamType.bool => false
  | ParamType.bytes32 => false
  | ParamType.array _ => true
  | ParamType.bytes => true
  | ParamType.fixedArray elemTy _ => isDynamicParamTypeForScope elemTy
  | ParamType.tuple elemTys => paramTypeListAnyDynamicForScope elemTys
termination_by ty => sizeOf ty
decreasing_by all_goals simp_wf; all_goals omega

def paramTypeListAnyDynamicForScope : List ParamType → Bool
  | [] => false
  | ty :: rest => isDynamicParamTypeForScope ty || paramTypeListAnyDynamicForScope rest
termination_by tys => sizeOf tys
decreasing_by all_goals simp_wf; all_goals omega
end

def isScalarParamTypeForScope : ParamType → Bool
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 => true
  | _ => false

def paramBindingNames (param : Param) : List String :=
  let names :=
    if isDynamicParamTypeForScope param.ty then
      dynamicParamBindingNames param.name ++ [param.name]
    else
      match param.ty with
      | ParamType.fixedArray elemTy n =>
          let staticNames := staticParamBindingNames param.name param.ty
          if n == 0 then
            staticNames
          else if isScalarParamTypeForScope elemTy then
            -- Keep `<name>` in scope for backward-compatible scalar fixed-array aliasing.
            staticNames ++ [param.name]
          else
            staticNames
      | _ =>
          staticParamBindingNames param.name param.ty
  if names.contains param.name then names else names ++ [param.name]

def paramScopeNames (params : List Param) : List String :=
  params.flatMap paramBindingNames

def dynamicParamBases (params : List Param) : List String :=
  (params.filter (fun p => isDynamicParamTypeForScope p.ty)).map (·.name)

mutual
def validateScopedExprIdentifiers
    (context : String) (params : List Param) (paramScope : List String) (dynamicParams : List String)
    (localScope : List String) (constructorArgCount : Option Nat) : Expr → Except String Unit
  | Expr.param name =>
      if paramScope.contains name then
        pure ()
      else
        throw s!"Compilation error: {context} references unknown parameter '{name}'"
  | Expr.constructorArg idx =>
      match constructorArgCount with
      | some count =>
          if idx < count then
            pure ()
          else
            throw s!"Compilation error: constructor Expr.constructorArg {idx} is out of bounds for {count} constructor parameter(s)"
      | none =>
          throw s!"Compilation error: {context} uses Expr.constructorArg outside constructor scope"
  | Expr.localVar name =>
      if localScope.contains name then
        pure ()
      else
        throw s!"Compilation error: {context} references unknown local variable '{name}'"
  | Expr.arrayLength name =>
      match findParamType params name with
      | some (ParamType.array _) => pure ()
      | some ty =>
          throw s!"Compilation error: {context} Expr.arrayLength '{name}' requires array parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: {context} references unknown parameter '{name}' in Expr.arrayLength"
  | Expr.arrayElement name index => do
      match findParamType params name with
      | some (ParamType.array _) => pure ()
      | some ty =>
          throw s!"Compilation error: {context} Expr.arrayElement '{name}' requires array parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: {context} references unknown parameter '{name}' in Expr.arrayElement"
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount index
  | Expr.mapping _ key | Expr.mappingWord _ key _ | Expr.mappingPackedWord _ key _ _ | Expr.mappingUint _ key
  | Expr.structMember _ key _ =>
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount key
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount key1
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount key2
  | Expr.call gas target value inOffset inSize outOffset outSize => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount gas
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount target
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount value
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount inOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount inSize
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount outOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount outSize
  | Expr.staticcall gas target inOffset inSize outOffset outSize => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount gas
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount target
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount inOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount inSize
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount outOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount outSize
  | Expr.delegatecall gas target inOffset inSize outOffset outSize => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount gas
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount target
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount inOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount inSize
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount outOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount outSize
  | Expr.extcodesize addr =>
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount addr
  | Expr.mload offset =>
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount offset
  | Expr.calldataload offset =>
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount offset
  | Expr.keccak256 offset size => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount offset
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount size
  | Expr.returndataOptionalBoolAt outOffset =>
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount outOffset
  | Expr.externalCall _ args | Expr.internalCall _ args =>
      validateScopedExprIdentifiersList context params paramScope dynamicParams localScope constructorArgCount args
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.mod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.lt a b | Expr.le a b |
    Expr.wMulDown a b => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount b
  | Expr.wDivUp a b => do
      validateArithDuplicatedOperandPurity context [b]
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount b
  | Expr.min a b | Expr.max a b => do
      validateArithDuplicatedOperandPurity context [a, b]
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount b
  | Expr.mulDivDown a b c => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount b
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount c
  | Expr.mulDivUp a b c => do
      validateArithDuplicatedOperandPurity context [c]
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount b
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount c
  | Expr.logicalAnd a b | Expr.logicalOr a b => do
      validateLogicalOperandPurity context a b
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount b
  | Expr.bitNot a | Expr.logicalNot a =>
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount a
  | Expr.ite cond thenVal elseVal => do
      -- Expr.ite compiles to a branchless ternary that eagerly evaluates all 3 operands;
      -- cond is also duplicated.  Reject call-like sub-expressions to avoid the same
      -- eager-evaluation footgun as logicalAnd/logicalOr (Issue #748).
      if exprContainsCallLike cond || exprContainsCallLike thenVal || exprContainsCallLike elseVal then
        throw s!"Compilation error: {context} uses Expr.ite with call-like operand(s), which are eagerly evaluated ({issue748Ref}). Both branches execute regardless of the condition. Move call-like expressions into Stmt.letVar/Stmt.ite before using Expr.ite."
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount cond
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount thenVal
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount elseVal
  -- Leaf expressions: no identifiers to validate.
  | Expr.literal _ | Expr.storage _ | Expr.caller | Expr.contractAddress | Expr.chainid
  | Expr.msgValue | Expr.blockTimestamp | Expr.calldatasize | Expr.returndataSize =>
      pure ()
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

def validateScopedExprIdentifiersList
    (context : String) (params : List Param) (paramScope : List String) (dynamicParams : List String)
    (localScope : List String) (constructorArgCount : Option Nat) : List Expr → Except String Unit
  | [] => pure ()
  | e :: es => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount e
      validateScopedExprIdentifiersList context params paramScope dynamicParams localScope constructorArgCount es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

def validateScopedStmtIdentifiers
    (context : String) (params : List Param) (paramScope : List String) (dynamicParams : List String)
    (localScope : List String) (constructorArgCount : Option Nat) : Stmt → Except String (List String)
  | Stmt.letVar name value => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount value
      if paramScope.contains name then
        throw s!"Compilation error: {context} declares local variable '{name}' that shadows a parameter"
      if localScope.contains name then
        throw s!"Compilation error: {context} redeclares local variable '{name}' in the same scope"
      pure (name :: localScope)
  | Stmt.assignVar name value => do
      if !localScope.contains name then
        throw s!"Compilation error: {context} assigns to undeclared local variable '{name}'"
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount value
      pure localScope
  | Stmt.setStorage _ value | Stmt.return value | Stmt.require value _ => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount value
      pure localScope
  | Stmt.setMapping _ key value | Stmt.setMappingWord _ key _ value | Stmt.setMappingPackedWord _ key _ _ value | Stmt.setMappingUint _ key value
  | Stmt.setStructMember _ key _ value => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount key
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount value
      pure localScope
  | Stmt.setMapping2 _ key1 key2 value | Stmt.setMapping2Word _ key1 key2 _ value
  | Stmt.setStructMember2 _ key1 key2 _ value => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount key1
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount key2
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount value
      pure localScope
  | Stmt.requireError cond _ args => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount cond
      validateScopedExprIdentifiersList context params paramScope dynamicParams localScope constructorArgCount args
      pure localScope
  | Stmt.revertError _ args | Stmt.emit _ args | Stmt.returnValues args => do
      validateScopedExprIdentifiersList context params paramScope dynamicParams localScope constructorArgCount args
      pure localScope
  | Stmt.mstore offset value => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount offset
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount value
      pure localScope
  | Stmt.calldatacopy destOffset sourceOffset size => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount destOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount sourceOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount size
      pure localScope
  | Stmt.returndataCopy destOffset sourceOffset size => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount destOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount sourceOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount size
      pure localScope
  | Stmt.ite cond thenBranch elseBranch => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount cond
      let _ ← validateScopedStmtListIdentifiers context params paramScope dynamicParams localScope constructorArgCount thenBranch
      let _ ← validateScopedStmtListIdentifiers context params paramScope dynamicParams localScope constructorArgCount elseBranch
      pure localScope
  | Stmt.forEach varName count body => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount count
      let _ ← validateScopedStmtListIdentifiers context params paramScope dynamicParams (varName :: localScope) constructorArgCount body
      pure localScope
  | Stmt.internalCall _ args => do
      validateScopedExprIdentifiersList context params paramScope dynamicParams localScope constructorArgCount args
      pure localScope
  | Stmt.internalCallAssign names _ args => do
      validateScopedExprIdentifiersList context params paramScope dynamicParams localScope constructorArgCount args
      pure (names.reverse ++ localScope)
  | Stmt.rawLog topics dataOffset dataSize => do
      validateScopedExprIdentifiersList context params paramScope dynamicParams localScope constructorArgCount topics
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount dataOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount dataSize
      pure localScope
  | Stmt.externalCallBind resultVars _ args => do
      validateScopedExprIdentifiersList context params paramScope dynamicParams localScope constructorArgCount args
      pure (resultVars.reverse ++ localScope)
  | Stmt.ecm mod args => do
      if args.length != mod.numArgs then
        throw s!"Compilation error: {context} uses ECM '{mod.name}' with {args.length} arguments but it expects {mod.numArgs}"
      validateScopedExprIdentifiersList context params paramScope dynamicParams localScope constructorArgCount args
      let mut scope := localScope
      for rv in mod.resultVars do
        if paramScope.contains rv then
          throw s!"Compilation error: {context} ECM '{mod.name}' result '{rv}' shadows a parameter"
        if scope.contains rv then
          throw s!"Compilation error: {context} ECM '{mod.name}' redeclares result '{rv}' in the same scope"
        scope := rv :: scope
      pure scope
  -- Leaf statements: no sub-expressions with identifiers to validate, no scope changes.
  | Stmt.returnArray _ | Stmt.returnBytes _ | Stmt.returnStorageWords _
  | Stmt.revertReturndata | Stmt.stop =>
      pure localScope
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def validateScopedStmtListIdentifiers
    (context : String) (params : List Param) (paramScope : List String) (dynamicParams : List String)
    (localScope : List String) (constructorArgCount : Option Nat) : List Stmt → Except String (List String)
  | [] => pure localScope
  | stmt :: rest => do
      let nextScope ← validateScopedStmtIdentifiers context params paramScope dynamicParams localScope constructorArgCount stmt
      validateScopedStmtListIdentifiers context params paramScope dynamicParams nextScope constructorArgCount rest
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

def validateFunctionIdentifierReferences (spec : FunctionSpec) : Except String Unit := do
  let _ ← validateScopedStmtListIdentifiers
    s!"function '{spec.name}'"
    spec.params
    (paramScopeNames spec.params)
    (dynamicParamBases spec.params)
    []
    none
    spec.body
  pure ()

def validateConstructorIdentifierReferences (ctor : Option ConstructorSpec) : Except String Unit := do
  match ctor with
  | none => pure ()
  | some spec =>
      let _ ← validateScopedStmtListIdentifiers
        "constructor"
        spec.params
        (paramScopeNames spec.params)
        (dynamicParamBases spec.params)
        []
        (some spec.params.length)
        spec.body
      pure ()

def isStorageWordArrayParam : ParamType → Bool
  | ParamType.array ParamType.bytes32 => true
  | ParamType.array ParamType.uint256 => true
  | _ => false

mutual
def validateStmtParamReferences (fnName : String) (params : List Param) :
    Stmt → Except String Unit
  | Stmt.returnArray name =>
      match findParamType params name with
      | some (ParamType.array _) =>
          pure ()
      | some ty =>
          throw s!"Compilation error: function '{fnName}' returnArray '{name}' requires array parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: function '{fnName}' returnArray references unknown parameter '{name}'"
  | Stmt.returnBytes name =>
      match findParamType params name with
      | some ParamType.bytes => pure ()
      | some ty =>
          throw s!"Compilation error: function '{fnName}' returnBytes '{name}' requires bytes parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: function '{fnName}' returnBytes references unknown parameter '{name}'"
  | Stmt.returnStorageWords name =>
      match findParamType params name with
      | some ty =>
          if isStorageWordArrayParam ty then
            pure ()
          else
            throw s!"Compilation error: function '{fnName}' returnStorageWords '{name}' requires bytes32[] or uint256[] parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: function '{fnName}' returnStorageWords references unknown parameter '{name}'"
  | Stmt.ite _ thenBranch elseBranch => do
      validateStmtParamReferencesInList fnName params thenBranch
      validateStmtParamReferencesInList fnName params elseBranch
  | Stmt.forEach _ _ body => do
      validateStmtParamReferencesInList fnName params body
  | _ => pure ()
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def validateStmtParamReferencesInList (fnName : String) (params : List Param) :
    List Stmt → Except String Unit
  | [] => pure ()
  | s :: ss => do
      validateStmtParamReferences fnName params s
      validateStmtParamReferencesInList fnName params ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
def validateReturnShapesInStmt (fnName : String)
    (expectedReturns : List ParamType) (isInternal : Bool) : Stmt → Except String Unit
  | Stmt.return _ =>
      if isInternal then
        match expectedReturns with
        | [_] => pure ()
        | [] =>
            throw s!"Compilation error: function '{fnName}' uses Stmt.return but declares no return values"
        | _ =>
            throw s!"Compilation error: function '{fnName}' uses Stmt.return but declares multiple return values; use Stmt.returnValues"
      else if expectedReturns.length > 1 then
        throw s!"Compilation error: function '{fnName}' uses Stmt.return but declares multiple return values; use Stmt.returnValues"
      else
        pure ()
  | Stmt.returnValues values =>
      if expectedReturns.isEmpty then
        throw s!"Compilation error: function '{fnName}' uses Stmt.returnValues but declares no return values"
      else if values.length != expectedReturns.length then
        throw s!"Compilation error: function '{fnName}' returnValues count mismatch: expected {expectedReturns.length}, got {values.length}"
      else
        pure ()
  | Stmt.returnArray _ =>
      if isInternal then
        throw s!"Compilation error: internal function '{fnName}' cannot use Stmt.returnArray; only static returns via Stmt.return/Stmt.returnValues are supported ({issue625Ref})."
      else if expectedReturns == [ParamType.array ParamType.uint256] then
        pure ()
      else
        throw s!"Compilation error: function '{fnName}' uses Stmt.returnArray but declared returns are {repr expectedReturns}"
  | Stmt.returnBytes _ =>
      if isInternal then
        throw s!"Compilation error: internal function '{fnName}' cannot use Stmt.returnBytes; only static returns via Stmt.return/Stmt.returnValues are supported ({issue625Ref})."
      else if expectedReturns == [ParamType.bytes] then
        pure ()
      else
        throw s!"Compilation error: function '{fnName}' uses Stmt.returnBytes but declared returns are {repr expectedReturns}"
  | Stmt.returnStorageWords _ =>
      if isInternal then
        throw s!"Compilation error: internal function '{fnName}' cannot use Stmt.returnStorageWords; only static returns via Stmt.return/Stmt.returnValues are supported ({issue625Ref})."
      else if expectedReturns == [ParamType.array ParamType.uint256] then
        pure ()
      else
        throw s!"Compilation error: function '{fnName}' uses Stmt.returnStorageWords but declared returns are {repr expectedReturns}"
  | Stmt.ite _ thenBranch elseBranch => do
      validateReturnShapesInStmtList fnName expectedReturns isInternal thenBranch
      validateReturnShapesInStmtList fnName expectedReturns isInternal elseBranch
  | Stmt.forEach _ _ body =>
      validateReturnShapesInStmtList fnName expectedReturns isInternal body
  | _ => pure ()
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def validateReturnShapesInStmtList (fnName : String)
    (expectedReturns : List ParamType) (isInternal : Bool) : List Stmt → Except String Unit
  | [] => pure ()
  | s :: ss => do
      validateReturnShapesInStmt fnName expectedReturns isInternal s
      validateReturnShapesInStmtList fnName expectedReturns isInternal ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
  private def stmtListAlwaysReturnsOrReverts : List Stmt → Bool
    | [] => false
    | stmt :: rest =>
        if stmtAlwaysReturnsOrReverts stmt then
          true
        else
          stmtListAlwaysReturnsOrReverts rest
  termination_by ss => sizeOf ss
  decreasing_by all_goals simp_wf; all_goals omega

  private def stmtAlwaysReturnsOrReverts : Stmt → Bool
    | Stmt.return _ | Stmt.returnValues _ | Stmt.returnArray _
    | Stmt.returnBytes _ | Stmt.returnStorageWords _
    | Stmt.revertError _ _ | Stmt.revertReturndata =>
        true
    | Stmt.ite _ thenBranch elseBranch =>
        stmtListAlwaysReturnsOrReverts thenBranch && stmtListAlwaysReturnsOrReverts elseBranch
    | _ =>
        false
  termination_by s => sizeOf s
  decreasing_by all_goals simp_wf; all_goals omega
end

def exprReadsStateOrEnv : Expr → Bool
  | Expr.literal _ => false
  | Expr.param _ => false
  | Expr.constructorArg _ => false
  | Expr.storage _ => true
  | Expr.mapping _ _ | Expr.mappingWord _ _ _ | Expr.mappingPackedWord _ _ _ _
  | Expr.mapping2 _ _ _ | Expr.mapping2Word _ _ _ _
  | Expr.mappingUint _ _
  | Expr.structMember _ _ _ | Expr.structMember2 _ _ _ _ => true
  | Expr.caller => true
  | Expr.contractAddress => true
  | Expr.chainid => true
  | Expr.extcodesize _ => true
  | Expr.msgValue => true
  | Expr.blockTimestamp => true
  | Expr.calldatasize => true
  | Expr.calldataload _ => true
  | Expr.mload offset => exprReadsStateOrEnv offset
  | Expr.keccak256 offset size => exprReadsStateOrEnv offset || exprReadsStateOrEnv size
  | Expr.call _ _ _ _ _ _ _ | Expr.staticcall _ _ _ _ _ _
  | Expr.delegatecall _ _ _ _ _ _ => true
  | Expr.returndataSize => true
  | Expr.returndataOptionalBoolAt _ => true
  | Expr.localVar _ => false
  | Expr.externalCall _ _ | Expr.internalCall _ _ => true
  | Expr.arrayLength _ => false
  | Expr.arrayElement _ index => exprReadsStateOrEnv index
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.mod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.lt a b | Expr.le a b |
    Expr.logicalAnd a b | Expr.logicalOr a b |
    Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b =>
      exprReadsStateOrEnv a || exprReadsStateOrEnv b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c =>
      exprReadsStateOrEnv a || exprReadsStateOrEnv b || exprReadsStateOrEnv c
  | Expr.bitNot a | Expr.logicalNot a =>
      exprReadsStateOrEnv a
  | Expr.ite cond thenVal elseVal =>
      exprReadsStateOrEnv cond || exprReadsStateOrEnv thenVal || exprReadsStateOrEnv elseVal

mutual
def exprWritesState : Expr → Bool
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.mod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.lt a b | Expr.le a b |
    Expr.logicalAnd a b | Expr.logicalOr a b |
    Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b =>
      exprWritesState a || exprWritesState b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c =>
      exprWritesState a || exprWritesState b || exprWritesState c
  | Expr.bitNot a | Expr.logicalNot a =>
      exprWritesState a
  | Expr.ite cond thenVal elseVal =>
      exprWritesState cond || exprWritesState thenVal || exprWritesState elseVal
  | Expr.mapping _ key | Expr.mappingWord _ key _ | Expr.mappingPackedWord _ key _ _ | Expr.mappingUint _ key
  | Expr.structMember _ key _ =>
      exprWritesState key
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ =>
      exprWritesState key1 || exprWritesState key2
  | Expr.call _ _ _ _ _ _ _ => true
  | Expr.staticcall gas target inOffset inSize outOffset outSize =>
      exprWritesState gas || exprWritesState target ||
      exprWritesState inOffset || exprWritesState inSize ||
      exprWritesState outOffset || exprWritesState outSize
  | Expr.delegatecall _ _ _ _ _ _ => true
  | Expr.mload offset =>
      exprWritesState offset
  | Expr.calldataload offset =>
      exprWritesState offset
  | Expr.keccak256 offset size =>
      exprWritesState offset || exprWritesState size
  | Expr.returndataOptionalBoolAt outOffset =>
      exprWritesState outOffset
  | Expr.externalCall _ _ | Expr.internalCall _ _ => true
  | Expr.extcodesize addr =>
      exprWritesState addr
  | Expr.arrayElement _ index =>
      exprWritesState index
  | _ =>
      false
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

def exprListWritesState : List Expr → Bool
  | [] => false
  | e :: es => exprWritesState e || exprListWritesState es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

def stmtWritesState : Stmt → Bool
  | Stmt.letVar _ value | Stmt.assignVar _ value =>
      exprWritesState value
  | Stmt.setStorage _ _
  | Stmt.setMapping _ _ _ | Stmt.setMappingWord _ _ _ _ | Stmt.setMappingPackedWord _ _ _ _ _ | Stmt.setMappingUint _ _ _
  | Stmt.setMapping2 _ _ _ _ | Stmt.setMapping2Word _ _ _ _ _
  | Stmt.setStructMember _ _ _ _ | Stmt.setStructMember2 _ _ _ _ _ => true
  | Stmt.require cond _ =>
      exprWritesState cond
  | Stmt.requireError cond _ args =>
      exprWritesState cond || exprListWritesState args
  | Stmt.revertError _ args =>
      exprListWritesState args
  | Stmt.return value =>
      exprWritesState value
  | Stmt.returnValues values =>
      exprListWritesState values
  | Stmt.returnArray _ =>
      false
  | Stmt.returnBytes _ =>
      false
  | Stmt.returnStorageWords _ =>
      false
  | Stmt.mstore offset value =>
      exprWritesState offset || exprWritesState value
  | Stmt.calldatacopy destOffset sourceOffset size =>
      exprWritesState destOffset || exprWritesState sourceOffset || exprWritesState size
  | Stmt.returndataCopy destOffset sourceOffset size =>
      exprWritesState destOffset || exprWritesState sourceOffset || exprWritesState size
  | Stmt.revertReturndata =>
      false
  | Stmt.stop =>
      false
  | Stmt.ite cond thenBranch elseBranch =>
      exprWritesState cond || stmtListWritesState thenBranch || stmtListWritesState elseBranch
  | Stmt.forEach _ count body =>
      exprWritesState count || stmtListWritesState body
  | Stmt.emit _ _ | Stmt.rawLog _ _ _
  | Stmt.internalCall _ _ | Stmt.internalCallAssign _ _ _
  | Stmt.externalCallBind _ _ _ => true
  | Stmt.ecm mod args =>
      mod.writesState || exprListWritesState args
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def stmtListWritesState : List Stmt → Bool
  | [] => false
  | s :: ss => stmtWritesState s || stmtListWritesState ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
def stmtReadsStateOrEnv : Stmt → Bool
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value |
    Stmt.return value | Stmt.require value _ =>
      exprReadsStateOrEnv value
  | Stmt.requireError cond _ args =>
      exprReadsStateOrEnv cond || args.any exprReadsStateOrEnv
  | Stmt.revertError _ args | Stmt.emit _ args | Stmt.returnValues args =>
      args.any exprReadsStateOrEnv
  | Stmt.returnArray _ | Stmt.returnBytes _ =>
      false
  | Stmt.returnStorageWords _ =>
      true
  | Stmt.mstore offset value =>
      exprReadsStateOrEnv offset || exprReadsStateOrEnv value
  | Stmt.calldatacopy _ _ _ | Stmt.returndataCopy _ _ _ => true
  | Stmt.revertReturndata =>
      true
  | Stmt.stop =>
      false
  | Stmt.setMapping _ _ _ | Stmt.setMappingWord _ _ _ _ | Stmt.setMappingPackedWord _ _ _ _ _ | Stmt.setMappingUint _ _ _
  | Stmt.setMapping2 _ _ _ _ | Stmt.setMapping2Word _ _ _ _ _
  | Stmt.setStructMember _ _ _ _ | Stmt.setStructMember2 _ _ _ _ _ => true
  | Stmt.ite cond thenBranch elseBranch =>
      exprReadsStateOrEnv cond || stmtListReadsStateOrEnv thenBranch || stmtListReadsStateOrEnv elseBranch
  | Stmt.forEach _ count body =>
      exprReadsStateOrEnv count || stmtListReadsStateOrEnv body
  | Stmt.rawLog topics dataOffset dataSize =>
      topics.any exprReadsStateOrEnv || exprReadsStateOrEnv dataOffset || exprReadsStateOrEnv dataSize
  | Stmt.internalCall _ _ | Stmt.internalCallAssign _ _ _
  | Stmt.externalCallBind _ _ _ => true
  | Stmt.ecm mod args => mod.readsState || mod.writesState || args.any exprReadsStateOrEnv
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def stmtListReadsStateOrEnv : List Stmt → Bool
  | [] => false
  | s :: ss => stmtReadsStateOrEnv s || stmtListReadsStateOrEnv ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

def validateFunctionSpec (spec : FunctionSpec) : Except String Unit := do
  if spec.isPayable && (spec.isView || spec.isPure) then
    throw s!"Compilation error: function '{spec.name}' cannot be both payable and view/pure ({issue586Ref})"
  if spec.isView && spec.isPure then
    throw s!"Compilation error: function '{spec.name}' cannot be both view and pure; use exactly one mutability marker ({issue586Ref})"
  if spec.isView && spec.body.any stmtWritesState then
    throw s!"Compilation error: function '{spec.name}' is marked view but writes state ({issue734Ref})"
  if spec.isPure && spec.body.any stmtWritesState then
    throw s!"Compilation error: function '{spec.name}' is marked pure but writes state ({issue734Ref})"
  if spec.isPure && spec.body.any stmtReadsStateOrEnv then
    throw s!"Compilation error: function '{spec.name}' is marked pure but reads state/environment ({issue734Ref})"
  if spec.body.any stmtContainsUnsafeLogicalCallLike then
    throw s!"Compilation error: function '{spec.name}' uses Expr.logicalAnd/Expr.logicalOr/Expr.ite or arithmetic helpers (mulDivUp/wDivUp/min/max) with call-like operand(s) that would be duplicated in Yul output ({issue748Ref}). Move call-like expressions into Stmt.letVar before combining."
  let returns ← functionReturns spec
  spec.body.forM (validateReturnShapesInStmt spec.name returns spec.isInternal)
  if !returns.isEmpty && !stmtListAlwaysReturnsOrReverts spec.body then
    throw s!"Compilation error: function '{spec.name}' declares return values but not all control-flow paths end in return/revert ({issue738Ref})"
  spec.body.forM (validateStmtParamReferences spec.name spec.params)
  validateFunctionIdentifierReferences spec

mutual
def validateNoRuntimeReturnsInConstructorStmt : Stmt → Except String Unit
  | Stmt.return _ | Stmt.returnValues _ | Stmt.returnArray _
  | Stmt.returnBytes _ | Stmt.returnStorageWords _ =>
      throw "Compilation error: constructor must not return runtime data directly"
  | Stmt.ite _ thenBranch elseBranch => do
      validateNoRuntimeReturnsInConstructorStmtList thenBranch
      validateNoRuntimeReturnsInConstructorStmtList elseBranch
  | Stmt.forEach _ _ body =>
      validateNoRuntimeReturnsInConstructorStmtList body
  | _ => pure ()
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def validateNoRuntimeReturnsInConstructorStmtList : List Stmt → Except String Unit
  | [] => pure ()
  | s :: ss => do
      validateNoRuntimeReturnsInConstructorStmt s
      validateNoRuntimeReturnsInConstructorStmtList ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

def validateConstructorSpec (ctor : Option ConstructorSpec) : Except String Unit := do
  match ctor with
  | none => pure ()
  | some spec =>
      if spec.body.any stmtContainsUnsafeLogicalCallLike then
        throw s!"Compilation error: constructor uses Expr.logicalAnd/Expr.logicalOr/Expr.ite or arithmetic helpers (mulDivUp/wDivUp/min/max) with call-like operand(s) that would be duplicated in Yul output ({issue748Ref}). Move call-like expressions into Stmt.letVar before combining."
      spec.body.forM validateNoRuntimeReturnsInConstructorStmt
      spec.body.forM (validateStmtParamReferences "constructor" spec.params)
      validateConstructorIdentifierReferences ctor

def customErrorRequiresDirectParamRef : ParamType → Bool
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 => false
  | _ => true

def validateDirectParamCustomErrorArg
    (fnName errorName : String) (params : List Param)
    (expectedTy : ParamType) (arg : Expr) : Except String Unit := do
  match arg with
  | Expr.param name =>
      match findParamType params name with
      | some ty =>
          if ty != expectedTy then
            throw s!"Compilation error: function '{fnName}' custom error '{errorName}' expects {repr expectedTy} arg to reference a matching parameter, got parameter '{name}' of type {repr ty} ({issue586Ref})."
      | none =>
          throw s!"Compilation error: function '{fnName}' custom error '{errorName}' references unknown parameter '{name}' ({issue586Ref})."
  | _ =>
      throw s!"Compilation error: function '{fnName}' custom error '{errorName}' parameter of type {repr expectedTy} currently requires direct parameter reference ({issue586Ref})."

mutual
def validateCustomErrorArgShapesInStmt (fnName : String) (params : List Param)
    (errors : List ErrorDef) : Stmt → Except String Unit
  | Stmt.requireError _ errorName args | Stmt.revertError errorName args => do
      let errorDef ←
        match errors.find? (·.name == errorName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown custom error '{errorName}' ({issue586Ref})"
      if errorDef.params.length != args.length then
        throw s!"Compilation error: custom error '{errorName}' expects {errorDef.params.length} args, got {args.length}"
      for (ty, arg) in errorDef.params.zip args do
        if customErrorRequiresDirectParamRef ty then
          validateDirectParamCustomErrorArg fnName errorName params ty arg
  | Stmt.ite _ thenBranch elseBranch => do
      validateCustomErrorArgShapesInStmtList fnName params errors thenBranch
      validateCustomErrorArgShapesInStmtList fnName params errors elseBranch
  | Stmt.forEach _ _ body =>
      validateCustomErrorArgShapesInStmtList fnName params errors body
  | _ => pure ()
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def validateCustomErrorArgShapesInStmtList (fnName : String) (params : List Param)
    (errors : List ErrorDef) : List Stmt → Except String Unit
  | [] => pure ()
  | s :: ss => do
      validateCustomErrorArgShapesInStmt fnName params errors s
      validateCustomErrorArgShapesInStmtList fnName params errors ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

def validateCustomErrorArgShapesInFunction (spec : FunctionSpec) (errors : List ErrorDef) :
    Except String Unit := do
  spec.body.forM (validateCustomErrorArgShapesInStmt spec.name spec.params errors)

partial def validateEventArgShapesInStmt (fnName : String) (params : List Param)
    (events : List EventDef) : Stmt → Except String Unit
  | Stmt.emit eventName args => do
      let eventDef ←
        match events.find? (·.name == eventName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown event '{eventName}'"
      if eventDef.params.length != args.length then
        throw s!"Compilation error: event '{eventName}' expects {eventDef.params.length} args, got {args.length}"
      for (eventParam, arg) in eventDef.params.zip args do
        match arg with
        | Expr.param name =>
            match findParamType params name with
            | some ty =>
                if ty != eventParam.ty then
                  throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
            | none =>
                throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
        | _ => pure ()
        if eventParam.kind == EventParamKind.unindexed then
          match eventParam.ty with
          | ParamType.array elemTy =>
              if elemTy == ParamType.bytes then
                  match arg with
                  | Expr.param name =>
                      match findParamType params name with
                      | some ty =>
                          if ty != eventParam.ty then
                            throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                      | none =>
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                  | _ =>
                      throw s!"Compilation error: function '{fnName}' unindexed dynamic array event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
              else if indexedDynamicArrayElemSupported elemTy then
                match arg with
                | Expr.param name =>
                    match findParamType params name with
                    | some ty =>
                        if ty != eventParam.ty then
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                    | none =>
                        throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                | _ =>
                    throw s!"Compilation error: function '{fnName}' unindexed dynamic array event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
              else if eventIsDynamicType elemTy then
                match arg with
                | Expr.param name =>
                    match findParamType params name with
                    | some ty =>
                        if ty != eventParam.ty then
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                    | none =>
                        throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                | _ =>
                    throw s!"Compilation error: function '{fnName}' unindexed dynamic array event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
              else
                throw s!"Compilation error: function '{fnName}' event '{eventName}' unindexed array param '{eventParam.name}' has unsupported element type {repr elemTy} ({issue586Ref})."
          | ParamType.fixedArray _ _ | ParamType.tuple _ =>
                match arg with
                | Expr.param name =>
                    match findParamType params name with
                    | some ty =>
                        if ty != eventParam.ty then
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                    | none =>
                        throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                | _ =>
                    throw s!"Compilation error: function '{fnName}' unindexed composite event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
          | ParamType.bytes =>
              match arg with
              | Expr.param name =>
                  match findParamType params name with
                  | some ParamType.bytes => pure ()
                  | some ty =>
                      throw s!"Compilation error: function '{fnName}' unindexed bytes event param '{eventParam.name}' in event '{eventName}' expects bytes arg to reference a bytes parameter, got {repr ty} ({issue586Ref})."
                  | none =>
                      throw s!"Compilation error: function '{fnName}' unindexed bytes event param '{eventParam.name}' in event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
              | _ =>
                  throw s!"Compilation error: function '{fnName}' unindexed bytes event param '{eventParam.name}' in event '{eventName}' currently requires direct bytes parameter reference ({issue586Ref})."
          | _ => pure ()
        if eventParam.kind == EventParamKind.indexed then
          match eventParam.ty with
          | ParamType.bytes =>
              match arg with
              | Expr.param name =>
                  match findParamType params name with
                  | some ParamType.bytes => pure ()
                  | some ty =>
                      throw s!"Compilation error: function '{fnName}' indexed bytes event param '{eventParam.name}' in event '{eventName}' expects bytes arg to reference a bytes parameter, got {repr ty} ({issue586Ref})."
                  | none =>
                      throw s!"Compilation error: function '{fnName}' indexed bytes event param '{eventParam.name}' in event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
              | _ =>
                  throw s!"Compilation error: function '{fnName}' indexed bytes event param '{eventParam.name}' in event '{eventName}' currently requires direct bytes parameter reference ({issue586Ref})."
          | ParamType.array elemTy =>
              match elemTy with
              | ParamType.bytes =>
                  match arg with
                  | Expr.param name =>
                      match findParamType params name with
                      | some ty =>
                          if ty != eventParam.ty then
                            throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                      | none =>
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                  | _ =>
                      throw s!"Compilation error: function '{fnName}' indexed dynamic array event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
              | _ =>
                  match arg with
                  | Expr.param name =>
                      match findParamType params name with
                      | some ty =>
                          if ty != eventParam.ty then
                            throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                      | none =>
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                  | _ =>
                      throw s!"Compilation error: function '{fnName}' indexed dynamic array event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
          | ParamType.fixedArray _ _ | ParamType.tuple _ =>
              match arg with
              | Expr.param name =>
                  match findParamType params name with
                  | some ty =>
                      if ty != eventParam.ty then
                        throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                  | none =>
                      throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
              | _ =>
                  throw s!"Compilation error: function '{fnName}' indexed composite event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
          | _ => pure ()
  | Stmt.ite _ thenBranch elseBranch => do
      thenBranch.forM (validateEventArgShapesInStmt fnName params events)
      elseBranch.forM (validateEventArgShapesInStmt fnName params events)
  | Stmt.forEach _ _ body =>
      body.forM (validateEventArgShapesInStmt fnName params events)
  | _ => pure ()

def validateEventArgShapesInFunction (spec : FunctionSpec) (events : List EventDef) :
    Except String Unit := do
  spec.body.forM (validateEventArgShapesInStmt spec.name spec.params events)

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
  | Expr.contractAddress | Expr.chainid =>
      pure ()
  | Expr.extcodesize addr =>
      validateInteropExpr context addr
  | Expr.calldatasize =>
      pure ()
  | Expr.calldataload offset =>
      validateInteropExpr context offset
  | Expr.mload offset =>
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
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.mod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.lt a b | Expr.le a b |
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
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value |
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

def reservedExternalNames (mappingHelpersRequired arrayHelpersRequired : Bool) : List String :=
  let mappingHelpers := if mappingHelpersRequired then ["mappingSlot"] else []
  let arrayHelpers :=
    if arrayHelpersRequired then
      [checkedArrayElementCalldataHelperName, checkedArrayElementMemoryHelperName]
    else
      []
  let entrypoints := ["fallback", "receive"]
  (mappingHelpers ++ arrayHelpers ++ entrypoints).eraseDups

def firstReservedExternalCollision
    (spec : CompilationModel) (mappingHelpersRequired arrayHelpersRequired : Bool) : Option String :=
  (spec.externals.map (·.name)).find? (fun name =>
    name.startsWith internalFunctionPrefix ||
      (reservedExternalNames mappingHelpersRequired arrayHelpersRequired).contains name)

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
  | Expr.mload offset =>
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
  | Expr.structMember _ key _ =>
      validateInternalCallShapesInExpr functions callerName key
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ => do
      validateInternalCallShapesInExpr functions callerName key1
      validateInternalCallShapesInExpr functions callerName key2
  | Expr.mappingUint _ key =>
      validateInternalCallShapesInExpr functions callerName key
  | Expr.arrayElement _ index =>
      validateInternalCallShapesInExpr functions callerName index
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.mod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.lt a b | Expr.le a b |
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
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value |
    Stmt.return value | Stmt.require value _ =>
      validateInternalCallShapesInExpr functions callerName value
  | Stmt.requireError cond _ args => do
      validateInternalCallShapesInExpr functions callerName cond
      validateInternalCallShapesInExprList functions callerName args
  | Stmt.revertError _ args =>
      validateInternalCallShapesInExprList functions callerName args
  | Stmt.mstore offset value => do
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
  | Expr.mload offset =>
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
  | Expr.arrayElement _ index =>
      validateExternalCallTargetsInExpr externals context index
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.mod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.lt a b | Expr.le a b |
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
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value |
    Stmt.return value | Stmt.require value _ =>
      validateExternalCallTargetsInExpr externals context value
  | Stmt.requireError cond _ args => do
      validateExternalCallTargetsInExpr externals context cond
      validateExternalCallTargetsInExprList externals context args
  | Stmt.revertError _ args =>
      validateExternalCallTargetsInExprList externals context args
  | Stmt.mstore offset value => do
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
          if resultVars.isEmpty then
            throw s!"Compilation error: {context} uses Stmt.externalCallBind with no result variables."
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
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 | ParamType.bytes => true
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
      throw s!"Compilation error: custom error '{err.name}' uses unsupported dynamic parameter type {repr ty} ({issue586Ref}). Use uint256/address/bool/bytes32/bytes parameters."

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

def validateIdentifierShapes (spec : CompilationModel) : Except String Unit := do
  ensureContractIdentifier "contract" spec.name
  for field in spec.fields do
    ensureContractIdentifier "field" field.name
  for fn in spec.functions do
    ensureContractIdentifier "function" fn.name
    for p in fn.params do
      ensureContractIdentifier "function parameter" p.name
  match spec.constructor with
  | none => pure ()
  | some ctor =>
      for p in ctor.params do
        ensureContractIdentifier "constructor parameter" p.name
  for eventDef in spec.events do
    ensureContractIdentifier "event" eventDef.name
    for p in eventDef.params do
      ensureContractIdentifier "event parameter" p.name
  for err in spec.errors do
    ensureContractIdentifier "custom error" err.name
  for ext in spec.externals do
    ensureContractIdentifier "external declaration" ext.name

end Compiler.CompilationModel
