/-
  Compiler.CompilationModel: Declarative Compilation Model DSL

  This module defines a declarative way to model contracts for compilation,
  eliminating manual IR writing while keeping the system simple and maintainable.

  Philosophy:
  - Contracts specify their structure declaratively
  - Compiler generates IR automatically from the spec
  - Reduces boilerplate and eliminates manual slot/selector management

  Features:
  - Storage fields with automatic slot assignment (uint256, address, mapping)
  - Flexible mapping types: Address→Uint256, Uint256→Uint256, nested mappings (#154)
  - Functions with automatic selector computation
  - Guards and access control patterns
  - If/else branching and bounded loops (#179)
  - Array/bytes parameter types and dynamic calldata (#180)
  - Internal function composition (#181)
  - Event emission (#153)
  - Verified external library integration (#184)
-/
import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.DynamicData
import Compiler.CompilationModel.EcmAxiomCollection
import Compiler.CompilationModel.InternalNaming
import Compiler.CompilationModel.LayoutValidation
import Compiler.CompilationModel.MappingWrites
import Compiler.CompilationModel.UsageAnalysis
import Compiler.CompilationModel.ValidationHelpers
import Compiler.CompilationModel.SelectorInteropHelpers
import Compiler.CompilationModel.ExpressionCompile

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul


private def findParamType (params : List Param) (name : String) : Option ParamType :=
  (params.find? (fun p => p.name == name)).map (·.ty)

private def exprContainsCallLike (expr : Expr) : Bool :=
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

private def issue748Ref : String :=
  "Issue #748 (logicalAnd/logicalOr eager evaluation footgun)"

private def issue586Ref : String :=
  "Issue #586 (Solidity interop profile)"

private def issue623Ref : String :=
  "Issue #623 (CompilationModel storage layout controls)"

private def issue625Ref : String :=
  "Issue #625 (internal function multi-return support)"

private def issue732Ref : String :=
  "Issue #732 (reject undeclared external call targets)"

private def issue734Ref : String :=
  "Issue #734 (view/pure mutability enforcement)"

private def issue738Ref : String :=
  "Issue #738 (exhaustive return-path analysis)"

private def issue753Ref : String :=
  "Issue #753 (internal dynamic params unsupported)"

private def issue756Ref : String :=
  "Issue #756 (external/helper namespace collisions)"

private def issue184Ref : String :=
  "Issue #184 (verified external interface declarations)"

private def validateLogicalOperandPurity (context : String) (a b : Expr) : Except String Unit := do
  if exprContainsCallLike a || exprContainsCallLike b then
    throw s!"Compilation error: {context} uses Expr.logicalAnd/Expr.logicalOr with call-like operand(s), which are eagerly evaluated ({issue748Ref}). Move call-like expressions into Stmt.letVar/Stmt.ite before combining booleans."

/-- Validate that subexpressions duplicated by arithmetic helpers don't contain call-like expressions.
    mulDivUp/wDivUp/min/max inline subexpressions multiple times in the generated Yul,
    so call-like operands would be re-evaluated. -/
private def validateArithDuplicatedOperandPurity (context : String) (duplicated : List Expr) : Except String Unit := do
  if duplicated.any exprContainsCallLike then
    throw s!"Compilation error: {context} uses an arithmetic helper (mulDivUp/wDivUp/min/max) with call-like operand(s) that would be duplicated in Yul output ({issue748Ref}). Move call-like expressions into Stmt.letVar before using them in arithmetic helpers."

mutual
private def exprContainsUnsafeLogicalCallLike (expr : Expr) : Bool :=
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

private def exprListAnyUnsafeLogicalCallLike : List Expr → Bool
  | [] => false
  | e :: es => exprContainsUnsafeLogicalCallLike e || exprListAnyUnsafeLogicalCallLike es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

private def stmtContainsUnsafeLogicalCallLike : Stmt → Bool
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

private def stmtListAnyUnsafeLogicalCallLike : List Stmt → Bool
  | [] => false
  | s :: ss => stmtContainsUnsafeLogicalCallLike s || stmtListAnyUnsafeLogicalCallLike ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

private partial def staticParamBindingNames (name : String) (ty : ParamType) : List String :=
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

private def dynamicParamBindingNames (name : String) : List String :=
  [s!"{name}_offset", s!"{name}_length", s!"{name}_data_offset"]

mutual
private def isDynamicParamTypeForScope : ParamType → Bool
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

private def paramTypeListAnyDynamicForScope : List ParamType → Bool
  | [] => false
  | ty :: rest => isDynamicParamTypeForScope ty || paramTypeListAnyDynamicForScope rest
termination_by tys => sizeOf tys
decreasing_by all_goals simp_wf; all_goals omega
end

private def isScalarParamTypeForScope : ParamType → Bool
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 => true
  | _ => false

private def paramBindingNames (param : Param) : List String :=
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

private def paramScopeNames (params : List Param) : List String :=
  params.flatMap paramBindingNames

private def dynamicParamBases (params : List Param) : List String :=
  (params.filter (fun p => isDynamicParamTypeForScope p.ty)).map (·.name)

mutual
private def validateScopedExprIdentifiers
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

private def validateScopedExprIdentifiersList
    (context : String) (params : List Param) (paramScope : List String) (dynamicParams : List String)
    (localScope : List String) (constructorArgCount : Option Nat) : List Expr → Except String Unit
  | [] => pure ()
  | e :: es => do
      validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount e
      validateScopedExprIdentifiersList context params paramScope dynamicParams localScope constructorArgCount es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

private def validateScopedStmtIdentifiers
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

private def validateScopedStmtListIdentifiers
    (context : String) (params : List Param) (paramScope : List String) (dynamicParams : List String)
    (localScope : List String) (constructorArgCount : Option Nat) : List Stmt → Except String (List String)
  | [] => pure localScope
  | stmt :: rest => do
      let nextScope ← validateScopedStmtIdentifiers context params paramScope dynamicParams localScope constructorArgCount stmt
      validateScopedStmtListIdentifiers context params paramScope dynamicParams nextScope constructorArgCount rest
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

private def validateFunctionIdentifierReferences (spec : FunctionSpec) : Except String Unit := do
  let _ ← validateScopedStmtListIdentifiers
    s!"function '{spec.name}'"
    spec.params
    (paramScopeNames spec.params)
    (dynamicParamBases spec.params)
    []
    none
    spec.body
  pure ()

private def validateConstructorIdentifierReferences (ctor : Option ConstructorSpec) : Except String Unit := do
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

private def isStorageWordArrayParam : ParamType → Bool
  | ParamType.array ParamType.bytes32 => true
  | ParamType.array ParamType.uint256 => true
  | _ => false

mutual
private def validateStmtParamReferences (fnName : String) (params : List Param) :
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

private def validateStmtParamReferencesInList (fnName : String) (params : List Param) :
    List Stmt → Except String Unit
  | [] => pure ()
  | s :: ss => do
      validateStmtParamReferences fnName params s
      validateStmtParamReferencesInList fnName params ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
private def validateReturnShapesInStmt (fnName : String)
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

private def validateReturnShapesInStmtList (fnName : String)
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

private def exprReadsStateOrEnv : Expr → Bool
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
private def exprWritesState : Expr → Bool
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

private def exprListWritesState : List Expr → Bool
  | [] => false
  | e :: es => exprWritesState e || exprListWritesState es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

private def stmtWritesState : Stmt → Bool
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

private def stmtListWritesState : List Stmt → Bool
  | [] => false
  | s :: ss => stmtWritesState s || stmtListWritesState ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
private def stmtReadsStateOrEnv : Stmt → Bool
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

private def stmtListReadsStateOrEnv : List Stmt → Bool
  | [] => false
  | s :: ss => stmtReadsStateOrEnv s || stmtListReadsStateOrEnv ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

private def validateFunctionSpec (spec : FunctionSpec) : Except String Unit := do
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
private def validateNoRuntimeReturnsInConstructorStmt : Stmt → Except String Unit
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

private def validateNoRuntimeReturnsInConstructorStmtList : List Stmt → Except String Unit
  | [] => pure ()
  | s :: ss => do
      validateNoRuntimeReturnsInConstructorStmt s
      validateNoRuntimeReturnsInConstructorStmtList ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

private def validateConstructorSpec (ctor : Option ConstructorSpec) : Except String Unit := do
  match ctor with
  | none => pure ()
  | some spec =>
      if spec.body.any stmtContainsUnsafeLogicalCallLike then
        throw s!"Compilation error: constructor uses Expr.logicalAnd/Expr.logicalOr/Expr.ite or arithmetic helpers (mulDivUp/wDivUp/min/max) with call-like operand(s) that would be duplicated in Yul output ({issue748Ref}). Move call-like expressions into Stmt.letVar before combining."
      spec.body.forM validateNoRuntimeReturnsInConstructorStmt
      spec.body.forM (validateStmtParamReferences "constructor" spec.params)
      validateConstructorIdentifierReferences ctor

private def customErrorRequiresDirectParamRef : ParamType → Bool
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 => false
  | _ => true

private def validateDirectParamCustomErrorArg
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
private def validateCustomErrorArgShapesInStmt (fnName : String) (params : List Param)
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

private def validateCustomErrorArgShapesInStmtList (fnName : String) (params : List Param)
    (errors : List ErrorDef) : List Stmt → Except String Unit
  | [] => pure ()
  | s :: ss => do
      validateCustomErrorArgShapesInStmt fnName params errors s
      validateCustomErrorArgShapesInStmtList fnName params errors ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

private def validateCustomErrorArgShapesInFunction (spec : FunctionSpec) (errors : List ErrorDef) :
    Except String Unit := do
  spec.body.forM (validateCustomErrorArgShapesInStmt spec.name spec.params errors)

-- Whether an ABI param type is dynamically sized (requires offset-based encoding).
-- Used by both event encoding and calldata parameter loading.
mutual
  def isDynamicParamType : ParamType → Bool
    | ParamType.uint256 => false
    | ParamType.uint8 => false
    | ParamType.address => false
    | ParamType.bool => false
    | ParamType.bytes32 => false
    | ParamType.array _ => true
    | ParamType.bytes => true
    | ParamType.fixedArray elemTy _ => isDynamicParamType elemTy
    | ParamType.tuple elemTys => isDynamicParamTypeList elemTys
  termination_by ty => sizeOf ty

  private def isDynamicParamTypeList : List ParamType → Bool
    | [] => false
    | ty :: rest => isDynamicParamType ty || isDynamicParamTypeList rest
  termination_by tys => sizeOf tys
end

-- ABI head size in bytes for a param type. Dynamic types occupy one 32-byte
-- offset word; static composites are the sum of their element head sizes.
-- Used by both event encoding and calldata parameter loading.
mutual
  def paramHeadSize : ParamType → Nat
    | ParamType.uint256 => 32
    | ParamType.uint8 => 32
    | ParamType.address => 32
    | ParamType.bool => 32
    | ParamType.bytes32 => 32
    | ParamType.array _ => 32
    | ParamType.bytes => 32
    | ParamType.fixedArray elemTy n =>
        if isDynamicParamType elemTy then 32 else n * paramHeadSize elemTy
    | ParamType.tuple elemTys =>
        if isDynamicParamTypeList elemTys then 32 else paramHeadSizeList elemTys
  termination_by ty => sizeOf ty

  private def paramHeadSizeList : List ParamType → Nat
    | [] => 0
    | ty :: rest => paramHeadSize ty + paramHeadSizeList rest
  termination_by tys => sizeOf tys
end

-- Legacy aliases used throughout event encoding code.
private def eventIsDynamicType := isDynamicParamType
private def eventHeadWordSize := paramHeadSize

private def indexedDynamicArrayElemSupported (elemTy : ParamType) : Bool :=
  !eventIsDynamicType elemTy &&
    eventHeadWordSize elemTy > 0

private partial def validateEventArgShapesInStmt (fnName : String) (params : List Param)
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

private def validateEventArgShapesInFunction (spec : FunctionSpec) (events : List EventDef) :
    Except String Unit := do
  spec.body.forM (validateEventArgShapesInStmt spec.name spec.params events)

private def normalizeEventWord (ty : ParamType) (expr : YulExpr) : YulExpr :=
  match ty with
  | ParamType.uint8 => YulExpr.call "and" [expr, YulExpr.lit 255]
  | ParamType.address => YulExpr.call "and" [expr, YulExpr.hex addressMask]
  | ParamType.bool => yulToBool expr
  | _ => expr

private partial def staticCompositeLeaves (baseName : String) (ty : ParamType) :
    List (ParamType × YulExpr) :=
  match ty with
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      [(ty, YulExpr.ident baseName)]
  | ParamType.fixedArray elemTy n =>
      (List.range n).flatMap fun i =>
        staticCompositeLeaves s!"{baseName}_{i}" elemTy
  | ParamType.tuple elemTys =>
      let rec go (tys : List ParamType) (idx : Nat) : List (ParamType × YulExpr) :=
        match tys with
        | [] => []
        | elemTy :: rest =>
            staticCompositeLeaves s!"{baseName}_{idx}" elemTy ++ go rest (idx + 1)
      go elemTys 0
  | _ => []

private partial def staticCompositeLeafTypeOffsets
    (baseOffset : Nat) (ty : ParamType) : List (Nat × ParamType) :=
  match ty with
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      [(baseOffset, ty)]
  | ParamType.fixedArray elemTy n =>
      (List.range n).flatMap fun i =>
        staticCompositeLeafTypeOffsets (baseOffset + i * eventHeadWordSize elemTy) elemTy
  | ParamType.tuple elemTys =>
      let rec go (remaining : List ParamType) (curOffset : Nat) : List (Nat × ParamType) :=
        match remaining with
        | [] => []
        | elemTy :: rest =>
            staticCompositeLeafTypeOffsets curOffset elemTy ++
              go rest (curOffset + eventHeadWordSize elemTy)
      go elemTys baseOffset
  | _ => []

private def indexedDynamicBaseOffsetExpr (dynamicSource : DynamicDataSource) (paramName : String) : YulExpr :=
  match dynamicSource with
  | .calldata => YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident s!"{paramName}_offset"]
  | .memory => YulExpr.ident s!"{paramName}_offset"

private partial def compileIndexedInPlaceEncoding
    (dynamicSource : DynamicDataSource) (ty : ParamType)
    (srcBase dstBase : YulExpr) (stem : String) :
    Except String (List YulStmt × YulExpr) := do
  match ty with
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      let loaded := dynamicWordLoad dynamicSource srcBase
      pure ([
        YulStmt.expr (YulExpr.call "mstore" [dstBase, normalizeEventWord ty loaded])
      ], YulExpr.lit 32)
  | ParamType.bytes =>
      let lenName := s!"{stem}_len"
      let paddedName := s!"{stem}_padded"
      pure ([
        YulStmt.let_ lenName (dynamicWordLoad dynamicSource srcBase)
      ] ++ dynamicCopyData dynamicSource
        dstBase
        (YulExpr.call "add" [srcBase, YulExpr.lit 32])
        (YulExpr.ident lenName) ++ [
        YulStmt.let_ paddedName (YulExpr.call "and" [
          YulExpr.call "add" [YulExpr.ident lenName, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ]),
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [dstBase, YulExpr.ident lenName],
          YulExpr.lit 0
        ])
      ], YulExpr.ident paddedName)
  | ParamType.array elemTy =>
      let lenName := s!"{stem}_arr_len"
      let dataBaseName := s!"{stem}_arr_data"
      let loopIndexName := s!"{stem}_arr_i"
      let outLenName := s!"{stem}_arr_out_len"
      let elemSrcName := s!"{stem}_arr_elem_src"
      let elemDstName := s!"{stem}_arr_elem_dst"
      let initStmts := [
        YulStmt.let_ lenName (dynamicWordLoad dynamicSource srcBase),
        YulStmt.let_ dataBaseName (YulExpr.call "add" [srcBase, YulExpr.lit 32]),
        YulStmt.let_ outLenName (YulExpr.lit 0)
      ]
      let elemSrcExpr :=
        if eventIsDynamicType elemTy then
          let relName := s!"{stem}_arr_elem_rel"
          let relDecl := YulStmt.let_ relName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
            YulExpr.ident dataBaseName,
            YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit 32]
          ]))
          let srcDecl := YulStmt.let_ elemSrcName (YulExpr.call "add" [
            YulExpr.ident dataBaseName,
            YulExpr.ident relName
          ])
          ([relDecl, srcDecl], YulExpr.ident elemSrcName)
        else
          let srcDecl := YulStmt.let_ elemSrcName (YulExpr.call "add" [
            YulExpr.ident dataBaseName,
            YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit (eventHeadWordSize elemTy)]
          ])
          ([srcDecl], YulExpr.ident elemSrcName)
      let (elemEncodeStmts, elemEncodedLen) ←
        compileIndexedInPlaceEncoding dynamicSource elemTy (elemSrcExpr.2) (YulExpr.ident elemDstName) s!"{stem}_arr_elem"
      let loopBody :=
        elemSrcExpr.1 ++ [
          YulStmt.let_ elemDstName (YulExpr.call "add" [dstBase, YulExpr.ident outLenName])
        ] ++ elemEncodeStmts ++ [
          YulStmt.assign outLenName (YulExpr.call "add" [YulExpr.ident outLenName, elemEncodedLen])
        ]
      pure (initStmts ++ [
        YulStmt.for_
          [YulStmt.let_ loopIndexName (YulExpr.lit 0)]
          (YulExpr.call "lt" [YulExpr.ident loopIndexName, YulExpr.ident lenName])
          [YulStmt.assign loopIndexName (YulExpr.call "add" [YulExpr.ident loopIndexName, YulExpr.lit 1])]
          loopBody
      ], YulExpr.ident outLenName)
  | ParamType.fixedArray elemTy n =>
      let outLenName := s!"{stem}_fixed_out_len"
      let initStmts := [YulStmt.let_ outLenName (YulExpr.lit 0)]
      let rec goFixed (i : Nat) : Except String (List YulStmt) := do
        if i < n then
          let elemSrcName := s!"{stem}_fixed_elem_src_{i}"
          let elemDstName := s!"{stem}_fixed_elem_dst_{i}"
          let srcStmts :=
            if eventIsDynamicType elemTy then
              let relName := s!"{stem}_fixed_elem_rel_{i}"
              [
                YulStmt.let_ relName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
                  srcBase, YulExpr.lit (i * 32)
                ])),
                YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.ident relName])
              ]
            else
              [YulStmt.let_ elemSrcName (YulExpr.call "add" [
                srcBase, YulExpr.lit (i * eventHeadWordSize elemTy)
              ])]
          let elemDstStmt := YulStmt.let_ elemDstName (YulExpr.call "add" [dstBase, YulExpr.ident outLenName])
          let (elemEncodeStmts, elemEncodedLen) ←
            compileIndexedInPlaceEncoding dynamicSource elemTy
              (YulExpr.ident elemSrcName)
              (YulExpr.ident elemDstName)
              s!"{stem}_fixed_elem_{i}"
          let rest ← goFixed (i + 1)
          pure (srcStmts ++ [elemDstStmt] ++ elemEncodeStmts ++ [
            YulStmt.assign outLenName (YulExpr.call "add" [YulExpr.ident outLenName, elemEncodedLen])
          ] ++ rest)
        else
          pure []
      pure (initStmts ++ (← goFixed 0), YulExpr.ident outLenName)
  | ParamType.tuple elemTys =>
      let outLenName := s!"{stem}_tuple_out_len"
      let initStmts := [YulStmt.let_ outLenName (YulExpr.lit 0)]
      let rec goTuple (remaining : List ParamType) (elemIdx headOffset : Nat) :
          Except String (List YulStmt) := do
        match remaining with
        | [] => pure []
        | elemTy :: rest =>
            let elemSrcName := s!"{stem}_tuple_elem_src_{elemIdx}"
            let elemDstName := s!"{stem}_tuple_elem_dst_{elemIdx}"
            let srcStmts :=
              if eventIsDynamicType elemTy then
                let relName := s!"{stem}_tuple_elem_rel_{elemIdx}"
                [
                  YulStmt.let_ relName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
                    srcBase, YulExpr.lit headOffset
                  ])),
                  YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.ident relName])
                ]
              else
                [YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.lit headOffset])]
            let elemDstStmt := YulStmt.let_ elemDstName (YulExpr.call "add" [dstBase, YulExpr.ident outLenName])
            let (elemEncodeStmts, elemEncodedLen) ←
              compileIndexedInPlaceEncoding dynamicSource elemTy
                (YulExpr.ident elemSrcName)
                (YulExpr.ident elemDstName)
                s!"{stem}_tuple_elem_{elemIdx}"
            let restStmts ← goTuple rest (elemIdx + 1) (headOffset + eventHeadWordSize elemTy)
            pure (srcStmts ++ [elemDstStmt] ++ elemEncodeStmts ++ [
              YulStmt.assign outLenName (YulExpr.call "add" [YulExpr.ident outLenName, elemEncodedLen])
            ] ++ restStmts)
      pure (initStmts ++ (← goTuple elemTys 0 0), YulExpr.ident outLenName)

private def lowLevelCallUnsupportedError (context : String) (name : String) : Except String Unit :=
  throw s!"Compilation error: {context} uses unsupported low-level call '{name}' ({issue586Ref}). Use a verified linked external function wrapper instead of raw call/staticcall/delegatecall/callcode."

private def interopBuiltinCallUnsupportedError (context : String) (name : String) : Except String Unit :=
  throw s!"Compilation error: {context} uses unsupported interop builtin call '{name}' ({issue586Ref}). Use a verified linked external wrapper or pass the required value through explicit function parameters."

private def unsupportedInteropCallError (context : String) (name : String) : Except String Unit :=
  if isLowLevelCallName name then
    lowLevelCallUnsupportedError context name
  else
    interopBuiltinCallUnsupportedError context name

mutual
private def validateInteropExpr (context : String) : Expr → Except String Unit
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

private def validateInteropExprList (context : String) : List Expr → Except String Unit
  | [] => pure ()
  | e :: es => do
      validateInteropExpr context e
      validateInteropExprList context es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

private def validateInteropStmt (context : String) : Stmt → Except String Unit
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

private def validateInteropStmtList (context : String) : List Stmt → Except String Unit
  | [] => pure ()
  | s :: ss => do
      validateInteropStmt context s
      validateInteropStmtList context ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

private def validateInteropFunctionSpec (spec : FunctionSpec) : Except String Unit := do
  spec.body.forM (validateInteropStmt s!"function '{spec.name}'")

private def validateInteropExternalSpec (spec : ExternalFunction) : Except String Unit := do
  if isInteropBuiltinCallName spec.name then
    unsupportedInteropCallError s!"external declaration '{spec.name}'" spec.name

private def validateInteropConstructorSpec (ctor : Option ConstructorSpec) : Except String Unit := do
  match ctor with
  | none => pure ()
  | some spec =>
      spec.body.forM (validateInteropStmt "constructor")

private def validateSpecialEntrypointSpec (spec : FunctionSpec) : Except String Unit := do
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

private def reservedExternalNames (mappingHelpersRequired arrayHelpersRequired : Bool) : List String :=
  let mappingHelpers := if mappingHelpersRequired then ["mappingSlot"] else []
  let arrayHelpers :=
    if arrayHelpersRequired then
      [checkedArrayElementCalldataHelperName, checkedArrayElementMemoryHelperName]
    else
      []
  let entrypoints := ["fallback", "receive"]
  (mappingHelpers ++ arrayHelpers ++ entrypoints).eraseDups

private def firstReservedExternalCollision
    (spec : CompilationModel) (mappingHelpersRequired arrayHelpersRequired : Bool) : Option String :=
  (spec.externals.map (·.name)).find? (fun name =>
    name.startsWith internalFunctionPrefix ||
      (reservedExternalNames mappingHelpersRequired arrayHelpersRequired).contains name)

private def firstInternalDynamicParam
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

private def findInternalFunctionByName (functions : List FunctionSpec)
    (callerName calleeName : String) : Except String FunctionSpec := do
  let candidates := functions.filter (fun fn => fn.isInternal && fn.name == calleeName)
  match candidates with
  | [fn] => pure fn
  | [] =>
      throw s!"Compilation error: function '{callerName}' references unknown internal function '{calleeName}' ({issue625Ref})."
  | _ =>
      throw s!"Compilation error: function '{callerName}' references ambiguous internal function '{calleeName}' ({issue625Ref})."

mutual
private def validateInternalCallShapesInExpr
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

private def validateInternalCallShapesInExprList
    (functions : List FunctionSpec) (callerName : String) : List Expr → Except String Unit
  | [] => pure ()
  | e :: es => do
      validateInternalCallShapesInExpr functions callerName e
      validateInternalCallShapesInExprList functions callerName es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

private def validateInternalCallShapesInStmt
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

private def validateInternalCallShapesInStmtList
    (functions : List FunctionSpec) (callerName : String) : List Stmt → Except String Unit
  | [] => pure ()
  | s :: ss => do
      validateInternalCallShapesInStmt functions callerName s
      validateInternalCallShapesInStmtList functions callerName ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

private def validateInternalCallShapesInFunction (functions : List FunctionSpec)
    (spec : FunctionSpec) : Except String Unit := do
  spec.body.forM (validateInternalCallShapesInStmt functions spec.name)

mutual
private def validateExternalCallTargetsInExpr
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

private def validateExternalCallTargetsInExprList
    (externals : List ExternalFunction) (context : String) : List Expr → Except String Unit
  | [] => pure ()
  | e :: es => do
      validateExternalCallTargetsInExpr externals context e
      validateExternalCallTargetsInExprList externals context es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

private def validateExternalCallTargetsInStmt
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

private def validateExternalCallTargetsInStmtList
    (externals : List ExternalFunction) (context : String) : List Stmt → Except String Unit
  | [] => pure ()
  | s :: ss => do
      validateExternalCallTargetsInStmt externals context s
      validateExternalCallTargetsInStmtList externals context ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

private def validateExternalCallTargetsInFunction
    (externals : List ExternalFunction) (spec : FunctionSpec) : Except String Unit := do
  spec.body.forM (validateExternalCallTargetsInStmt externals s!"function '{spec.name}'")

private def validateExternalCallTargetsInConstructor
    (externals : List ExternalFunction) (ctor : Option ConstructorSpec) : Except String Unit := do
  match ctor with
  | none => pure ()
  | some spec =>
      spec.body.forM (validateExternalCallTargetsInStmt externals "constructor")

mutual
private def supportedCustomErrorParamType : ParamType → Bool
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 | ParamType.bytes => true
  | ParamType.array elemTy => supportedCustomErrorParamType elemTy
  | ParamType.fixedArray elemTy _ => supportedCustomErrorParamType elemTy
  | ParamType.tuple elemTys => supportedCustomErrorParamTypes elemTys
termination_by ty => sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals omega

private def supportedCustomErrorParamTypes : List ParamType → Bool
  | [] => true
  | ty :: tys => supportedCustomErrorParamType ty && supportedCustomErrorParamTypes tys
termination_by tys => sizeOf tys
decreasing_by
  all_goals simp_wf
  all_goals omega
end

private def encodeStaticCustomErrorArg (errorName : String) (ty : ParamType) (argExpr : YulExpr) :
    Except String YulExpr :=
  match ty with
  | ParamType.uint256 | ParamType.bytes32 =>
      pure argExpr
  | ParamType.uint8 =>
      pure (YulExpr.call "and" [argExpr, YulExpr.lit 255])
  | ParamType.address =>
      pure (YulExpr.call "and" [argExpr, YulExpr.hex addressMask])
  | ParamType.bool =>
      pure (yulToBool argExpr)
  | _ =>
      throw s!"Compilation error: custom error '{errorName}' uses unsupported non-scalar parameter type {repr ty} in scalar encoding ({issue586Ref})."

/-- Compute the ABI head size (in bytes) for a list of member types.
Static members take their flattened word count × 32; dynamic members take 32 (offset word). -/
private def abiHeadSize (tys : List ParamType) : Nat :=
  tys.foldl (fun acc ty => acc + eventHeadWordSize ty) 0

/-- Recursively ABI-encode a dynamic composite type into memory at `dstBase`.
    Reads input from `dynamicSource` at `srcBase`.
    Returns (stmts, totalLenExpr) where totalLenExpr is the total bytes written. -/
private partial def compileUnindexedAbiEncode
    (dynamicSource : DynamicDataSource) (ty : ParamType)
    (srcBase dstBase : YulExpr) (stem : String) :
    Except String (List YulStmt × YulExpr) := do
  match ty with
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      let loaded := dynamicWordLoad dynamicSource srcBase
      pure ([
        YulStmt.expr (YulExpr.call "mstore" [dstBase, normalizeEventWord ty loaded])
      ], YulExpr.lit 32)
  | ParamType.bytes =>
      let lenName := s!"{stem}_len"
      let paddedName := s!"{stem}_padded"
      pure ([
        YulStmt.let_ lenName (dynamicWordLoad dynamicSource srcBase),
        YulStmt.expr (YulExpr.call "mstore" [dstBase, YulExpr.ident lenName])
      ] ++ dynamicCopyData dynamicSource
        (YulExpr.call "add" [dstBase, YulExpr.lit 32])
        (YulExpr.call "add" [srcBase, YulExpr.lit 32])
        (YulExpr.ident lenName) ++ [
        YulStmt.let_ paddedName (YulExpr.call "and" [
          YulExpr.call "add" [YulExpr.ident lenName, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ]),
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [
            YulExpr.call "add" [dstBase, YulExpr.lit 32],
            YulExpr.ident lenName
          ],
          YulExpr.lit 0
        ])
      ], YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident paddedName])
  | ParamType.tuple elemTys =>
      let headSize := abiHeadSize elemTys
      let tailLenName := s!"{stem}_tail_len"
      let initStmts := [YulStmt.let_ tailLenName (YulExpr.lit headSize)]
      let rec goMembers (remaining : List ParamType) (elemIdx headOffset : Nat) :
          Except String (List YulStmt) := do
        match remaining with
        | [] => pure []
        | elemTy :: rest =>
            let elemSrcName := s!"{stem}_m{elemIdx}_src"
            let elemDstName := s!"{stem}_m{elemIdx}_dst"
            let srcStmts :=
              if eventIsDynamicType elemTy then
                let relName := s!"{stem}_m{elemIdx}_rel"
                [
                  YulStmt.let_ relName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
                    srcBase, YulExpr.lit headOffset
                  ])),
                  YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.ident relName])
                ]
              else
                [YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.lit headOffset])]
            let encStmts ←
              if eventIsDynamicType elemTy then do
                let storeOffset := YulStmt.expr (YulExpr.call "mstore" [
                  YulExpr.call "add" [dstBase, YulExpr.lit headOffset],
                  YulExpr.ident tailLenName
                ])
                let (innerStmts, innerLen) ←
                  compileUnindexedAbiEncode dynamicSource elemTy
                    (YulExpr.ident elemSrcName)
                    (YulExpr.ident elemDstName)
                    s!"{stem}_m{elemIdx}"
                pure ([storeOffset,
                  YulStmt.let_ elemDstName (YulExpr.call "add" [dstBase, YulExpr.ident tailLenName])
                ] ++ innerStmts ++ [
                  YulStmt.assign tailLenName (YulExpr.call "add" [YulExpr.ident tailLenName, innerLen])
                ])
              else do
                let (innerStmts, _) ←
                  compileUnindexedAbiEncode dynamicSource elemTy
                    (YulExpr.ident elemSrcName)
                    (YulExpr.call "add" [dstBase, YulExpr.lit headOffset])
                    s!"{stem}_m{elemIdx}"
                pure innerStmts
            let restStmts ← goMembers rest (elemIdx + 1) (headOffset + eventHeadWordSize elemTy)
            pure (srcStmts ++ encStmts ++ restStmts)
      let memberStmts ← goMembers elemTys 0 0
      pure (initStmts ++ memberStmts, YulExpr.ident tailLenName)
  | ParamType.fixedArray elemTy n =>
      if eventIsDynamicType elemTy then
        let tailLenName := s!"{stem}_fa_tail_len"
        let headSize := n * 32
        let initStmts := [YulStmt.let_ tailLenName (YulExpr.lit headSize)]
        let rec goElems (i : Nat) : Except String (List YulStmt) := do
          if i < n then
            let elemSrcName := s!"{stem}_fa{i}_src"
            let elemDstName := s!"{stem}_fa{i}_dst"
            let relName := s!"{stem}_fa{i}_rel"
            let storeOffset := YulStmt.expr (YulExpr.call "mstore" [
              YulExpr.call "add" [dstBase, YulExpr.lit (i * 32)],
              YulExpr.ident tailLenName
            ])
            let srcStmts := [
              YulStmt.let_ relName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
                srcBase, YulExpr.lit (i * 32)
              ])),
              YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.ident relName])
            ]
            let (innerStmts, innerLen) ←
              compileUnindexedAbiEncode dynamicSource elemTy
                (YulExpr.ident elemSrcName)
                (YulExpr.ident elemDstName)
                s!"{stem}_fa{i}"
            let restStmts ← goElems (i + 1)
            pure (srcStmts ++ [storeOffset,
              YulStmt.let_ elemDstName (YulExpr.call "add" [dstBase, YulExpr.ident tailLenName])
            ] ++ innerStmts ++ [
              YulStmt.assign tailLenName (YulExpr.call "add" [YulExpr.ident tailLenName, innerLen])
            ] ++ restStmts)
          else
            pure []
        let elemStmts ← goElems 0
        pure (initStmts ++ elemStmts, YulExpr.ident tailLenName)
      else
        let elemWordSize := eventHeadWordSize elemTy
        let rec goStaticElems (i : Nat) : Except String (List YulStmt) := do
          if i < n then
            let elemSrcName := s!"{stem}_fa{i}_src"
            let srcStmt := YulStmt.let_ elemSrcName (YulExpr.call "add" [
              srcBase, YulExpr.lit (i * elemWordSize)
            ])
            let (innerStmts, _) ←
              compileUnindexedAbiEncode dynamicSource elemTy
                (YulExpr.ident elemSrcName)
                (YulExpr.call "add" [dstBase, YulExpr.lit (i * elemWordSize)])
                s!"{stem}_fa{i}"
            let restStmts ← goStaticElems (i + 1)
            pure ([srcStmt] ++ innerStmts ++ restStmts)
          else
            pure []
        let elemStmts ← goStaticElems 0
        pure (elemStmts, YulExpr.lit (n * elemWordSize))
  | ParamType.array elemTy =>
      -- Dynamic array: [length][head_0]...[head_{n-1}][tail_0]...[tail_{n-1}]
      -- Each head word is an offset (relative to start of elements area) pointing
      -- to the element's tail data. For static elements the data is inline.
      let lenName := s!"{stem}_arr_len"
      let lenStmt := YulStmt.let_ lenName (dynamicWordLoad dynamicSource srcBase)
      let storeLenStmt := YulStmt.expr (YulExpr.call "mstore" [dstBase, YulExpr.ident lenName])
      if eventIsDynamicType elemTy then
        -- Dynamic elements need offset-based head/tail layout
        let headLenName := s!"{stem}_arr_head_len"
        let tailLenName := s!"{stem}_arr_tail_len"
        let loopIdxName := s!"{stem}_arr_i"
        let elemRelName := s!"{stem}_arr_elem_rel"
        let elemSrcName := s!"{stem}_arr_elem_src"
        let elemDstName := s!"{stem}_arr_elem_dst"
        -- We generate a loop that processes each element:
        --   1) Read element offset from source, resolve to absolute source position
        --   2) Store current tail offset as the head word
        --   3) Recursively encode element data at current tail position
        --   4) Advance tail offset
        -- Since element encoding size is data-dependent, we track tail with a mutable var.
        let (innerStmts, innerLen) ←
          compileUnindexedAbiEncode dynamicSource elemTy
            (YulExpr.ident elemSrcName)
            (YulExpr.ident elemDstName)
            s!"{stem}_arr_e"
        let loopBody := [
          -- Read element's relative offset from source head area
          YulStmt.let_ elemRelName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
            YulExpr.call "add" [srcBase, YulExpr.lit 32],
            YulExpr.call "mul" [YulExpr.ident loopIdxName, YulExpr.lit 32]
          ])),
          -- Resolve to absolute source position (relative to array data start = srcBase + 32)
          YulStmt.let_ elemSrcName (YulExpr.call "add" [
            YulExpr.call "add" [srcBase, YulExpr.lit 32],
            YulExpr.ident elemRelName
          ]),
          -- Store offset in head area of destination
          YulStmt.expr (YulExpr.call "mstore" [
            YulExpr.call "add" [
              YulExpr.call "add" [dstBase, YulExpr.lit 32],
              YulExpr.call "mul" [YulExpr.ident loopIdxName, YulExpr.lit 32]
            ],
            YulExpr.ident tailLenName
          ]),
          -- Destination for this element's encoded data
          YulStmt.let_ elemDstName (YulExpr.call "add" [
            YulExpr.call "add" [dstBase, YulExpr.lit 32],
            YulExpr.ident tailLenName
          ])
        ] ++ innerStmts ++ [
          YulStmt.assign tailLenName (YulExpr.call "add" [YulExpr.ident tailLenName, innerLen])
        ]
        let loopStmt := YulStmt.for_
          [YulStmt.let_ loopIdxName (YulExpr.lit 0)]
          (YulExpr.call "lt" [YulExpr.ident loopIdxName, YulExpr.ident lenName])
          [YulStmt.assign loopIdxName (YulExpr.call "add" [YulExpr.ident loopIdxName, YulExpr.lit 1])]
          loopBody
        pure ([lenStmt, storeLenStmt,
          YulStmt.let_ headLenName (YulExpr.call "mul" [YulExpr.ident lenName, YulExpr.lit 32]),
          YulStmt.let_ tailLenName (YulExpr.ident headLenName),
          loopStmt
        ], YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident tailLenName])
      else
        -- Static elements: each takes a fixed number of words, no offsets needed
        let elemWordSize := eventHeadWordSize elemTy
        let byteLenName := s!"{stem}_arr_byte_len"
        let loopIdxName := s!"{stem}_arr_i"
        let elemSrcName := s!"{stem}_arr_elem_src"
        let (innerStmts, _) ←
          compileUnindexedAbiEncode dynamicSource elemTy
            (YulExpr.ident elemSrcName)
            (YulExpr.call "add" [
              YulExpr.call "add" [dstBase, YulExpr.lit 32],
              YulExpr.call "mul" [YulExpr.ident loopIdxName, YulExpr.lit elemWordSize]
            ])
            s!"{stem}_arr_e"
        let loopBody := [
          YulStmt.let_ elemSrcName (YulExpr.call "add" [
            YulExpr.call "add" [srcBase, YulExpr.lit 32],
            YulExpr.call "mul" [YulExpr.ident loopIdxName, YulExpr.lit elemWordSize]
          ])
        ] ++ innerStmts
        let loopStmt := YulStmt.for_
          [YulStmt.let_ loopIdxName (YulExpr.lit 0)]
          (YulExpr.call "lt" [YulExpr.ident loopIdxName, YulExpr.ident lenName])
          [YulStmt.assign loopIdxName (YulExpr.call "add" [YulExpr.ident loopIdxName, YulExpr.lit 1])]
          loopBody
        let paddedName := s!"{stem}_arr_padded"
        pure ([lenStmt, storeLenStmt,
            YulStmt.let_ byteLenName (YulExpr.call "mul" [YulExpr.ident lenName, YulExpr.lit elemWordSize]),
            loopStmt,
            YulStmt.let_ paddedName (YulExpr.call "and" [
              YulExpr.call "add" [YulExpr.ident byteLenName, YulExpr.lit 31],
              YulExpr.call "not" [YulExpr.lit 31]
            ])
          ], YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident paddedName])

private def revertWithCustomError (dynamicSource : DynamicDataSource)
    (errorDef : ErrorDef) (sourceArgs : List Expr) (args : List YulExpr) :
    Except String (List YulStmt) := do
  if errorDef.params.length != args.length || sourceArgs.length != args.length then
    throw s!"Compilation error: custom error '{errorDef.name}' expects {errorDef.params.length} args, got {args.length}"
  let sigBytes := bytesFromString (errorSignature errorDef)
  let storePtr := YulStmt.let_ "__err_ptr" (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
  let sigStores := (chunkBytes32 sigBytes).zipIdx.map fun (chunk, idx) =>
    YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.call "add" [YulExpr.ident "__err_ptr", YulExpr.lit (idx * 32)],
      YulExpr.hex (wordFromBytes chunk)
    ])
  let hashStmt := YulStmt.let_ "__err_hash"
    (YulExpr.call "keccak256" [YulExpr.ident "__err_ptr", YulExpr.lit sigBytes.length])
  let selectorStmt := YulStmt.let_ "__err_selector"
    (YulExpr.call "shl" [YulExpr.lit selectorShift, YulExpr.call "shr" [YulExpr.lit selectorShift, YulExpr.ident "__err_hash"]])
  let selectorStore := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.ident "__err_selector"])
  let headSize := abiHeadSize errorDef.params
  let tailInit := YulStmt.let_ "__err_tail" (YulExpr.lit headSize)
  let argsWithSources := (errorDef.params.zip sourceArgs).zip args |>.map (fun ((ty, srcExpr), argExpr) => (ty, srcExpr, argExpr))
  let rec attachOffsets (items : List (ParamType × Expr × YulExpr)) (headOffset : Nat) :
      List (ParamType × Expr × YulExpr × Nat) :=
    match items with
    | [] => []
    | (ty, srcExpr, argExpr) :: rest =>
        (ty, srcExpr, argExpr, headOffset) :: attachOffsets rest (headOffset + paramHeadSize ty)
  let argsWithHeadOffsets := attachOffsets argsWithSources 4
  let argStores ← argsWithHeadOffsets.zipIdx.mapM fun ((ty, srcExpr, argExpr, headOffset), idx) => do
    match ty with
    | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
        let encoded ← encodeStaticCustomErrorArg errorDef.name ty argExpr
        pure [YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit headOffset, encoded])]
    | ParamType.tuple _ | ParamType.fixedArray _ _ =>
        match srcExpr with
        | Expr.param name =>
            if isDynamicParamType ty then
              let dstName := s!"__err_arg{idx}_dst"
              let srcBase := indexedDynamicBaseOffsetExpr dynamicSource name
              let (encStmts, encLen) ←
                compileUnindexedAbiEncode dynamicSource ty srcBase (YulExpr.ident dstName) s!"__err_arg{idx}"
              pure ([
                YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit headOffset, YulExpr.ident "__err_tail"]),
                YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident "__err_tail"])
              ] ++ encStmts ++ [
                YulStmt.assign "__err_tail" (YulExpr.call "add" [YulExpr.ident "__err_tail", encLen])
              ])
            else
              let leaves := staticCompositeLeaves name ty
              let stores := leaves.zipIdx.map fun ((leafTy, leafExpr), wordIdx) =>
                YulStmt.expr (YulExpr.call "mstore" [
                  YulExpr.lit (headOffset + wordIdx * 32),
                  normalizeEventWord leafTy leafExpr
                ])
              pure stores
        | _ =>
            throw s!"Compilation error: custom error '{errorDef.name}' parameter of type {repr ty} currently requires direct parameter reference ({issue586Ref})."
    | ParamType.bytes | ParamType.array _ =>
        match srcExpr with
        | Expr.param name =>
            let dstName := s!"__err_arg{idx}_dst"
            let srcBase := indexedDynamicBaseOffsetExpr dynamicSource name
            let (encStmts, encLen) ←
              compileUnindexedAbiEncode dynamicSource ty srcBase (YulExpr.ident dstName) s!"__err_arg{idx}"
            pure ([
              YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit headOffset, YulExpr.ident "__err_tail"]),
              YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident "__err_tail"])
            ] ++ encStmts ++ [
              YulStmt.assign "__err_tail" (YulExpr.call "add" [YulExpr.ident "__err_tail", encLen])
            ])
        | _ =>
            throw s!"Compilation error: custom error '{errorDef.name}' parameter of type {repr ty} currently requires direct parameter reference ({issue586Ref})."
  let revertStmt := YulStmt.expr (YulExpr.call "revert" [
    YulExpr.lit 0,
    YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident "__err_tail"]
  ])
  pure [YulStmt.block ([storePtr] ++ sigStores ++ [hashStmt, selectorStmt, selectorStore, tailInit] ++ argStores.flatten ++ [revertStmt])]

-- Compile statement to Yul (using mutual recursion for lists).
-- When isInternal=true, Stmt.return compiles to `__ret := value; leave` so internal
-- function execution terminates immediately without exiting the outer EVM call.
mutual
def compileStmtList (fields : List Field) (events : List EventDef := [])
    (errors : List ErrorDef := [])
    (dynamicSource : DynamicDataSource := .calldata)
    (internalRetNames : List String := [])
    (isInternal : Bool := false)
    (inScopeNames : List String := []) :
    List Stmt → Except String (List YulStmt)
  | [] => pure []
  | s :: ss => do
      let head ← compileStmt fields events errors dynamicSource internalRetNames isInternal inScopeNames s
      let nextScopeNames := collectStmtNames s ++ inScopeNames
      let tail ← compileStmtList fields events errors dynamicSource internalRetNames isInternal nextScopeNames ss
      pure (head ++ tail)

def compileStmt (fields : List Field) (events : List EventDef := [])
    (errors : List ErrorDef := [])
    (dynamicSource : DynamicDataSource := .calldata)
    (internalRetNames : List String := [])
    (isInternal : Bool := false)
    (inScopeNames : List String := []) :
    Stmt → Except String (List YulStmt)
  | Stmt.letVar name value => do
      pure [YulStmt.let_ name (← compileExpr fields dynamicSource value)]
  | Stmt.assignVar name value => do
      pure [YulStmt.assign name (← compileExpr fields dynamicSource value)]
  | Stmt.setStorage field value =>
    if isMapping fields field then
      throw s!"Compilation error: field '{field}' is a mapping; use setMapping, setMappingWord, or setMappingPackedWord"
    else
      match findFieldWithResolvedSlot fields field with
      | some (f, slot) => do
          let slots := slot :: f.aliasSlots
          let valueExpr ← compileExpr fields dynamicSource value
          match slots with
          | [] =>
              throw s!"Compilation error: internal invariant failure: no write slots for field '{field}' in setStorage"
          | [singleSlot] =>
              match f.packedBits with
              | none =>
                  pure [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit singleSlot, valueExpr])]
              | some packed =>
                  let maskNat := packedMaskNat packed
                  let shiftedMaskNat := packedShiftedMaskNat packed
                  pure [
                    YulStmt.block [
                      YulStmt.let_ "__compat_value" valueExpr,
                      YulStmt.let_ "__compat_packed" (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit maskNat]),
                      YulStmt.let_ "__compat_slot_word" (YulExpr.call "sload" [YulExpr.lit singleSlot]),
                      YulStmt.let_ "__compat_slot_cleared" (YulExpr.call "and" [
                        YulExpr.ident "__compat_slot_word",
                        YulExpr.call "not" [YulExpr.lit shiftedMaskNat]
                      ]),
                      YulStmt.expr (YulExpr.call "sstore" [
                        YulExpr.lit singleSlot,
                        YulExpr.call "or" [
                          YulExpr.ident "__compat_slot_cleared",
                          YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]
                        ]
                      ])
                    ]
                  ]
          | _ =>
              match f.packedBits with
              | none =>
                  pure [
                    YulStmt.block (
                      [YulStmt.let_ "__compat_value" valueExpr] ++
                      slots.map (fun writeSlot =>
                        YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"]))
                    )
                  ]
              | some packed =>
                  let maskNat := packedMaskNat packed
                  let shiftedMaskNat := packedShiftedMaskNat packed
                  pure [
                    YulStmt.block (
                      [YulStmt.let_ "__compat_value" valueExpr,
                       YulStmt.let_ "__compat_packed" (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit maskNat])] ++
                      slots.map (fun writeSlot =>
                        YulStmt.block [
                          YulStmt.let_ "__compat_slot_word" (YulExpr.call "sload" [YulExpr.lit writeSlot]),
                          YulStmt.let_ "__compat_slot_cleared" (YulExpr.call "and" [
                            YulExpr.ident "__compat_slot_word",
                            YulExpr.call "not" [YulExpr.lit shiftedMaskNat]
                          ]),
                          YulStmt.expr (YulExpr.call "sstore" [
                            YulExpr.lit writeSlot,
                            YulExpr.call "or" [
                              YulExpr.ident "__compat_slot_cleared",
                              YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]
                            ]
                          ])
                        ])
                    )
                  ]
      | none => throw s!"Compilation error: unknown storage field '{field}' in setStorage"
  | Stmt.setMapping field key value => do
      compileMappingSlotWrite fields field
        (← compileExpr fields dynamicSource key)
        (← compileExpr fields dynamicSource value)
        "setMapping"
  | Stmt.setMappingWord field key wordOffset value => do
      compileMappingSlotWrite fields field
        (← compileExpr fields dynamicSource key)
        (← compileExpr fields dynamicSource value)
        "setMappingWord"
        wordOffset
  | Stmt.setMappingPackedWord field key wordOffset packed value => do
      compileMappingPackedSlotWrite fields field
        (← compileExpr fields dynamicSource key)
        (← compileExpr fields dynamicSource value)
        wordOffset
        packed
        "setMappingPackedWord"
  | Stmt.setMapping2 field key1 key2 value =>
    if !isMapping2 fields field then
      throw s!"Compilation error: field '{field}' is not a double mapping"
    else
      match findFieldWriteSlots fields field with
      | some slots => do
          let key1Expr ← compileExpr fields dynamicSource key1
          let key2Expr ← compileExpr fields dynamicSource key2
          let valueExpr ← compileExpr fields dynamicSource value
          match slots with
          | [] =>
              throw s!"Compilation error: internal invariant failure: no write slots for mapping field '{field}' in setMapping2"
          | [slot] =>
              let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
              pure [
                YulStmt.expr (YulExpr.call "sstore" [
                  YulExpr.call "mappingSlot" [innerSlot, key2Expr],
                  valueExpr
                ])
              ]
          | _ =>
              pure [
                YulStmt.block (
                  [YulStmt.let_ "__compat_key1" key1Expr, YulStmt.let_ "__compat_key2" key2Expr, YulStmt.let_ "__compat_value" valueExpr] ++
                  slots.map (fun slot =>
                    let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, YulExpr.ident "__compat_key1"]
                    YulStmt.expr (YulExpr.call "sstore" [
                      YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"],
                      YulExpr.ident "__compat_value"
                    ]))
                )
              ]
      | none => throw s!"Compilation error: unknown mapping field '{field}' in setMapping2"
  | Stmt.setMapping2Word field key1 key2 wordOffset value =>
    if !isMapping2 fields field then
      throw s!"Compilation error: field '{field}' is not a double mapping"
    else
      match findFieldWriteSlots fields field with
      | some slots => do
          let key1Expr ← compileExpr fields dynamicSource key1
          let key2Expr ← compileExpr fields dynamicSource key2
          let valueExpr ← compileExpr fields dynamicSource value
          match slots with
          | [] =>
              throw s!"Compilation error: internal invariant failure: no write slots for mapping field '{field}' in setMapping2Word"
          | [slot] =>
              let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
              let outerSlot := YulExpr.call "mappingSlot" [innerSlot, key2Expr]
              let finalSlot := if wordOffset == 0 then outerSlot else YulExpr.call "add" [outerSlot, YulExpr.lit wordOffset]
              pure [
                YulStmt.expr (YulExpr.call "sstore" [finalSlot, valueExpr])
              ]
          | _ =>
              pure [
                YulStmt.block (
                  [YulStmt.let_ "__compat_key1" key1Expr, YulStmt.let_ "__compat_key2" key2Expr, YulStmt.let_ "__compat_value" valueExpr] ++
                  slots.map (fun slot =>
                    let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, YulExpr.ident "__compat_key1"]
                    let outerSlot := YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"]
                    let finalSlot := if wordOffset == 0 then outerSlot else YulExpr.call "add" [outerSlot, YulExpr.lit wordOffset]
                    YulStmt.expr (YulExpr.call "sstore" [finalSlot, YulExpr.ident "__compat_value"])))
              ]
      | none => throw s!"Compilation error: unknown mapping field '{field}' in setMapping2Word"
  | Stmt.setMappingUint field key value => do
      compileMappingSlotWrite fields field
        (← compileExpr fields dynamicSource key)
        (← compileExpr fields dynamicSource value)
        "setMappingUint"
  | Stmt.setStructMember field key memberName value => do
      if isMapping2 fields field then
        throw s!"Compilation error: field '{field}' is a double mapping; use Stmt.setStructMember2 instead of Stmt.setStructMember"
      match findStructMembers fields field with
      | none => throw s!"Compilation error: field '{field}' is not a mappingStruct"
      | some members =>
        match findStructMember members memberName with
        | none => throw s!"Compilation error: struct field '{field}' has no member '{memberName}'"
        | some member =>
          match member.packed with
          | none =>
            compileMappingSlotWrite fields field
              (← compileExpr fields dynamicSource key)
              (← compileExpr fields dynamicSource value)
              s!"setStructMember.{memberName}"
              member.wordOffset
          | some packed =>
            compileMappingPackedSlotWrite fields field
              (← compileExpr fields dynamicSource key)
              (← compileExpr fields dynamicSource value)
              member.wordOffset
              packed
              s!"setStructMember.{memberName}"
  | Stmt.setStructMember2 field key1 key2 memberName value =>
      if !isMapping2 fields field then
        throw s!"Compilation error: field '{field}' is not a double mapping; use Stmt.setStructMember instead of Stmt.setStructMember2"
      else
        match findStructMembers fields field with
        | none => throw s!"Compilation error: field '{field}' is not a mappingStruct"
        | some members =>
          match findStructMember members memberName with
          | none => throw s!"Compilation error: struct field '{field}' has no member '{memberName}'"
          | some member =>
            match findFieldWriteSlots fields field with
            | some slots => do
                let key1Expr ← compileExpr fields dynamicSource key1
                let key2Expr ← compileExpr fields dynamicSource key2
                let valueExpr ← compileExpr fields dynamicSource value
                match slots with
                | [] =>
                    throw s!"Compilation error: internal invariant failure: no write slots for mapping field '{field}' in setStructMember2.{memberName}"
                | [slot] =>
                    let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
                    let outerSlot := YulExpr.call "mappingSlot" [innerSlot, key2Expr]
                    let finalSlot := if member.wordOffset == 0 then outerSlot else YulExpr.call "add" [outerSlot, YulExpr.lit member.wordOffset]
                    match member.packed with
                    | none =>
                      pure [YulStmt.expr (YulExpr.call "sstore" [finalSlot, valueExpr])]
                    | some packed =>
                      let maskNat := packedMaskNat packed
                      let shiftedMaskNat := packedShiftedMaskNat packed
                      pure [
                        YulStmt.block [
                          YulStmt.let_ "__compat_value" valueExpr,
                          YulStmt.let_ "__compat_packed" (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit maskNat]),
                          YulStmt.let_ "__compat_slot_word" (YulExpr.call "sload" [finalSlot]),
                          YulStmt.let_ "__compat_slot_cleared" (YulExpr.call "and" [
                            YulExpr.ident "__compat_slot_word",
                            YulExpr.call "not" [YulExpr.lit shiftedMaskNat]
                          ]),
                          YulStmt.expr (YulExpr.call "sstore" [
                            finalSlot,
                            YulExpr.call "or" [
                              YulExpr.ident "__compat_slot_cleared",
                              YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]
                            ]
                          ])
                        ]
                      ]
                | _ =>
                    pure [
                      YulStmt.block (
                        [YulStmt.let_ "__compat_key1" key1Expr, YulStmt.let_ "__compat_key2" key2Expr, YulStmt.let_ "__compat_value" valueExpr] ++
                        slots.map (fun slot =>
                          let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, YulExpr.ident "__compat_key1"]
                          let outerSlot := YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"]
                          let finalSlot := if member.wordOffset == 0 then outerSlot else YulExpr.call "add" [outerSlot, YulExpr.lit member.wordOffset]
                          match member.packed with
                          | none =>
                            YulStmt.expr (YulExpr.call "sstore" [finalSlot, YulExpr.ident "__compat_value"])
                          | some packed =>
                            let maskNat := packedMaskNat packed
                            let shiftedMaskNat := packedShiftedMaskNat packed
                            YulStmt.block [
                              YulStmt.let_ "__compat_slot_word" (YulExpr.call "sload" [finalSlot]),
                              YulStmt.let_ "__compat_slot_cleared" (YulExpr.call "and" [
                                YulExpr.ident "__compat_slot_word",
                                YulExpr.call "not" [YulExpr.lit shiftedMaskNat]
                              ]),
                              YulStmt.expr (YulExpr.call "sstore" [
                                finalSlot,
                                YulExpr.call "or" [
                                  YulExpr.ident "__compat_slot_cleared",
                                  YulExpr.call "shl" [YulExpr.lit packed.offset,
                                    YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit maskNat]]
                                ]
                              ])
                            ])
                      )
                    ]
            | none => throw s!"Compilation error: unknown mapping field '{field}' in setStructMember2.{memberName}"
  | Stmt.require cond message =>
    do
      let failCond ← compileRequireFailCond fields dynamicSource cond
      pure [
        YulStmt.if_ failCond (revertWithMessage message)
      ]
  | Stmt.requireError cond errorName args => do
      let failCond ← compileRequireFailCond fields dynamicSource cond
      let errorDef ←
        match errors.find? (·.name == errorName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown custom error '{errorName}' ({issue586Ref})"
      let argExprs ← compileExprList fields dynamicSource args
      let revertStmts ← revertWithCustomError dynamicSource errorDef args argExprs
      pure [YulStmt.if_ failCond revertStmts]
  | Stmt.revertError errorName args => do
      let errorDef ←
        match errors.find? (·.name == errorName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown custom error '{errorName}' ({issue586Ref})"
      let argExprs ← compileExprList fields dynamicSource args
      revertWithCustomError dynamicSource errorDef args argExprs
  | Stmt.return value =>
    do
      let valueExpr ← compileExpr fields dynamicSource value
      if isInternal then
        match internalRetNames with
        | retName :: _ => pure [YulStmt.assign retName valueExpr, YulStmt.leave]
        | [] => throw s!"Compilation error: internal return target is missing"
      else
        pure [
          YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueExpr]),
          YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        ]
  | Stmt.stop => return [YulStmt.expr (YulExpr.call "stop" [])]

  | Stmt.ite cond thenBranch elseBranch => do
      -- If/else: compile to Yul if + negated if (#179)
      let condExpr ← compileExpr fields dynamicSource cond
      let thenStmts ← compileStmtList fields events errors dynamicSource internalRetNames isInternal inScopeNames thenBranch
      let elseStmts ← compileStmtList fields events errors dynamicSource internalRetNames isInternal inScopeNames elseBranch
      if elseBranch.isEmpty then
        -- Simple if (no else)
        pure [YulStmt.if_ condExpr thenStmts]
      else
        -- If/else: cache condition in a block-scoped local to avoid re-evaluation
        -- after then-branch may have mutated state.
        -- Wrapped in block { } and freshened against names seen in this if/else shape
        -- so user locals cannot shadow the compiler-generated temp.
        let iteUsedNames := inScopeNames ++ collectExprNames cond ++ collectStmtListNames thenBranch ++ collectStmtListNames elseBranch
        let iteCondName := pickFreshName "__ite_cond" iteUsedNames
        pure [YulStmt.block [
          YulStmt.let_ iteCondName condExpr,
          YulStmt.if_ (YulExpr.ident iteCondName) thenStmts,
          YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident iteCondName]) elseStmts
        ]]

  | Stmt.forEach varName count body => do
      -- Bounded loop: for { let i := 0 } lt(i, count) { i := add(i, 1) } { body } (#179)
      let countExpr ← compileExpr fields dynamicSource count
      let bodyStmts ← compileStmtList fields events errors dynamicSource internalRetNames isInternal (varName :: inScopeNames) body
      let initStmts := [YulStmt.let_ varName (YulExpr.lit 0)]
      let condExpr := YulExpr.call "lt" [YulExpr.ident varName, countExpr]
      let postStmts := [YulStmt.assign varName (YulExpr.call "add" [YulExpr.ident varName, YulExpr.lit 1])]
      pure [YulStmt.for_ initStmts condExpr postStmts bodyStmts]

  | Stmt.emit eventName args => do
      let eventDef? := events.find? (·.name == eventName)
      let eventDef ←
        match eventDef? with
        | some e => pure e
        | none => throw s!"Compilation error: unknown event '{eventName}'"
      if args.length != eventDef.params.length then
        throw s!"Compilation error: event '{eventName}' expects {eventDef.params.length} args, got {args.length}"
      let compiledArgs ← compileExprList fields dynamicSource args
      let zippedWithSource := (eventDef.params.zip args).zip compiledArgs |>.map (fun ((p, srcExpr), argExpr) =>
        (p, srcExpr, argExpr))
      let indexed := zippedWithSource.filter (fun (p, _, _) => p.kind == EventParamKind.indexed)
      let unindexed := zippedWithSource.filter (fun (p, _, _) => p.kind == EventParamKind.unindexed)
      if indexed.length > 3 then
        throw s!"Compilation error: event '{eventName}' has {indexed.length} indexed params; max is 3"
      let sig := eventSignature eventDef
      let sigBytes := bytesFromString sig
      let freeMemPtr := YulExpr.call "mload" [YulExpr.lit freeMemoryPointer]
      let storePtr := YulStmt.let_ "__evt_ptr" freeMemPtr
      let sigStores := (chunkBytes32 sigBytes).zipIdx.map fun (chunk, idx) =>
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit (idx * 32)],
          YulExpr.hex (wordFromBytes chunk)
        ])
      let topic0Expr := YulExpr.call "keccak256" [YulExpr.ident "__evt_ptr", YulExpr.lit sigBytes.length]
      let topic0Store := YulStmt.let_ "__evt_topic0" topic0Expr
      let unindexedHeadSize := (unindexed.map (fun (p, _, _) => eventHeadWordSize p.ty)).foldl (· + ·) 0
      let hasUnindexedDynamicData := unindexed.any (fun (p, _, _) => eventIsDynamicType p.ty)
      let unindexedTailInit :=
        if hasUnindexedDynamicData then
          [YulStmt.let_ "__evt_data_tail" (YulExpr.lit unindexedHeadSize)]
        else
          []
      let rec compileUnindexedStores
          (remaining : List (EventParam × Expr × YulExpr)) (argIdx : Nat) (headOffset : Nat) :
          Except String (List YulStmt) := do
        match remaining with
        | [] => pure []
        | (p, srcExpr, argExpr) :: rest =>
            let curHeadPtr := YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit headOffset]
            let current ←
              match p.ty with
              | ParamType.bytes =>
                  match srcExpr with
                  | Expr.param name =>
                      let lenName := s!"__evt_arg{argIdx}_len"
                      let dstName := s!"__evt_arg{argIdx}_dst"
                      let paddedName := s!"__evt_arg{argIdx}_padded"
                      pure ([
                        YulStmt.expr (YulExpr.call "mstore" [curHeadPtr, YulExpr.ident "__evt_data_tail"]),
                        YulStmt.let_ lenName (YulExpr.ident s!"{name}_length"),
                        YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.ident "__evt_data_tail"]),
                        YulStmt.expr (YulExpr.call "mstore" [YulExpr.ident dstName, YulExpr.ident lenName]),
                      ] ++ dynamicCopyData dynamicSource
                        (YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32])
                        (YulExpr.ident s!"{name}_data_offset")
                        (YulExpr.ident lenName) ++ [
                        YulStmt.let_ paddedName (YulExpr.call "and" [
                          YulExpr.call "add" [YulExpr.ident lenName, YulExpr.lit 31],
                          YulExpr.call "not" [YulExpr.lit 31]
                        ]),
                        YulStmt.expr (YulExpr.call "mstore" [
                          YulExpr.call "add" [
                            YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32],
                            YulExpr.ident lenName
                          ],
                          YulExpr.lit 0
                        ]),
                        YulStmt.assign "__evt_data_tail" (YulExpr.call "add" [
                          YulExpr.ident "__evt_data_tail",
                          YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident paddedName]
                        ])
                      ])
                  | _ =>
                      throw s!"Compilation error: unindexed bytes event param '{p.name}' in event '{eventName}' currently requires direct bytes parameter reference ({issue586Ref})."
              | ParamType.array elemTy =>
                  if elemTy == ParamType.bytes then
                      match srcExpr with
                      | Expr.param name =>
                          let lenName := s!"__evt_arg{argIdx}_len"
                          let dstName := s!"__evt_arg{argIdx}_dst"
                          let headLenName := s!"__evt_arg{argIdx}_head_len"
                          let tailLenName := s!"__evt_arg{argIdx}_tail_len"
                          let loopIndexName := s!"__evt_arg{argIdx}_i"
                          let elemOffsetName := s!"__evt_arg{argIdx}_elem_offset"
                          let elemLenPosName := s!"__evt_arg{argIdx}_elem_len_pos"
                          let elemLenName := s!"__evt_arg{argIdx}_elem_len"
                          let elemDataName := s!"__evt_arg{argIdx}_elem_data"
                          let elemDstName := s!"__evt_arg{argIdx}_elem_dst"
                          let elemPaddedName := s!"__evt_arg{argIdx}_elem_padded"
                          pure ([
                            YulStmt.expr (YulExpr.call "mstore" [curHeadPtr, YulExpr.ident "__evt_data_tail"]),
                            YulStmt.let_ lenName (YulExpr.ident s!"{name}_length"),
                            YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.ident "__evt_data_tail"]),
                            YulStmt.expr (YulExpr.call "mstore" [YulExpr.ident dstName, YulExpr.ident lenName]),
                            YulStmt.let_ headLenName (YulExpr.call "mul" [YulExpr.ident lenName, YulExpr.lit 32]),
                            YulStmt.let_ tailLenName (YulExpr.ident headLenName),
                            YulStmt.for_
                              [YulStmt.let_ loopIndexName (YulExpr.lit 0)]
                              (YulExpr.call "lt" [YulExpr.ident loopIndexName, YulExpr.ident lenName])
                              [YulStmt.assign loopIndexName (YulExpr.call "add" [YulExpr.ident loopIndexName, YulExpr.lit 1])]
                              ([
                                YulStmt.let_ elemOffsetName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
                                  YulExpr.ident s!"{name}_data_offset",
                                  YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit 32]
                                ])),
                                YulStmt.let_ elemLenPosName (YulExpr.call "add" [
                                  YulExpr.ident s!"{name}_data_offset",
                                  YulExpr.ident elemOffsetName
                                ]),
                                YulStmt.let_ elemLenName (dynamicWordLoad dynamicSource (YulExpr.ident elemLenPosName)),
                                YulStmt.let_ elemDataName (YulExpr.call "add" [YulExpr.ident elemLenPosName, YulExpr.lit 32]),
                                YulStmt.expr (YulExpr.call "mstore" [
                                  YulExpr.call "add" [
                                    YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32],
                                    YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit 32]
                                  ],
                                  YulExpr.ident tailLenName
                                ]),
                                YulStmt.let_ elemDstName (YulExpr.call "add" [
                                  YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32],
                                  YulExpr.ident tailLenName
                                ]),
                                YulStmt.expr (YulExpr.call "mstore" [
                                  YulExpr.ident elemDstName,
                                  YulExpr.ident elemLenName
                                ])
                              ] ++ dynamicCopyData dynamicSource
                                (YulExpr.call "add" [YulExpr.ident elemDstName, YulExpr.lit 32])
                                (YulExpr.ident elemDataName)
                                (YulExpr.ident elemLenName) ++ [
                                YulStmt.let_ elemPaddedName (YulExpr.call "and" [
                                  YulExpr.call "add" [YulExpr.ident elemLenName, YulExpr.lit 31],
                                  YulExpr.call "not" [YulExpr.lit 31]
                                ]),
                                YulStmt.expr (YulExpr.call "mstore" [
                                  YulExpr.call "add" [
                                    YulExpr.call "add" [YulExpr.ident elemDstName, YulExpr.lit 32],
                                    YulExpr.ident elemLenName
                                  ],
                                  YulExpr.lit 0
                                ]),
                                YulStmt.assign tailLenName (YulExpr.call "add" [
                                  YulExpr.ident tailLenName,
                                  YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident elemPaddedName]
                                ])
                              ]),
                            YulStmt.assign "__evt_data_tail" (YulExpr.call "add" [
                              YulExpr.ident "__evt_data_tail",
                              YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident tailLenName]
                            ])
                          ])
                      | _ =>
                          throw s!"Compilation error: unindexed dynamic array event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
                  else if indexedDynamicArrayElemSupported elemTy then
                    match srcExpr with
                    | Expr.param name =>
                        let lenName := s!"__evt_arg{argIdx}_len"
                        let dstName := s!"__evt_arg{argIdx}_dst"
                        let elemWordSize := eventHeadWordSize elemTy
                        let byteLenName := s!"__evt_arg{argIdx}_byte_len"
                        let paddedName := s!"__evt_arg{argIdx}_padded"
                        let elemBaseName := s!"__evt_arg{argIdx}_elem_base"
                        let elemOutBaseName := s!"__evt_arg{argIdx}_out_base"
                        let loopIndexName := s!"__evt_arg{argIdx}_i"
                        let leafStores :=
                          (staticCompositeLeafTypeOffsets 0 elemTy).map fun (leafOffset, leafTy) =>
                            let loadExpr := dynamicWordLoad dynamicSource (YulExpr.call "add" [
                              YulExpr.ident elemBaseName,
                              YulExpr.lit leafOffset
                            ])
                            YulStmt.expr (YulExpr.call "mstore" [
                              YulExpr.call "add" [YulExpr.ident elemOutBaseName, YulExpr.lit leafOffset],
                              normalizeEventWord leafTy loadExpr
                            ])
                        pure ([
                          YulStmt.expr (YulExpr.call "mstore" [curHeadPtr, YulExpr.ident "__evt_data_tail"]),
                          YulStmt.let_ lenName (YulExpr.ident s!"{name}_length"),
                          YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.ident "__evt_data_tail"]),
                          YulStmt.expr (YulExpr.call "mstore" [YulExpr.ident dstName, YulExpr.ident lenName]),
                          YulStmt.let_ byteLenName (YulExpr.call "mul" [YulExpr.ident lenName, YulExpr.lit elemWordSize]),
                          YulStmt.for_
                            [YulStmt.let_ loopIndexName (YulExpr.lit 0)]
                            (YulExpr.call "lt" [YulExpr.ident loopIndexName, YulExpr.ident lenName])
                            [YulStmt.assign loopIndexName (YulExpr.call "add" [YulExpr.ident loopIndexName, YulExpr.lit 1])]
                            ([
                              YulStmt.let_ elemBaseName (YulExpr.call "add" [
                                YulExpr.ident s!"{name}_data_offset",
                                YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit elemWordSize]
                              ]),
                              YulStmt.let_ elemOutBaseName (YulExpr.call "add" [
                                YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32],
                                YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit elemWordSize]
                              ])
                            ] ++ leafStores),
                          YulStmt.let_ paddedName (YulExpr.call "and" [
                            YulExpr.call "add" [YulExpr.ident byteLenName, YulExpr.lit 31],
                            YulExpr.call "not" [YulExpr.lit 31]
                          ]),
                          YulStmt.expr (YulExpr.call "mstore" [
                            YulExpr.call "add" [
                              YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32],
                              YulExpr.ident byteLenName
                            ],
                            YulExpr.lit 0
                          ]),
                          YulStmt.assign "__evt_data_tail" (YulExpr.call "add" [
                            YulExpr.ident "__evt_data_tail",
                            YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident paddedName]
                          ])
                        ])
                    | _ =>
                        throw s!"Compilation error: unindexed dynamic array event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
                  else if eventIsDynamicType elemTy then
                    match srcExpr with
                    | Expr.param name =>
                        let dstName := s!"__evt_arg{argIdx}_dst"
                        let srcBase := indexedDynamicBaseOffsetExpr dynamicSource name
                        let (encStmts, encLen) ←
                          compileUnindexedAbiEncode dynamicSource p.ty srcBase (YulExpr.ident dstName) s!"__evt_arg{argIdx}"
                        pure ([
                          YulStmt.expr (YulExpr.call "mstore" [curHeadPtr, YulExpr.ident "__evt_data_tail"]),
                          YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.ident "__evt_data_tail"])
                        ] ++ encStmts ++ [
                          YulStmt.assign "__evt_data_tail" (YulExpr.call "add" [YulExpr.ident "__evt_data_tail", encLen])
                        ])
                    | _ =>
                        throw s!"Compilation error: unindexed dynamic array event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
                  else
                    throw s!"Compilation error: unindexed array event param '{p.name}' in event '{eventName}' has unsupported element type {repr elemTy} ({issue586Ref})."
              | ParamType.fixedArray _ _ | ParamType.tuple _ =>
                  if eventIsDynamicType p.ty then
                    match srcExpr with
                    | Expr.param name =>
                        let dstName := s!"__evt_arg{argIdx}_dst"
                        let srcBase := indexedDynamicBaseOffsetExpr dynamicSource name
                        let (encStmts, encLen) ←
                          compileUnindexedAbiEncode dynamicSource p.ty srcBase (YulExpr.ident dstName) s!"__evt_arg{argIdx}"
                        pure ([
                          YulStmt.expr (YulExpr.call "mstore" [curHeadPtr, YulExpr.ident "__evt_data_tail"]),
                          YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.ident "__evt_data_tail"])
                        ] ++ encStmts ++ [
                          YulStmt.assign "__evt_data_tail" (YulExpr.call "add" [YulExpr.ident "__evt_data_tail", encLen])
                        ])
                    | _ =>
                        throw s!"Compilation error: unindexed dynamic composite event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
                  else
                    match srcExpr with
                    | Expr.param name =>
                        let leaves := staticCompositeLeaves name p.ty
                        let stores := leaves.zipIdx.map fun ((leafTy, leafExpr), wordIdx) =>
                          YulStmt.expr (YulExpr.call "mstore" [
                            YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit (headOffset + wordIdx * 32)],
                            normalizeEventWord leafTy leafExpr
                          ])
                        pure stores
                    | _ =>
                        throw s!"Compilation error: unindexed static composite event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
              | _ =>
                  pure [YulStmt.expr (YulExpr.call "mstore" [curHeadPtr, normalizeEventWord p.ty argExpr])]
            let tail ← compileUnindexedStores rest (argIdx + 1) (headOffset + eventHeadWordSize p.ty)
            pure (current ++ tail)
      let unindexedStores ← compileUnindexedStores unindexed 0 0
      let dataSizeExpr :=
        if hasUnindexedDynamicData then YulExpr.ident "__evt_data_tail" else YulExpr.lit unindexedHeadSize
      let indexedTopicParts ← indexed.zipIdx.mapM fun ((p, srcExpr, argExpr), idx) => do
        match p.ty with
        | ParamType.bytes =>
            match srcExpr with
            | Expr.param name =>
                let topicName := s!"__evt_topic{idx + 1}"
                let hashStmts :=
                  dynamicCopyData dynamicSource
                    (YulExpr.ident "__evt_ptr")
                    (YulExpr.ident s!"{name}_data_offset")
                    (YulExpr.ident s!"{name}_length") ++ [
                  YulStmt.let_ topicName (YulExpr.call "keccak256" [
                    YulExpr.ident "__evt_ptr",
                    YulExpr.ident s!"{name}_length"
                  ])
                ]
                pure (hashStmts, YulExpr.ident topicName)
            | _ =>
                throw s!"Compilation error: indexed bytes event param '{p.name}' in event '{eventName}' currently requires direct bytes parameter reference ({issue586Ref})."
        | ParamType.array elemTy =>
            match elemTy with
            | ParamType.bytes =>
                match srcExpr with
                | Expr.param name =>
                    let topicName := s!"__evt_topic{idx + 1}"
                    let tailLenName := s!"__evt_arg{idx}_tail_len"
                    let loopIndexName := s!"__evt_arg{idx}_i"
                    let elemOffsetName := s!"__evt_arg{idx}_elem_offset"
                    let elemLenPosName := s!"__evt_arg{idx}_elem_len_pos"
                    let elemLenName := s!"__evt_arg{idx}_elem_len"
                    let elemDataName := s!"__evt_arg{idx}_elem_data"
                    let elemDstName := s!"__evt_arg{idx}_elem_dst"
                    let elemPaddedName := s!"__evt_arg{idx}_elem_padded"
                    let hashStmts := [
                      YulStmt.let_ tailLenName (YulExpr.lit 0),
                      YulStmt.for_
                        [YulStmt.let_ loopIndexName (YulExpr.lit 0)]
                        (YulExpr.call "lt" [YulExpr.ident loopIndexName, YulExpr.ident s!"{name}_length"])
                        [YulStmt.assign loopIndexName (YulExpr.call "add" [YulExpr.ident loopIndexName, YulExpr.lit 1])]
                        ([
                          YulStmt.let_ elemOffsetName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
                            YulExpr.ident s!"{name}_data_offset",
                            YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit 32]
                          ])),
                          YulStmt.let_ elemLenPosName (YulExpr.call "add" [
                            YulExpr.ident s!"{name}_data_offset",
                            YulExpr.ident elemOffsetName
                          ]),
                          YulStmt.let_ elemLenName (dynamicWordLoad dynamicSource (YulExpr.ident elemLenPosName)),
                          YulStmt.let_ elemDataName (YulExpr.call "add" [YulExpr.ident elemLenPosName, YulExpr.lit 32]),
                          YulStmt.let_ elemDstName (YulExpr.call "add" [
                            YulExpr.ident "__evt_ptr",
                            YulExpr.ident tailLenName
                          ])
                        ] ++ dynamicCopyData dynamicSource
                          (YulExpr.ident elemDstName)
                          (YulExpr.ident elemDataName)
                          (YulExpr.ident elemLenName) ++ [
                          YulStmt.let_ elemPaddedName (YulExpr.call "and" [
                            YulExpr.call "add" [YulExpr.ident elemLenName, YulExpr.lit 31],
                            YulExpr.call "not" [YulExpr.lit 31]
                          ]),
                          YulStmt.expr (YulExpr.call "mstore" [
                            YulExpr.call "add" [YulExpr.ident elemDstName, YulExpr.ident elemLenName],
                            YulExpr.lit 0
                          ]),
                          YulStmt.assign tailLenName (YulExpr.call "add" [
                            YulExpr.ident tailLenName,
                            YulExpr.ident elemPaddedName
                          ])
                        ]),
                      YulStmt.let_ topicName (YulExpr.call "keccak256" [
                        YulExpr.ident "__evt_ptr",
                        YulExpr.ident tailLenName
                      ])
                    ]
                    pure (hashStmts, YulExpr.ident topicName)
                | _ =>
                    throw s!"Compilation error: indexed dynamic array event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
            | _ =>
                if indexedDynamicArrayElemSupported elemTy then
                  match srcExpr with
                  | Expr.param name =>
                      let topicName := s!"__evt_topic{idx + 1}"
                      let byteLenName := s!"__evt_arg{idx}_byte_len"
                      let elemWordSize := eventHeadWordSize elemTy
                      let elemBaseName := s!"__evt_arg{idx}_elem_base"
                      let elemOutBaseName := s!"__evt_arg{idx}_out_base"
                      let loopIndexName := s!"__evt_arg{idx}_i"
                      let leafStores :=
                        (staticCompositeLeafTypeOffsets 0 elemTy).map fun (leafOffset, leafTy) =>
                          let loadExpr := dynamicWordLoad dynamicSource (YulExpr.call "add" [
                            YulExpr.ident elemBaseName,
                            YulExpr.lit leafOffset
                          ])
                          YulStmt.expr (YulExpr.call "mstore" [
                            YulExpr.call "add" [
                              YulExpr.ident elemOutBaseName,
                              YulExpr.lit leafOffset
                            ],
                            normalizeEventWord leafTy loadExpr
                          ])
                      let hashStmts := [
                        YulStmt.let_ byteLenName (YulExpr.call "mul" [
                          YulExpr.ident s!"{name}_length",
                          YulExpr.lit elemWordSize
                        ]),
                        YulStmt.for_
                          [YulStmt.let_ loopIndexName (YulExpr.lit 0)]
                          (YulExpr.call "lt" [YulExpr.ident loopIndexName, YulExpr.ident s!"{name}_length"])
                          [YulStmt.assign loopIndexName (YulExpr.call "add" [YulExpr.ident loopIndexName, YulExpr.lit 1])]
                          ([
                            YulStmt.let_ elemBaseName (YulExpr.call "add" [
                              YulExpr.ident s!"{name}_data_offset",
                              YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit elemWordSize]
                            ]),
                            YulStmt.let_ elemOutBaseName (YulExpr.call "add" [
                              YulExpr.ident "__evt_ptr",
                              YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit elemWordSize]
                            ])
                          ] ++ leafStores),
                        YulStmt.let_ topicName (YulExpr.call "keccak256" [
                          YulExpr.ident "__evt_ptr",
                          YulExpr.ident byteLenName
                        ])
                      ]
                      pure (hashStmts, YulExpr.ident topicName)
                  | _ =>
                      throw s!"Compilation error: indexed dynamic array event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
                else if eventIsDynamicType elemTy then
                  match srcExpr with
                  | Expr.param name =>
                      let topicName := s!"__evt_topic{idx + 1}"
                      let srcBase := indexedDynamicBaseOffsetExpr dynamicSource name
                      let (encodeStmts, encodeLen) ←
                        compileIndexedInPlaceEncoding dynamicSource p.ty srcBase (YulExpr.ident "__evt_ptr") s!"__evt_arg{idx}_indexed"
                      pure (encodeStmts ++ [YulStmt.let_ topicName (YulExpr.call "keccak256" [
                        YulExpr.ident "__evt_ptr",
                        encodeLen
                      ])], YulExpr.ident topicName)
                  | _ =>
                      throw s!"Compilation error: indexed dynamic array event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
                else
                  throw s!"Compilation error: indexed array event param '{p.name}' in event '{eventName}' has unsupported element type {repr elemTy} ({issue586Ref})."
        | ParamType.fixedArray _ _ | ParamType.tuple _ =>
            if eventIsDynamicType p.ty then
              match srcExpr with
              | Expr.param name =>
                  let topicName := s!"__evt_topic{idx + 1}"
                  let srcBase := indexedDynamicBaseOffsetExpr dynamicSource name
                  let (encodeStmts, encodeLen) ←
                    compileIndexedInPlaceEncoding dynamicSource p.ty srcBase (YulExpr.ident "__evt_ptr") s!"__evt_arg{idx}_indexed"
                  pure (encodeStmts ++ [YulStmt.let_ topicName (YulExpr.call "keccak256" [
                    YulExpr.ident "__evt_ptr",
                    encodeLen
                  ])], YulExpr.ident topicName)
              | _ =>
                  throw s!"Compilation error: indexed dynamic composite event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
            else
              match srcExpr with
              | Expr.param name =>
                  let topicName := s!"__evt_topic{idx + 1}"
                  let leaves := staticCompositeLeaves name p.ty
                  let stores := leaves.zipIdx.map fun ((leafTy, leafExpr), wordIdx) =>
                    YulStmt.expr (YulExpr.call "mstore" [
                      YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit (wordIdx * 32)],
                      normalizeEventWord leafTy leafExpr
                    ])
                  pure (stores ++ [YulStmt.let_ topicName (YulExpr.call "keccak256" [
                    YulExpr.ident "__evt_ptr",
                    YulExpr.lit (eventHeadWordSize p.ty)
                  ])], YulExpr.ident topicName)
              | _ =>
                  throw s!"Compilation error: indexed static composite event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
        | ParamType.address =>
            pure ([], YulExpr.call "and" [argExpr, YulExpr.hex addressMask])
        | ParamType.bool =>
            pure ([], yulToBool argExpr)
        | _ =>
            pure ([], argExpr)
      let indexedTopicStmts := indexedTopicParts.flatMap (·.1)
      let topicExprs := [YulExpr.ident "__evt_topic0"] ++ indexedTopicParts.map (·.2)
      let logFn := match indexed.length with
        | 0 => "log1"
        | 1 => "log2"
        | 2 => "log3"
        | _ => "log4"
      let logArgs := [YulExpr.ident "__evt_ptr", dataSizeExpr] ++ topicExprs
      let logStmt := YulStmt.expr (YulExpr.call logFn logArgs)
      pure [YulStmt.block ([storePtr] ++ sigStores ++ [topic0Store] ++ indexedTopicStmts ++ unindexedTailInit ++ unindexedStores ++ [logStmt])]

  | Stmt.internalCall functionName args => do
      -- Internal function call as statement (#181)
      let argExprs ← compileExprList fields dynamicSource args
      pure [YulStmt.expr (YulExpr.call (internalFunctionYulName functionName) argExprs)]
  | Stmt.internalCallAssign names functionName args => do
      let argExprs ← compileExprList fields dynamicSource args
      pure [YulStmt.letMany names (YulExpr.call (internalFunctionYulName functionName) argExprs)]
  | Stmt.externalCallBind resultVars externalName args => do
      let argExprs ← compileExprList fields dynamicSource args
      pure [YulStmt.letMany resultVars (YulExpr.call externalName argExprs)]
  -- NOTE: safeTransfer, safeTransferFrom, externalCallWithReturn, callback, ecrecover
  -- have been removed. Use Stmt.ecm with the appropriate module from Compiler/Modules/.
  | Stmt.ecm mod args => do
      if args.length != mod.numArgs then
        throw s!"ECM '{mod.name}': expected {mod.numArgs} arguments, got {args.length}"
      let compiledArgs ← compileExprList fields dynamicSource args
      let ctx : ECM.CompilationContext := {
        isDynamicFromCalldata := dynamicSource == .calldata
      }
      mod.compile ctx compiledArgs
  | Stmt.returnValues values => do
      if isInternal then
        if values.length != internalRetNames.length then
          throw s!"Compilation error: internal return arity mismatch: expected {internalRetNames.length}, got {values.length}"
        else
          let compiled ← compileExprList fields dynamicSource values
          let assigns := (internalRetNames.zip compiled).map fun (name, valueExpr) =>
            YulStmt.assign name valueExpr
          pure (assigns ++ [YulStmt.leave])
      else if values.isEmpty then
        pure [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 0])]
      else
        let compiled ← compileExprList fields dynamicSource values
        let stores := (compiled.zipIdx.map fun (valueExpr, idx) =>
          YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit (idx * 32), valueExpr]))
        pure (stores ++ [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit (values.length * 32)])])
  | Stmt.returnArray name => do
      let lenIdent := YulExpr.ident s!"{name}_length"
      let dataOffset := YulExpr.ident s!"{name}_data_offset"
      let byteLen := YulExpr.call "mul" [lenIdent, YulExpr.lit 32]
      pure ([
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 32]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, lenIdent]),
      ] ++ dynamicCopyData dynamicSource (YulExpr.lit 64) dataOffset byteLen ++ [
        YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.call "add" [YulExpr.lit 64, byteLen]])
      ])
  | Stmt.returnBytes name => do
      let lenIdent := YulExpr.ident s!"{name}_length"
      let dataOffset := YulExpr.ident s!"{name}_data_offset"
      let tailOffset := YulExpr.call "add" [YulExpr.lit 64, lenIdent]
      let paddedLen :=
        YulExpr.call "and" [
          YulExpr.call "add" [lenIdent, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ]
      pure ([
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 32]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, lenIdent]),
      ] ++ dynamicCopyData dynamicSource (YulExpr.lit 64) dataOffset lenIdent ++ [
        YulStmt.expr (YulExpr.call "mstore" [tailOffset, YulExpr.lit 0]),
        YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.call "add" [YulExpr.lit 64, paddedLen]])
      ])
  | Stmt.returnStorageWords name => do
      let lenIdent := YulExpr.ident s!"{name}_length"
      let dataOffset := YulExpr.ident s!"{name}_data_offset"
      pure [
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 32]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, lenIdent]),
        YulStmt.for_
          [YulStmt.let_ "__i" (YulExpr.lit 0)]
          (YulExpr.call "lt" [YulExpr.ident "__i", lenIdent])
          [YulStmt.assign "__i" (YulExpr.call "add" [YulExpr.ident "__i", YulExpr.lit 1])]
          [
            YulStmt.let_ "__slot" (dynamicWordLoad dynamicSource (YulExpr.call "add" [
              dataOffset,
              YulExpr.call "mul" [YulExpr.ident "__i", YulExpr.lit 32]
            ])),
            YulStmt.expr (YulExpr.call "mstore" [
              YulExpr.call "add" [YulExpr.lit 64, YulExpr.call "mul" [YulExpr.ident "__i", YulExpr.lit 32]],
              YulExpr.call "sload" [YulExpr.ident "__slot"]
            ])
          ],
        YulStmt.expr (YulExpr.call "return" [
          YulExpr.lit 0,
          YulExpr.call "add" [YulExpr.lit 64, YulExpr.call "mul" [lenIdent, YulExpr.lit 32]]
        ])
      ]
  | Stmt.mstore offset value => do
      pure [YulStmt.expr (YulExpr.call "mstore" [
        ← compileExpr fields dynamicSource offset,
        ← compileExpr fields dynamicSource value
      ])]
  | Stmt.calldatacopy destOffset sourceOffset size => do
      pure [YulStmt.expr (YulExpr.call "calldatacopy" [
        ← compileExpr fields dynamicSource destOffset,
        ← compileExpr fields dynamicSource sourceOffset,
        ← compileExpr fields dynamicSource size
      ])]
  | Stmt.returndataCopy destOffset sourceOffset size => do
      pure [YulStmt.expr (YulExpr.call "returndatacopy" [
        ← compileExpr fields dynamicSource destOffset,
        ← compileExpr fields dynamicSource sourceOffset,
        ← compileExpr fields dynamicSource size
      ])]
  | Stmt.revertReturndata =>
      pure [YulStmt.block [
        YulStmt.let_ "__returndata_size" (YulExpr.call "returndatasize" []),
        YulStmt.expr (YulExpr.call "returndatacopy" [
          YulExpr.lit 0,
          YulExpr.lit 0,
          YulExpr.ident "__returndata_size"
        ]),
        YulStmt.expr (YulExpr.call "revert" [
          YulExpr.lit 0,
          YulExpr.ident "__returndata_size"
        ])
      ]]
  | Stmt.rawLog topics dataOffset dataSize => do
      if topics.length > 4 then
        throw s!"Compilation error: rawLog supports at most 4 topics (log0–log4), got {topics.length}"
      let topicExprs ← compileExprList fields dynamicSource topics
      let offsetExpr ← compileExpr fields dynamicSource dataOffset
      let sizeExpr ← compileExpr fields dynamicSource dataSize
      let logFn := s!"log{topics.length}"
      pure [YulStmt.expr (YulExpr.call logFn ([offsetExpr, sizeExpr] ++ topicExprs))]
end

private def isScalarParamType : ParamType → Bool
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 => true
  | _ => false

private def genDynamicParamLoads
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr) (headSize : Nat)
    (baseOffset : Nat) (name : String) (ty : ParamType) (headOffset : Nat) :
    List YulStmt :=
  let offsetLoad := YulStmt.let_ s!"{name}_offset"
    (loadWord (YulExpr.lit headOffset))
  let relativeOffset := YulExpr.ident s!"{name}_offset"
  let absoluteOffsetExpr :=
    if baseOffset == 0 then
      relativeOffset
    else
      YulExpr.call "add" [YulExpr.lit baseOffset, relativeOffset]
  let absoluteOffsetName := s!"{name}_abs_offset"
  let absoluteOffsetLoad := YulStmt.let_ absoluteOffsetName absoluteOffsetExpr
  let absoluteOffset := YulExpr.ident absoluteOffsetName
  let offsetBoundsCheck := YulStmt.if_ (YulExpr.call "lt" [relativeOffset, YulExpr.lit headSize]) [
    YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
  ]
  let absoluteBoundsCheck := YulStmt.if_ (YulExpr.call "gt" [
    absoluteOffset,
    YulExpr.call "sub" [sizeExpr, YulExpr.lit 32]
  ]) [
    YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
  ]
  let lengthLoad := YulStmt.let_ s!"{name}_length"
    (loadWord absoluteOffset)
  let tailHeadEndName := s!"{name}_tail_head_end"
  let tailHeadEndLoad := YulStmt.let_ tailHeadEndName
    (YulExpr.call "add" [absoluteOffset, YulExpr.lit 32])
  let tailRemainingName := s!"{name}_tail_remaining"
  let tailRemainingLoad := YulStmt.let_ tailRemainingName
    (YulExpr.call "sub" [sizeExpr, YulExpr.ident tailHeadEndName])
  let lengthBoundsCheck :=
    match ty with
    | ParamType.bytes =>
        [YulStmt.if_ (YulExpr.call "gt" [
            YulExpr.ident s!"{name}_length",
            YulExpr.ident tailRemainingName
          ]) [
            YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
          ]]
    | ParamType.array _ =>
        [YulStmt.if_ (YulExpr.call "gt" [
            YulExpr.ident s!"{name}_length",
            YulExpr.call "div" [YulExpr.ident tailRemainingName, YulExpr.lit 32]
          ]) [
            YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
          ]]
    | _ => []
  let dataOffsetLoad := YulStmt.let_ s!"{name}_data_offset"
    (YulExpr.ident tailHeadEndName)
  [offsetLoad, offsetBoundsCheck, absoluteOffsetLoad, absoluteBoundsCheck, lengthLoad, tailHeadEndLoad, tailRemainingLoad]
    ++ lengthBoundsCheck ++ [dataOffsetLoad]

private def genScalarLoad
    (loadWord : YulExpr → YulExpr) (name : String) (ty : ParamType) (offset : Nat) :
    List YulStmt :=
  let load := loadWord (YulExpr.lit offset)
  match ty with
  | ParamType.uint256 =>
      [YulStmt.let_ name load]
  | ParamType.uint8 =>
      [YulStmt.let_ name (YulExpr.call "and" [load, YulExpr.lit 255])]
  | ParamType.bytes32 =>
      [YulStmt.let_ name load]
  | ParamType.address =>
      [YulStmt.let_ name (YulExpr.call "and" [
        load,
        YulExpr.hex addressMask
      ])]
  | ParamType.bool =>
      let boolWord := s!"__abi_bool_word_{offset}"
      [ YulStmt.let_ boolWord load
      , YulStmt.if_ (YulExpr.call "iszero" [
          YulExpr.call "or" [
            YulExpr.call "eq" [YulExpr.ident boolWord, YulExpr.lit 0],
            YulExpr.call "eq" [YulExpr.ident boolWord, YulExpr.lit 1]
          ]
        ]) [
          YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
        ]
      , YulStmt.let_ name (YulExpr.call "iszero" [YulExpr.call "iszero" [
          YulExpr.ident boolWord
        ]])
      ]
  | _ => []

private partial def genStaticTypeLoads
    (loadWord : YulExpr → YulExpr) (name : String) (ty : ParamType) (offset : Nat) :
    List YulStmt :=
  match ty with
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      genScalarLoad loadWord name ty offset
  | ParamType.fixedArray elemTy n =>
      (List.range n).flatMap fun i =>
        genStaticTypeLoads loadWord s!"{name}_{i}" elemTy (offset + i * paramHeadSize elemTy)
  | ParamType.tuple elemTys =>
      let rec go (tys : List ParamType) (idx : Nat) (curOffset : Nat) : List YulStmt :=
        match tys with
        | [] => []
        | elemTy :: rest =>
            let elemName := s!"{name}_{idx}"
            let here := genStaticTypeLoads loadWord elemName elemTy curOffset
            here ++ go rest (idx + 1) (curOffset + paramHeadSize elemTy)
      go elemTys 0 offset
  | _ => []

private def genParamLoadsFrom
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headStart : Nat) (baseOffset : Nat) (params : List Param) :
    List YulStmt :=
  let headSize := (params.map (fun p => paramHeadSize p.ty)).foldl (· + ·) 0
  let minInputSizeCheck :=
    YulStmt.if_ (YulExpr.call "lt" [sizeExpr, YulExpr.lit (baseOffset + headSize)]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
  let rec go (paramList : List Param) (headOffset : Nat) : List YulStmt :=
    match paramList with
    | [] => []
    | param :: rest =>
      let stmts := match param.ty with
        | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
          genScalarLoad loadWord param.name param.ty headOffset
        | ParamType.tuple elemTypes =>
          if isDynamicParamType param.ty then
            genDynamicParamLoads loadWord sizeExpr headSize baseOffset param.name param.ty headOffset
          else
            genStaticTypeLoads loadWord param.name (ParamType.tuple elemTypes) headOffset
        | ParamType.array _ =>
          genDynamicParamLoads loadWord sizeExpr headSize baseOffset param.name param.ty headOffset
        | ParamType.fixedArray _ n =>
          -- Static fixed arrays are decoded inline recursively (including nested tuple members).
          -- For scalar element arrays we preserve `<name>` as an alias to `<name>_0`.
          if isDynamicParamType param.ty then
            genDynamicParamLoads loadWord sizeExpr headSize baseOffset param.name param.ty headOffset
          else
            let staticLoads := genStaticTypeLoads loadWord param.name param.ty headOffset
            if n == 0 then staticLoads else
              -- Backward compatibility: keep `<name>` bound to first element for scalar fixed arrays.
              let firstAlias := match param.ty with
                | ParamType.fixedArray elemTy _ =>
                    if isScalarParamType elemTy then
                      [YulStmt.let_ param.name (YulExpr.ident s!"{param.name}_0")]
                    else
                      []
                | _ => []
              staticLoads ++ firstAlias
        | ParamType.bytes =>
          genDynamicParamLoads loadWord sizeExpr headSize baseOffset param.name param.ty headOffset
      stmts ++ go rest (headOffset + paramHeadSize param.ty)
  minInputSizeCheck :: go params headStart

-- Generate parameter loading code (from calldata)
def genParamLoads (params : List Param) : List YulStmt :=
  genParamLoadsFrom (fun pos => YulExpr.call "calldataload" [pos]) (YulExpr.call "calldatasize" []) 4 4 params

private def pickFreshInternalRetName (usedNames : List String) (idx : Nat) : String :=
  pickFreshName s!"__ret{idx}" usedNames

private def freshInternalRetNames (returns : List ParamType) (usedNames : List String) : List String :=
  let (_, namesRev) := returns.zipIdx.foldl
    (fun (acc : List String × List String) (_retTy, idx) =>
      let (used, names) := acc
      let fresh := pickFreshInternalRetName used idx
      (fresh :: used, fresh :: names))
    (usedNames, [])
  namesRev.reverse

-- Compile internal function to a Yul function definition (#181)
def compileInternalFunction (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (spec : FunctionSpec) :
    Except String YulStmt := do
  validateFunctionSpec spec
  let returns ← functionReturns spec
  let paramNames := spec.params.map (·.name)
  let usedNames := paramNames ++ collectStmtListBindNames spec.body
  let retNames := freshInternalRetNames returns usedNames
  let bodyStmts ← compileStmtList fields events errors .calldata retNames true
    (paramNames ++ retNames) spec.body
  pure (YulStmt.funcDef (internalFunctionYulName spec.name) paramNames retNames bodyStmts)

-- Compile function spec to IR function
def compileFunctionSpec (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec) :
    Except String IRFunction := do
  validateFunctionSpec spec
  let returns ← functionReturns spec
  let paramLoads := genParamLoads spec.params
  let bodyStmts ← compileStmtList fields events errors .calldata [] false
    (spec.params.map (·.name)) spec.body
  let allStmts := paramLoads ++ bodyStmts
  let retType := match returns with
    | [single] => single.toIRType
    | _ => IRType.unit
  return {
    name := spec.name
    selector := selector
    params := spec.params.map Param.toIRParam
    ret := retType
    payable := spec.isPayable
    body := allStmts
  }

private def compileSpecialEntrypoint (fields : List Field) (events : List EventDef)
    (errors : List ErrorDef) (spec : FunctionSpec) :
    Except String IREntrypoint := do
  let bodyChunks ← compileStmtList fields events errors .calldata [] false [] spec.body
  pure {
    payable := spec.isPayable
    body := bodyChunks
  }

private def pickUniqueFunctionByName (name : String) (funcs : List FunctionSpec) :
    Except String (Option FunctionSpec) :=
  match funcs.filter (·.name == name) with
  | [] => pure none
  | [single] => pure (some single)
  | _ => throw s!"Compilation error: multiple '{name}' entrypoints are not allowed ({issue586Ref})"

-- Check if contract uses mappings
def usesMapping (fields : List Field) : Bool :=
  fields.any fun f => isMapping fields f.name

private def constructorArgAliases (params : List Param) : List YulStmt :=
  let rec go (ps : List Param) (idx : Nat) (headOffset : Nat) : List YulStmt :=
    match ps with
    | [] => []
    | param :: rest =>
        let source := if isDynamicParamType param.ty then
          YulExpr.ident s!"{param.name}_offset"
        else
          match param.ty with
          | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
              YulExpr.ident param.name
          | _ =>
              YulExpr.call "mload" [YulExpr.lit headOffset]
        let alias := YulStmt.let_ s!"arg{idx}" source
        alias :: go rest (idx + 1) (headOffset + paramHeadSize param.ty)
  go params 0 0

-- Generate constructor argument loading code (from appended initcode args)
def genConstructorArgLoads (params : List Param) : List YulStmt :=
  if params.isEmpty then []
  else
    let argsOffset := YulExpr.call "add" [
      YulExpr.call "dataoffset" [YulExpr.str "runtime"],
      YulExpr.call "datasize" [YulExpr.str "runtime"]
    ]
    let initcodeArgCopy := [
      YulStmt.let_ "argsOffset" argsOffset,
      YulStmt.let_ "argsSize"
        (YulExpr.call "sub" [YulExpr.call "codesize" [], YulExpr.ident "argsOffset"]),
      YulStmt.expr (YulExpr.call "codecopy" [YulExpr.lit 0, YulExpr.ident "argsOffset", YulExpr.ident "argsSize"])
    ]
    let paramLoads := genParamLoadsFrom (fun pos => YulExpr.call "mload" [pos]) (YulExpr.ident "argsSize") 0 0 params
    initcodeArgCopy ++ paramLoads ++ constructorArgAliases params

-- Compile deploy code (constructor)
-- Note: Don't append datacopy/return here - Codegen.deployCode does that
def compileConstructor (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (ctor : Option ConstructorSpec) :
    Except String (List YulStmt) := do
  match ctor with
  | none => return []
  | some spec =>
    let argLoads := genConstructorArgLoads spec.params
    let bodyChunks ← compileStmtList fields events errors .memory [] false [] spec.body
    return argLoads ++ bodyChunks

-- Main compilation function
-- NOTE: this is the pure core compiler and does *not* verify canonical
-- selector/signature correspondence (it only checks count/duplicates).
-- Use `Compiler.Selector.compileChecked` on caller-provided selector lists.
-- WARNING: Order matters! If selector list is reordered but function list isn't,
-- functions will be mapped to wrong selectors with no runtime error.

private def validateErrorDef (err : ErrorDef) : Except String Unit := do
  for ty in err.params do
    if !supportedCustomErrorParamType ty then
      throw s!"Compilation error: custom error '{err.name}' uses unsupported dynamic parameter type {repr ty} ({issue586Ref}). Use uint256/address/bool/bytes32/bytes parameters."

private def validateEventDef (eventDef : EventDef) : Except String Unit := do
  let indexedCount := eventDef.params.foldl
    (fun acc p => if p.kind == EventParamKind.indexed then acc + 1 else acc)
    0
  if indexedCount > 3 then
    throw s!"Compilation error: event '{eventDef.name}' has {indexedCount} indexed params; max is 3"

private def ensureContractIdentifier (kind name : String) : Except String Unit := do
  match Compiler.ensureValidIdentifier kind name with
  | .ok _ => pure ()
  | .error err => throw s!"Compilation error: {err}"

private def validateIdentifierShapes (spec : CompilationModel) : Except String Unit := do
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

def compile (spec : CompilationModel) (selectors : List Nat) : Except String IRContract := do
  validateIdentifierShapes spec
  match firstInvalidSlotAliasRange spec.slotAliasRanges with
  | some (idx, range) =>
      throw s!"Compilation error: slotAliasRanges[{idx}] has invalid source interval {range.sourceStart}..{range.sourceEnd} in {spec.name} ({issue623Ref}). slotAliasRanges require sourceStart <= sourceEnd."
  | none =>
      pure ()
  match firstSlotAliasSourceOverlap spec.slotAliasRanges with
  | some (idxA, a, idxB, b) =>
      throw s!"Compilation error: slotAliasRanges[{idxA}]={a.sourceStart}..{a.sourceEnd} and slotAliasRanges[{idxB}]={b.sourceStart}..{b.sourceEnd} overlap in source slots in {spec.name} ({issue623Ref}). Ensure slotAliasRanges source intervals are disjoint."
  | none =>
      pure ()
  let fields := applySlotAliasRanges spec.fields spec.slotAliasRanges
  let externalFns := spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)
  let internalFns := spec.functions.filter (·.isInternal)
  match firstInternalDynamicParam spec.functions with
  | some (fnName, paramName, ty) =>
      throw s!"Compilation error: internal function '{fnName}' parameter '{paramName}' has dynamic type {repr ty}, which is currently unsupported ({issue753Ref}). Internal dynamic ABI lowering is not implemented yet."
  | none =>
      pure ()
  match firstDuplicateFunctionParamName spec.functions with
  | some (fnName, dup) =>
      throw s!"Compilation error: duplicate parameter name '{dup}' in function '{fnName}'"
  | none =>
      pure ()
  match firstDuplicateConstructorParamName spec.constructor with
  | some dup =>
      throw s!"Compilation error: duplicate parameter name '{dup}' in constructor"
  | none =>
      pure ()
  for fn in spec.functions do
    validateFunctionSpec fn
    validateInteropFunctionSpec fn
    validateSpecialEntrypointSpec fn
    validateEventArgShapesInFunction fn spec.events
    validateCustomErrorArgShapesInFunction fn spec.errors
    validateInternalCallShapesInFunction spec.functions fn
    validateExternalCallTargetsInFunction spec.externals fn
  validateConstructorSpec spec.constructor
  validateInteropConstructorSpec spec.constructor
  validateExternalCallTargetsInConstructor spec.externals spec.constructor
  match spec.constructor with
  | none => pure ()
  | some ctor => do
      ctor.body.forM (validateEventArgShapesInStmt "constructor" ctor.params spec.events)
      ctor.body.forM (validateCustomErrorArgShapesInStmt "constructor" ctor.params spec.errors)
      ctor.body.forM (validateInternalCallShapesInStmt spec.functions "constructor")
  for ext in spec.externals do
    let _ ← externalFunctionReturns ext
    validateInteropExternalSpec ext
  match firstDuplicateName (spec.functions.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate function name '{dup}' in {spec.name}"
  | none =>
      pure ()
  match firstDuplicateName (spec.errors.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate custom error declaration '{dup}'"
  | none =>
      pure ()
  match firstDuplicateName (spec.fields.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate field name '{dup}' in {spec.name}"
  | none =>
      pure ()
  match firstInvalidPackedBits spec.fields with
  | some (fieldName, packed) =>
      throw s!"Compilation error: field '{fieldName}' has invalid packedBits offset={packed.offset} width={packed.width} in {spec.name} ({issue623Ref}). Require 0 < width <= 256, offset < 256, and offset + width <= 256."
  | none =>
      pure ()
  match firstMappingPackedBits spec.fields with
  | some fieldName =>
      throw s!"Compilation error: field '{fieldName}' is a mapping and cannot declare packedBits in {spec.name} ({issue623Ref}). Packed subfields are only supported for value-word fields."
  | none =>
      pure ()
  firstInvalidStructField spec.fields
  match firstFieldWriteSlotConflict fields with
  | some (slot, existingField, conflictingField) =>
      throw s!"Compilation error: storage slot {slot} has overlapping write ranges for '{existingField}' and '{conflictingField}' in {spec.name} ({issue623Ref}). Ensure full-slot writes are unique and packed bit ranges are disjoint per slot."
  | none =>
      pure ()
  match firstInvalidReservedRange spec.reservedSlotRanges with
  | some (idx, range) =>
      throw s!"Compilation error: reservedSlotRanges[{idx}] has invalid interval {range.start}..{range.end_} in {spec.name} ({issue623Ref}). Reserved slot range start must be <= end."
  | none =>
      pure ()
  match firstReservedRangeOverlap spec.reservedSlotRanges with
  | some (idxA, a, idxB, b) =>
      throw s!"Compilation error: reserved slot ranges reservedSlotRanges[{idxA}]={a.start}..{a.end_} and reservedSlotRanges[{idxB}]={b.start}..{b.end_} overlap in {spec.name} ({issue623Ref}). Ensure reserved ranges are disjoint."
  | none =>
      pure ()
  match firstReservedSlotWriteConflict fields spec.reservedSlotRanges with
  | some (slot, ownerName, rangeIdx, range) =>
      throw s!"Compilation error: field write slot {slot} ('{ownerName}') overlaps reservedSlotRanges[{rangeIdx}]={range.start}..{range.end_} in {spec.name} ({issue623Ref}). Adjust field slot/aliasSlots or reservedSlotRanges."
  | none =>
      pure ()
  match firstDuplicateName (spec.events.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate event name '{dup}' in {spec.name}"
  | none =>
      pure ()
  for eventDef in spec.events do
    validateEventDef eventDef
  match firstDuplicateEventParamName spec.events with
  | some (evName, dup) =>
      throw s!"Compilation error: duplicate parameter name '{dup}' in event '{evName}'"
  | none =>
      pure ()
  match firstDuplicateName (spec.externals.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate external declaration '{dup}' in {spec.name}"
  | none =>
      pure ()
  let mappingHelpersRequired := usesMapping fields
  let arrayHelpersRequired := contractUsesArrayElement spec
  match firstReservedExternalCollision spec mappingHelpersRequired arrayHelpersRequired with
  | some name =>
      if name.startsWith internalFunctionPrefix then
        throw s!"Compilation error: external declaration '{name}' uses reserved prefix '{internalFunctionPrefix}' ({issue756Ref})."
      else
        throw s!"Compilation error: external declaration '{name}' collides with compiler-generated/reserved symbol '{name}' ({issue756Ref}). Rename the external wrapper."
  | none =>
      pure ()
  for err in spec.errors do
    validateErrorDef err
  let fallbackSpec ← pickUniqueFunctionByName "fallback" spec.functions
  let receiveSpec ← pickUniqueFunctionByName "receive" spec.functions
  if externalFns.length != selectors.length then
    throw s!"Selector count mismatch for {spec.name}: {selectors.length} selectors for {externalFns.length} external functions"
  match firstDuplicateSelector selectors with
  | some dup =>
      let names := selectorNames spec selectors dup
      let nameStr := if names.isEmpty then "<unknown>" else String.intercalate ", " names
      throw s!"Selector collision in {spec.name}: {dup} assigned to {nameStr}"
  | none => pure ()
  let functions ← (externalFns.zip selectors).mapM fun (fnSpec, sel) =>
    compileFunctionSpec fields spec.events spec.errors sel fnSpec
  -- Compile internal functions as Yul function definitions (#181)
  let internalFuncDefs ← internalFns.mapM (compileInternalFunction fields spec.events spec.errors)
  let arrayElementHelpers :=
    if arrayHelpersRequired then
      [checkedArrayElementCalldataHelper, checkedArrayElementMemoryHelper]
    else
      []
  let fallbackEntrypoint ← fallbackSpec.mapM (compileSpecialEntrypoint fields spec.events spec.errors)
  let receiveEntrypoint ← receiveSpec.mapM (compileSpecialEntrypoint fields spec.events spec.errors)
  return {
    name := spec.name
    deploy := (← compileConstructor fields spec.events spec.errors spec.constructor)
    constructorPayable := spec.constructor.map (·.isPayable) |>.getD false
    functions := functions
    fallbackEntrypoint := fallbackEntrypoint
    receiveEntrypoint := receiveEntrypoint
    usesMapping := mappingHelpersRequired
    internalFunctions := arrayElementHelpers ++ internalFuncDefs
  }

end Compiler.CompilationModel
