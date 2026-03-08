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
import Compiler.CompilationModel.LogicalPurity
import Compiler.CompilationModel.MappingWrites
import Compiler.CompilationModel.ScopeValidation
import Compiler.CompilationModel.UsageAnalysis
import Compiler.CompilationModel.ValidationCalls
import Compiler.CompilationModel.ValidationEvents
import Compiler.CompilationModel.ValidationHelpers
import Compiler.CompilationModel.ValidationInterop
import Compiler.CompilationModel.SelectorInteropHelpers
import Compiler.CompilationModel.ExpressionCompile

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

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
      | some ParamType.bytes | some ParamType.string => pure ()
      | some ty =>
          throw s!"Compilation error: function '{fnName}' returnBytes '{name}' requires bytes/string parameter, got {repr ty}"
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
def validateReturnShapesInStmt (fnName : String) (params : List Param)
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
  | Stmt.returnBytes name =>
      if isInternal then
        throw s!"Compilation error: internal function '{fnName}' cannot use Stmt.returnBytes; only static returns via Stmt.return/Stmt.returnValues are supported ({issue625Ref})."
      else if expectedReturns == [ParamType.bytes] || expectedReturns == [ParamType.string] then
        match findParamType params name with
        | some ty =>
            if expectedReturns == [ty] then
              pure ()
            else
              throw s!"Compilation error: function '{fnName}' uses Stmt.returnBytes to return parameter '{name}' of type {repr ty}, but declared returns are {repr expectedReturns}"
        | none =>
            throw s!"Compilation error: function '{fnName}' returnBytes references unknown parameter '{name}'"
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
      validateReturnShapesInStmtList fnName params expectedReturns isInternal thenBranch
      validateReturnShapesInStmtList fnName params expectedReturns isInternal elseBranch
  | Stmt.forEach _ _ body =>
      validateReturnShapesInStmtList fnName params expectedReturns isInternal body
  | _ => pure ()
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def validateReturnShapesInStmtList (fnName : String)
    (params : List Param) (expectedReturns : List ParamType) (isInternal : Bool) : List Stmt → Except String Unit
  | [] => pure ()
  | s :: ss => do
      validateReturnShapesInStmt fnName params expectedReturns isInternal s
      validateReturnShapesInStmtList fnName params expectedReturns isInternal ss
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
  | Expr.storage _ | Expr.storageAddr _ => true
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
  | Expr.blockNumber => true
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
  | Stmt.setStorage _ _ | Stmt.setStorageAddr _ _
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
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value | Stmt.setStorageAddr _ value |
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
  spec.body.forM (validateReturnShapesInStmt spec.name spec.params returns spec.isInternal)
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

end Compiler.CompilationModel
