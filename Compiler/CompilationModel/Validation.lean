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
import Compiler.CompilationModel.TrustSurface
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
  | ty => isWordArrayParam ty

mutual
def validateStmtParamReferences (fnName : String) (params : List Param) :
    Stmt → Except String Unit
  | Stmt.returnArray name =>
      match findParamType params name with
      | some ty =>
          if isWordArrayParam ty then
            pure ()
          else
            throw s!"Compilation error: function '{fnName}' returnArray '{name}' requires an array parameter with single-word static elements, got {repr ty}"
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
            throw s!"Compilation error: function '{fnName}' returnStorageWords '{name}' requires an array parameter with single-word static elements, got {repr ty}"
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
  | Stmt.returnArray name =>
      if isInternal then
        throw s!"Compilation error: internal function '{fnName}' cannot use Stmt.returnArray; only static returns via Stmt.return/Stmt.returnValues are supported ({issue625Ref})."
      else
        match findParamType params name with
        | some ty =>
            if !isWordArrayParam ty then
              throw s!"Compilation error: function '{fnName}' uses Stmt.returnArray with parameter '{name}' of type {repr ty}; only arrays with single-word static elements are currently supported"
            else if expectedReturns == [ty] then
              pure ()
            else
              throw s!"Compilation error: function '{fnName}' uses Stmt.returnArray to return parameter '{name}' of type {repr ty}, but declared returns are {repr expectedReturns}"
        | none =>
            throw s!"Compilation error: function '{fnName}' returnArray references unknown parameter '{name}'"
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
  | Expr.mappingChain _ _
  | Expr.structMember _ _ _ | Expr.structMember2 _ _ _ _ => true
  | Expr.caller => true
  | Expr.contractAddress => true
  | Expr.chainid => true
  | Expr.extcodesize _ => true
  | Expr.msgValue => true
  | Expr.blockTimestamp => true
  | Expr.blockNumber => true
  | Expr.blobbasefee => true
  | Expr.calldatasize => true
  | Expr.calldataload _ => true
  | Expr.mload offset => exprReadsStateOrEnv offset
  | Expr.tload _ => true
  | Expr.keccak256 offset size => exprReadsStateOrEnv offset || exprReadsStateOrEnv size
  | Expr.call _ _ _ _ _ _ _ | Expr.staticcall _ _ _ _ _ _
  | Expr.delegatecall _ _ _ _ _ _ => true
  | Expr.returndataSize => true
  | Expr.returndataOptionalBoolAt _ => true
  | Expr.dynamicBytesEq _ _ => false
  | Expr.localVar _ => false
  | Expr.externalCall _ _ | Expr.internalCall _ _ => true
  | Expr.arrayLength _ => false
  | Expr.storageArrayLength _ => true
  | Expr.storageArrayElement _ index => true || exprReadsStateOrEnv index
  | Expr.arrayElement _ index => exprReadsStateOrEnv index
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.sdiv a b
  | Expr.mod a b | Expr.smod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b
  | Expr.sar a b | Expr.signextend a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.sgt a b | Expr.lt a b | Expr.slt a b | Expr.le a b |
    Expr.logicalAnd a b | Expr.logicalOr a b |
    Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b |
    Expr.ceilDiv a b =>
      exprReadsStateOrEnv a || exprReadsStateOrEnv b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c =>
      exprReadsStateOrEnv a || exprReadsStateOrEnv b || exprReadsStateOrEnv c
  | Expr.bitNot a | Expr.logicalNot a =>
      exprReadsStateOrEnv a
  | Expr.ite cond thenVal elseVal =>
      exprReadsStateOrEnv cond || exprReadsStateOrEnv thenVal || exprReadsStateOrEnv elseVal

mutual
def exprWritesState : Expr → Bool
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.sdiv a b
  | Expr.mod a b | Expr.smod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b
  | Expr.sar a b | Expr.signextend a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.sgt a b | Expr.lt a b | Expr.slt a b | Expr.le a b |
    Expr.logicalAnd a b | Expr.logicalOr a b |
    Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b |
    Expr.ceilDiv a b =>
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
  | Expr.mappingChain _ keys =>
      exprListWritesState keys
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ =>
      exprWritesState key1 || exprWritesState key2
  | Expr.call _ _ _ _ _ _ _ => true
  | Expr.staticcall gas target inOffset inSize outOffset outSize =>
      exprWritesState gas || exprWritesState target ||
      exprWritesState inOffset || exprWritesState inSize ||
      exprWritesState outOffset || exprWritesState outSize
  | Expr.delegatecall _ _ _ _ _ _ => true
  | Expr.mload offset | Expr.tload offset =>
      exprWritesState offset
  | Expr.calldataload offset =>
      exprWritesState offset
  | Expr.keccak256 offset size =>
      exprWritesState offset || exprWritesState size
  | Expr.returndataOptionalBoolAt outOffset =>
      exprWritesState outOffset
  | Expr.dynamicBytesEq _ _ =>
      false
  | Expr.externalCall _ _ | Expr.internalCall _ _ => true
  | Expr.extcodesize addr =>
      exprWritesState addr
  | Expr.storageArrayLength _ =>
      false
  | Expr.storageArrayElement _ index =>
      exprWritesState index
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
  | Stmt.storageArrayPush _ _ | Stmt.storageArrayPop _ | Stmt.setStorageArrayElement _ _ _
  | Stmt.setMapping _ _ _ | Stmt.setMappingWord _ _ _ _ | Stmt.setMappingPackedWord _ _ _ _ _ | Stmt.setMappingUint _ _ _
  | Stmt.setMappingChain _ _ _
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
  | Stmt.tstore _ _ =>
      true
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
/-- Collect the set of storage field names written by a statement.
    Returns a list of field name strings found in `setStorage`, `setStorageAddr`,
    `setMapping*`, `storageArray*`, and `setStructMember*` constructors.
    Used by `modifies(...)` validation (#1729, Axis 3 Step 1b). -/
def stmtWrittenFields : Stmt → List String
  | Stmt.setStorage field _ | Stmt.setStorageAddr field _
  | Stmt.storageArrayPush field _ | Stmt.storageArrayPop field | Stmt.setStorageArrayElement field _ _
  | Stmt.setMapping field _ _ | Stmt.setMappingWord field _ _ _ | Stmt.setMappingPackedWord field _ _ _ _
  | Stmt.setMappingUint field _ _
  | Stmt.setMappingChain field _ _
  | Stmt.setMapping2 field _ _ _ | Stmt.setMapping2Word field _ _ _ _
  | Stmt.setStructMember field _ _ _ | Stmt.setStructMember2 field _ _ _ _ => [field]
  | Stmt.ite _ thenBranch elseBranch =>
      stmtListWrittenFields thenBranch ++ stmtListWrittenFields elseBranch
  | Stmt.forEach _ _ body =>
      stmtListWrittenFields body
  | _ => []
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def stmtListWrittenFields : List Stmt → List String
  | [] => []
  | s :: ss => stmtWrittenFields s ++ stmtListWrittenFields ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
/-- Check whether an expression contains an external call (call, staticcall, delegatecall,
    or externalCall).  Used by `no_external_calls` validation (#1729, Axis 3 Step 1c). -/
def exprContainsExternalCall : Expr → Bool
  | Expr.call _ _ _ _ _ _ _ | Expr.staticcall _ _ _ _ _ _
  | Expr.delegatecall _ _ _ _ _ _ | Expr.externalCall _ _ => true
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.sdiv a b
  | Expr.mod a b | Expr.smod a b
  | Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b | Expr.sar a b
  | Expr.lt a b | Expr.gt a b | Expr.slt a b | Expr.sgt a b | Expr.eq a b
  | Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b
  | Expr.ceilDiv a b =>
      exprContainsExternalCall a || exprContainsExternalCall b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c =>
      exprContainsExternalCall a || exprContainsExternalCall b || exprContainsExternalCall c
  | Expr.bitNot a | Expr.logicalNot a =>
      exprContainsExternalCall a
  | Expr.ite cond thenVal elseVal =>
      exprContainsExternalCall cond || exprContainsExternalCall thenVal || exprContainsExternalCall elseVal
  | Expr.mapping _ key | Expr.mappingWord _ key _ | Expr.mappingPackedWord _ key _ _ | Expr.mappingUint _ key
  | Expr.structMember _ key _ =>
      exprContainsExternalCall key
  | Expr.mappingChain _ keys =>
      exprListContainsExternalCall keys
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ =>
      exprContainsExternalCall key1 || exprContainsExternalCall key2
  | Expr.mload offset | Expr.tload offset | Expr.calldataload offset
  | Expr.returndataOptionalBoolAt offset =>
      exprContainsExternalCall offset
  | Expr.keccak256 offset size =>
      exprContainsExternalCall offset || exprContainsExternalCall size
  | _ => false
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

def exprListContainsExternalCall : List Expr → Bool
  | [] => false
  | e :: es => exprContainsExternalCall e || exprListContainsExternalCall es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
/-- Check whether a statement contains an external call (externalCallBind, ecm, or
    an expression with call/staticcall/delegatecall/externalCall).
    Used by `no_external_calls` validation (#1729, Axis 3 Step 1c). -/
def stmtContainsExternalCall : Stmt → Bool
  | Stmt.externalCallBind _ _ _ => true
  | Stmt.ecm _ _ => true
  | Stmt.letVar _ value | Stmt.assignVar _ value =>
      exprContainsExternalCall value
  | Stmt.setStorage _ value | Stmt.setStorageAddr _ value | Stmt.require value _ =>
      exprContainsExternalCall value
  | Stmt.requireError cond _ args =>
      exprContainsExternalCall cond || args.any exprContainsExternalCall
  | Stmt.revertError _ args =>
      args.any exprContainsExternalCall
  | Stmt.return value =>
      exprContainsExternalCall value
  | Stmt.returnValues values =>
      values.any exprContainsExternalCall
  | Stmt.storageArrayPush _ value =>
      exprContainsExternalCall value
  | Stmt.setStorageArrayElement _ index value =>
      exprContainsExternalCall index || exprContainsExternalCall value
  | Stmt.setMapping _ key value | Stmt.setMappingUint _ key value =>
      exprContainsExternalCall key || exprContainsExternalCall value
  | Stmt.setMappingWord _ key _ value =>
      exprContainsExternalCall key || exprContainsExternalCall value
  | Stmt.setMappingPackedWord _ key _ _ value =>
      exprContainsExternalCall key || exprContainsExternalCall value
  | Stmt.setMappingChain _ keys value =>
      keys.any exprContainsExternalCall || exprContainsExternalCall value
  | Stmt.setMapping2 _ key1 key2 value =>
      exprContainsExternalCall key1 || exprContainsExternalCall key2 || exprContainsExternalCall value
  | Stmt.setMapping2Word _ key1 key2 _ value =>
      exprContainsExternalCall key1 || exprContainsExternalCall key2 || exprContainsExternalCall value
  | Stmt.setStructMember _ key _ value =>
      exprContainsExternalCall key || exprContainsExternalCall value
  | Stmt.setStructMember2 _ key1 key2 _ value =>
      exprContainsExternalCall key1 || exprContainsExternalCall key2 || exprContainsExternalCall value
  | Stmt.emit _ args =>
      args.any exprContainsExternalCall
  | Stmt.rawLog topics dataOffset dataSize =>
      topics.any exprContainsExternalCall || exprContainsExternalCall dataOffset || exprContainsExternalCall dataSize
  | Stmt.tstore offset value | Stmt.mstore offset value =>
      exprContainsExternalCall offset || exprContainsExternalCall value
  | Stmt.calldatacopy destOffset sourceOffset size =>
      exprContainsExternalCall destOffset || exprContainsExternalCall sourceOffset || exprContainsExternalCall size
  | Stmt.returndataCopy destOffset sourceOffset size =>
      exprContainsExternalCall destOffset || exprContainsExternalCall sourceOffset || exprContainsExternalCall size
  | Stmt.ite cond thenBranch elseBranch =>
      exprContainsExternalCall cond || stmtListContainsExternalCall thenBranch || stmtListContainsExternalCall elseBranch
  | Stmt.forEach _ count body =>
      exprContainsExternalCall count || stmtListContainsExternalCall body
  | Stmt.internalCall _ args | Stmt.internalCallAssign _ _ args =>
      args.any exprContainsExternalCall
  | _ => false
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def stmtListContainsExternalCall : List Stmt → Bool
  | [] => false
  | s :: ss => stmtContainsExternalCall s || stmtListContainsExternalCall ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

mutual
def stmtReadsStateOrEnv : Stmt → Bool
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value | Stmt.setStorageAddr _ value |
    Stmt.return value | Stmt.require value _ =>
      exprReadsStateOrEnv value
  | Stmt.storageArrayPush _ value =>
      true || exprReadsStateOrEnv value
  | Stmt.setStorageArrayElement _ index value =>
      true || exprReadsStateOrEnv index || exprReadsStateOrEnv value
  | Stmt.storageArrayPop _ =>
      true
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
  | Stmt.tstore offset value =>
      exprReadsStateOrEnv offset || exprReadsStateOrEnv value
  | Stmt.calldatacopy _ _ _ | Stmt.returndataCopy _ _ _ => true
  | Stmt.revertReturndata =>
      true
  | Stmt.stop =>
      false
  | Stmt.setMapping _ _ _ | Stmt.setMappingWord _ _ _ _ | Stmt.setMappingPackedWord _ _ _ _ _ | Stmt.setMappingUint _ _ _
  | Stmt.setMappingChain _ _ _
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

/-- Check whether a single statement is a direct persistent-storage write.
    This covers all `setStorage*`, `setMapping*`, `storageArray*`, `setStructMember*`,
    and `tstore` constructors.  Events, local variables, and memory writes are NOT
    considered persistent state writes for CEI purposes.
    (#1728, Axis 2 Step 2a) -/
def stmtIsPersistentWrite : Stmt → Bool
  | Stmt.setStorage _ _ | Stmt.setStorageAddr _ _
  | Stmt.storageArrayPush _ _ | Stmt.storageArrayPop _ | Stmt.setStorageArrayElement _ _ _
  | Stmt.setMapping _ _ _ | Stmt.setMappingWord _ _ _ _ | Stmt.setMappingPackedWord _ _ _ _ _ | Stmt.setMappingUint _ _ _
  | Stmt.setMappingChain _ _ _
  | Stmt.setMapping2 _ _ _ _ | Stmt.setMapping2Word _ _ _ _ _
  | Stmt.setStructMember _ _ _ _ | Stmt.setStructMember2 _ _ _ _ _
  | Stmt.tstore _ _ => true
  | _ => false

/-- Check whether a single statement directly performs an external call
    (excluding expressions nested inside it — only `externalCallBind` and `ecm`).
    (#1728, Axis 2 Step 2a) -/
def stmtIsDirectExternalCall : Stmt → Bool
  | Stmt.externalCallBind _ _ _ => true
  | Stmt.ecm _ _ => true
  | _ => false

mutual
/-- CEI analysis: walk a statement list sequentially and return a descriptive
    violation string if a persistent-storage write occurs after any statement
    that is or contains an external call.  Returns `none` if compliant.
    For `ite`, each branch is checked independently AND if either branch contains
    an external call, subsequent statements must not write state.
    For `forEach`, the body is checked and if it contains an external call the
    loop is treated as an interaction for subsequent statements.
    (#1728, Axis 2 Step 2a) -/
def stmtListCEIViolation : List Stmt → Bool → Option String
  | [], _ => none
  | s :: rest, seenCall =>
      -- First, check for CEI violation within this statement itself
      match stmtInternalCEIViolation s with
      | some msg => some msg
      | none =>
          -- If we've seen an external call and this statement writes state, violation
          if seenCall && stmtIsPersistentWrite s then
            some "state write after external call"
          else
            let newSeenCall := seenCall || stmtContainsExternalCall s
            stmtListCEIViolation rest newSeenCall
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega

/-- Check for CEI violations within a single compound statement (ite, forEach).
    Returns a descriptive string if a violation is found within the statement's
    own nested structure. -/
def stmtInternalCEIViolation : Stmt → Option String
  | Stmt.ite _ thenBranch elseBranch =>
      match stmtListCEIViolation thenBranch false with
      | some msg => some s!"in if-then branch: {msg}"
      | none =>
          match stmtListCEIViolation elseBranch false with
          | some msg => some s!"in if-else branch: {msg}"
          | none => none
  | Stmt.forEach _ _ body =>
      -- In a loop, if the body has both an external call and a state write,
      -- a second iteration would violate CEI even if the first doesn't
      let bodyHasCall := body.any stmtContainsExternalCall
      let bodyHasWrite := body.any stmtIsPersistentWrite
      if bodyHasCall && bodyHasWrite then
        some "loop body contains both external call and state write (subsequent iterations would violate CEI)"
      else
        match stmtListCEIViolation body false with
        | some msg => some s!"in loop body: {msg}"
        | none => none
  | _ => none
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega
end

def validateFunctionSpec (spec : FunctionSpec) : Except String Unit := do
  let unsafeBoundaryMechanics := collectUnsafeBoundaryMechanicsFromStmts spec.body
  if !unsafeBoundaryMechanics.isEmpty && spec.localObligations.isEmpty then
    throw s!"Compilation error: function '{spec.name}' uses low-level/assembly mechanic(s) {String.intercalate ", " unsafeBoundaryMechanics} without any local_obligations entry ({issue1424Ref}). Add local_obligations [...] to make the trust boundary explicit."
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
  -- Validate modifies annotation: if declared, every written field must be in the set
  if !spec.modifies.isEmpty then
    let writtenFields := (stmtListWrittenFields spec.body).eraseDups
    for field in writtenFields do
      if !spec.modifies.contains field then
        throw s!"Compilation error: function '{spec.name}' is annotated modifies({String.intercalate ", " spec.modifies}) but writes to undeclared field '{field}'"
  -- Validate no_external_calls annotation: reject external call statements
  if spec.noExternalCalls && spec.body.any stmtContainsExternalCall then
    throw s!"Compilation error: function '{spec.name}' is annotated no_external_calls but contains external call statements"
  -- CEI enforcement: reject state writes after external calls unless opted out (#1728, Axis 2 Step 2a)
  if !spec.allowPostInteractionWrites then
    match stmtListCEIViolation spec.body false with
    | some violation =>
        throw s!"Compilation error: function '{spec.name}' violates CEI (Checks-Effects-Interactions) ordering: {violation}. Reorder state writes before external calls, or annotate with allow_post_interaction_writes to opt out ({issue1728Ref})"
    | none => pure ()
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
      let unsafeBoundaryMechanics := collectUnsafeBoundaryMechanicsFromStmts spec.body
      if !unsafeBoundaryMechanics.isEmpty && spec.localObligations.isEmpty then
        throw s!"Compilation error: constructor uses low-level/assembly mechanic(s) {String.intercalate ", " unsafeBoundaryMechanics} without any local_obligations entry ({issue1424Ref}). Add local_obligations [...] to make the trust boundary explicit."
      if spec.body.any stmtContainsUnsafeLogicalCallLike then
        throw s!"Compilation error: constructor uses Expr.logicalAnd/Expr.logicalOr/Expr.ite or arithmetic helpers (mulDivUp/wDivUp/min/max) with call-like operand(s) that would be duplicated in Yul output ({issue748Ref}). Move call-like expressions into Stmt.letVar before combining."
      spec.body.forM validateNoRuntimeReturnsInConstructorStmt
      spec.body.forM (validateStmtParamReferences "constructor" spec.params)
      validateConstructorIdentifierReferences ctor

end Compiler.CompilationModel
