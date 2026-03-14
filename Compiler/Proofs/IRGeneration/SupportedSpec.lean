import Compiler.Proofs.IRGeneration.SupportedFragment
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.Dispatch
import Compiler.CompilationModel.UsageAnalysis
import Compiler.CompilationModel.SelectorInteropHelpers
import Compiler.TypedIRCompilerCorrectness

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel

/-- ABI parameter types admitted by the first whole-contract Layer 2 fragment.
Only single-head-word scalars are included for the initial generic theorem. -/
def SupportedExternalParamType : ParamType → Prop
  | .uint256 | .uint8 | .address | .bytes32 => True
  | _ => False

/-- Return profiles admitted by the first whole-contract Layer 2 fragment.
The initial theorem only targets zero-return or single-head-word-return entrypoints. -/
def SupportedExternalReturnProfile : List ParamType → Prop
  | [] => True
  | [ty] => SupportedExternalParamType ty
  | _ => False

/-- Selector-dispatched entrypoints in the same order used by `CompilationModel.compile`. -/
def selectorDispatchedFunctions (spec : CompilationModel) : List FunctionSpec :=
  spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)

/-- Parameter-profile interface for selector-dispatched entrypoints covered by the
current whole-contract theorem. -/
structure SupportedParamProfile (params : List Param) : Prop where
  namesNodup : (params.map (·.name)).Nodup
  supported : ∀ param ∈ params, SupportedExternalParamType param.ty

/-- Return-profile interface for selector-dispatched entrypoints covered by the
current whole-contract theorem. -/
structure SupportedReturnProfile (fn : FunctionSpec) : Prop where
  resolved :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns

/-- Pure expression forms still outside the current generic-induction core, even
before any richer contract surface is considered. This tracks proof-core gaps
rather than a semantic trust boundary. -/
def exprTouchesUnsupportedCoreSurface : Expr → Bool
  | .literal _ | .param _ | .caller | .contractAddress
  | .chainid | .msgValue | .blockTimestamp | .blockNumber
  | .localVar _ => false
  | .storage _ | .storageAddr _ => false
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .eq a b | .ge a b | .gt a b | .lt a b | .le a b
  | .logicalAnd a b | .logicalOr a b =>
      exprTouchesUnsupportedCoreSurface a || exprTouchesUnsupportedCoreSurface b
  | .logicalNot a => exprTouchesUnsupportedCoreSurface a
  | .sdiv a b | .smod a b | .bitAnd a b | .bitOr a b | .bitXor a b
  | .sgt a b | .slt a b | .min a b | .max a b | .wMulDown a b | .wDivUp a b =>
      true
  | .bitNot _ => true
  | .ite cond thenVal elseVal =>
      exprTouchesUnsupportedCoreSurface cond ||
        exprTouchesUnsupportedCoreSurface thenVal ||
        exprTouchesUnsupportedCoreSurface elseVal
  | .mulDivDown _ _ _ | .mulDivUp _ _ _ | .shl _ _
  | .shr _ _ | .sar _ _ | .signextend _ _ => true
  | .mapping _ _ | .mappingWord _ _ _ | .mappingPackedWord _ _ _ _
  | .mapping2 _ _ _ | .mapping2Word _ _ _ _ | .mappingUint _ _ | .mappingChain _ _
  | .structMember _ _ _ | .structMember2 _ _ _ _
  | .constructorArg _ | .blobbasefee | .mload _ | .tload _ | .keccak256 _ _
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _
  | .calldatasize | .calldataload _ | .returndataSize | .extcodesize _
  | .returndataOptionalBoolAt _ | .externalCall _ _ | .internalCall _ _
  | .arrayLength _ | .arrayElement _ _ | .storageArrayLength _ | .storageArrayElement _ _
  | .dynamicBytesEq _ _ => true

/-- Stateful expression surfaces not yet carried by the generic Layer 2 body
interface. These are the next storage/layout-style widening targets. -/
def exprTouchesUnsupportedStateSurface : Expr → Bool
  | .literal _ | .param _ | .caller | .contractAddress
  | .chainid | .msgValue | .blockTimestamp | .blockNumber
  | .localVar _ => false
  | .storage _ | .storageAddr _ => true
  | .mapping _ _ | .mappingWord _ _ _ | .mappingPackedWord _ _ _ _
  | .mapping2 _ _ _ | .mapping2Word _ _ _ _ | .mappingUint _ _ | .mappingChain _ _
  | .structMember _ _ _ | .structMember2 _ _ _ _
  | .storageArrayLength _ | .storageArrayElement _ _ => true
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b =>
      exprTouchesUnsupportedStateSurface a || exprTouchesUnsupportedStateSurface b
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b =>
      exprTouchesUnsupportedStateSurface a || exprTouchesUnsupportedStateSurface b
  | .bitNot a | .logicalNot a => exprTouchesUnsupportedStateSurface a
  | .ite cond thenVal elseVal =>
      exprTouchesUnsupportedStateSurface cond ||
        exprTouchesUnsupportedStateSurface thenVal ||
        exprTouchesUnsupportedStateSurface elseVal
  | .constructorArg _ | .blobbasefee | .mload _ | .tload _ | .keccak256 _ _
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _
  | .calldatasize | .calldataload _ | .returndataSize | .extcodesize _
  | .returndataOptionalBoolAt _ | .externalCall _ _ | .internalCall _ _
  | .arrayLength _ | .arrayElement _ _ | .mulDivDown _ _ _ | .mulDivUp _ _ _
  | .shl _ _ | .shr _ _ | .sar _ _ | .signextend _ _
  | .dynamicBytesEq _ _ => false

/-- Call-related surfaces that still sit outside the current generic Layer 2
body theorem: internal helper reuse, low-level calls, and foreign call hooks. -/
def exprTouchesUnsupportedCallSurface : Expr → Bool
  | .internalCall _ _ | .externalCall _ _ => true
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _ => true
  | .literal _ | .param _ | .caller | .contractAddress
  | .chainid | .msgValue | .blockTimestamp | .blockNumber
  | .localVar _ | .storage _ | .storageAddr _
  | .constructorArg _ | .blobbasefee | .mload _ | .tload _
  | .calldatasize | .calldataload _ | .returndataSize | .extcodesize _
  | .returndataOptionalBoolAt _ | .keccak256 _ _ | .arrayLength _
  | .storageArrayLength _ => false
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b =>
      exprTouchesUnsupportedCallSurface a || exprTouchesUnsupportedCallSurface b
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b =>
      exprTouchesUnsupportedCallSurface a || exprTouchesUnsupportedCallSurface b
  | .mapping _ b | .mappingUint _ b | .arrayElement _ b | .storageArrayElement _ b =>
      exprTouchesUnsupportedCallSurface b
  | .mappingChain _ _ => true
  | .bitNot a | .logicalNot a | .mappingWord _ a _ | .mappingPackedWord _ a _ _
  | .structMember _ a _ => exprTouchesUnsupportedCallSurface a
  | .ite cond thenVal elseVal =>
      exprTouchesUnsupportedCallSurface cond ||
        exprTouchesUnsupportedCallSurface thenVal ||
        exprTouchesUnsupportedCallSurface elseVal
  | .mapping2 _ a b | .mapping2Word _ a b _ | .structMember2 _ a b _ =>
      exprTouchesUnsupportedCallSurface a || exprTouchesUnsupportedCallSurface b
  | .mulDivDown a b c | .mulDivUp a b c =>
      exprTouchesUnsupportedCallSurface a ||
        exprTouchesUnsupportedCallSurface b ||
        exprTouchesUnsupportedCallSurface c
  | .shl a b | .shr a b | .sar a b | .signextend a b =>
      exprTouchesUnsupportedCallSurface a || exprTouchesUnsupportedCallSurface b
  | .dynamicBytesEq _ _ => false

/-- Internal helper-call surfaces not yet modeled compositionally in the current
generic whole-contract theorem. -/
def exprTouchesUnsupportedHelperSurface : Expr → Bool
  | .internalCall _ _ => true
  | .literal _ | .param _ | .caller | .contractAddress
  | .chainid | .msgValue | .blockTimestamp | .blockNumber
  | .localVar _ | .storage _ | .storageAddr _
  | .constructorArg _ | .blobbasefee | .mload _ | .tload _
  | .calldatasize | .calldataload _ | .returndataSize | .extcodesize _
  | .returndataOptionalBoolAt _ | .keccak256 _ _ | .arrayLength _
  | .storageArrayLength _ | .externalCall _ _ => false
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _ => false
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b =>
      exprTouchesUnsupportedHelperSurface a || exprTouchesUnsupportedHelperSurface b
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b =>
      exprTouchesUnsupportedHelperSurface a || exprTouchesUnsupportedHelperSurface b
  | .mapping _ b | .mappingUint _ b | .arrayElement _ b | .storageArrayElement _ b =>
      exprTouchesUnsupportedHelperSurface b
  | .mappingChain _ _ => true
  | .bitNot a | .logicalNot a | .mappingWord _ a _ | .mappingPackedWord _ a _ _
  | .structMember _ a _ => exprTouchesUnsupportedHelperSurface a
  | .ite cond thenVal elseVal =>
      exprTouchesUnsupportedHelperSurface cond ||
        exprTouchesUnsupportedHelperSurface thenVal ||
        exprTouchesUnsupportedHelperSurface elseVal
  | .mapping2 _ a b | .mapping2Word _ a b _ | .structMember2 _ a b _ =>
      exprTouchesUnsupportedHelperSurface a || exprTouchesUnsupportedHelperSurface b
  | .mulDivDown a b c | .mulDivUp a b c =>
      exprTouchesUnsupportedHelperSurface a ||
        exprTouchesUnsupportedHelperSurface b ||
        exprTouchesUnsupportedHelperSurface c
  | .shl a b | .shr a b | .sar a b | .signextend a b =>
      exprTouchesUnsupportedHelperSurface a || exprTouchesUnsupportedHelperSurface b
  | .dynamicBytesEq _ _ => false

def exprListTouchesUnsupportedHelperSurface : List Expr → Bool
  | [] => false
  | e :: rest => exprTouchesUnsupportedHelperSurface e || exprListTouchesUnsupportedHelperSurface rest

mutual
/-- Narrow helper-effect surface used by the exact helper-aware induction seam:
this tracks only genuine internal-helper execution, not the broader set of
still-unsupported expression shapes that currently share the coarse
`exprTouchesUnsupportedHelperSurface` approximation. -/
def exprTouchesInternalHelperSurface : Expr → Bool
  | .internalCall _ _ => true
  | .literal _ | .param _ | .caller | .contractAddress
  | .chainid | .msgValue | .blockTimestamp | .blockNumber
  | .localVar _ | .storage _ | .storageAddr _
  | .constructorArg _ | .blobbasefee | .mload _ | .tload _
  | .calldatasize | .calldataload _ | .returndataSize | .extcodesize _
  | .returndataOptionalBoolAt _ | .keccak256 _ _ | .arrayLength _
  | .storageArrayLength _ | .externalCall _ _ => false
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _ => false
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b =>
      exprTouchesInternalHelperSurface a || exprTouchesInternalHelperSurface b
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b =>
      exprTouchesInternalHelperSurface a || exprTouchesInternalHelperSurface b
  | .mapping _ b | .mappingUint _ b | .arrayElement _ b | .storageArrayElement _ b =>
      exprTouchesInternalHelperSurface b
  | .mappingChain _ keys =>
      exprListTouchesInternalHelperSurface keys
  | .bitNot a | .logicalNot a | .mappingWord _ a _ | .mappingPackedWord _ a _ _
  | .structMember _ a _ => exprTouchesInternalHelperSurface a
  | .ite cond thenVal elseVal =>
      exprTouchesInternalHelperSurface cond ||
        exprTouchesInternalHelperSurface thenVal ||
        exprTouchesInternalHelperSurface elseVal
  | .mapping2 _ a b | .mapping2Word _ a b _ | .structMember2 _ a b _ =>
      exprTouchesInternalHelperSurface a || exprTouchesInternalHelperSurface b
  | .mulDivDown a b c | .mulDivUp a b c =>
      exprTouchesInternalHelperSurface a ||
        exprTouchesInternalHelperSurface b ||
        exprTouchesInternalHelperSurface c
  | .shl a b | .shr a b | .sar a b | .signextend a b =>
      exprTouchesInternalHelperSurface a || exprTouchesInternalHelperSurface b
  | .dynamicBytesEq _ _ => false

def exprListTouchesInternalHelperSurface : List Expr → Bool
  | [] => false
  | e :: rest => exprTouchesInternalHelperSurface e || exprListTouchesInternalHelperSurface rest
end

/-- Foreign-call/library-hook surfaces still outside the current generic
whole-contract theorem. -/
def exprTouchesUnsupportedForeignSurface : Expr → Bool
  | .externalCall _ _ => true
  | .literal _ | .param _ | .caller | .contractAddress
  | .chainid | .msgValue | .blockTimestamp | .blockNumber
  | .localVar _ | .storage _ | .storageAddr _
  | .constructorArg _ | .blobbasefee | .mload _ | .tload _
  | .calldatasize | .calldataload _ | .returndataSize | .extcodesize _
  | .returndataOptionalBoolAt _ | .keccak256 _ _ | .arrayLength _
  | .storageArrayLength _ | .internalCall _ _ => false
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _ => false
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b =>
      exprTouchesUnsupportedForeignSurface a || exprTouchesUnsupportedForeignSurface b
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b =>
      exprTouchesUnsupportedForeignSurface a || exprTouchesUnsupportedForeignSurface b
  | .mapping _ b | .mappingUint _ b | .arrayElement _ b | .storageArrayElement _ b =>
      exprTouchesUnsupportedForeignSurface b
  | .mappingChain _ _ => true
  | .bitNot a | .logicalNot a | .mappingWord _ a _ | .mappingPackedWord _ a _ _
  | .structMember _ a _ => exprTouchesUnsupportedForeignSurface a
  | .ite cond thenVal elseVal =>
      exprTouchesUnsupportedForeignSurface cond ||
        exprTouchesUnsupportedForeignSurface thenVal ||
        exprTouchesUnsupportedForeignSurface elseVal
  | .mapping2 _ a b | .mapping2Word _ a b _ | .structMember2 _ a b _ =>
      exprTouchesUnsupportedForeignSurface a || exprTouchesUnsupportedForeignSurface b
  | .mulDivDown a b c | .mulDivUp a b c =>
      exprTouchesUnsupportedForeignSurface a ||
        exprTouchesUnsupportedForeignSurface b ||
        exprTouchesUnsupportedForeignSurface c
  | .shl a b | .shr a b | .sar a b | .signextend a b =>
      exprTouchesUnsupportedForeignSurface a || exprTouchesUnsupportedForeignSurface b
  | .dynamicBytesEq _ _ => false

/-- Low-level call/runtime-mechanic surfaces still outside the current generic
whole-contract theorem. -/
def exprTouchesUnsupportedLowLevelSurface : Expr → Bool
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _ => true
  | .literal _ | .param _ | .caller | .contractAddress
  | .chainid | .msgValue | .blockTimestamp | .blockNumber
  | .localVar _ | .storage _ | .storageAddr _
  | .constructorArg _ | .blobbasefee | .mload _ | .tload _
  | .calldatasize | .calldataload _ | .returndataSize | .extcodesize _
  | .returndataOptionalBoolAt _ | .keccak256 _ _ | .arrayLength _
  | .storageArrayLength _ | .internalCall _ _ | .externalCall _ _ => false
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b =>
      exprTouchesUnsupportedLowLevelSurface a || exprTouchesUnsupportedLowLevelSurface b
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b =>
      exprTouchesUnsupportedLowLevelSurface a || exprTouchesUnsupportedLowLevelSurface b
  | .mapping _ b | .mappingUint _ b | .arrayElement _ b | .storageArrayElement _ b =>
      exprTouchesUnsupportedLowLevelSurface b
  | .mappingChain _ _ => true
  | .bitNot a | .logicalNot a | .mappingWord _ a _ | .mappingPackedWord _ a _ _
  | .structMember _ a _ => exprTouchesUnsupportedLowLevelSurface a
  | .ite cond thenVal elseVal =>
      exprTouchesUnsupportedLowLevelSurface cond ||
        exprTouchesUnsupportedLowLevelSurface thenVal ||
        exprTouchesUnsupportedLowLevelSurface elseVal
  | .mapping2 _ a b | .mapping2Word _ a b _ | .structMember2 _ a b _ =>
      exprTouchesUnsupportedLowLevelSurface a || exprTouchesUnsupportedLowLevelSurface b
  | .mulDivDown a b c | .mulDivUp a b c =>
      exprTouchesUnsupportedLowLevelSurface a ||
        exprTouchesUnsupportedLowLevelSurface b ||
        exprTouchesUnsupportedLowLevelSurface c
  | .shl a b | .shr a b | .sar a b | .signextend a b =>
      exprTouchesUnsupportedLowLevelSurface a || exprTouchesUnsupportedLowLevelSurface b
  | .dynamicBytesEq _ _ => false

/-- Compatibility expression scan retained for the current generic-induction
proofs. This intentionally preserves the pre-interface split meaning so the
generic-induction boundary does not silently widen or tighten while the new
feature-local interfaces are introduced alongside it. -/
def exprTouchesUnsupportedContractSurface (expr : Expr) : Bool :=
  match expr with
  | .literal _ | .param _ | .caller | .contractAddress
  | .chainid | .msgValue | .blockTimestamp | .blockNumber
  | .localVar _ => false
  | .storage _ | .storageAddr _ => true
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b =>
      exprTouchesUnsupportedContractSurface a || exprTouchesUnsupportedContractSurface b
  | .bitNot a | .logicalNot a => exprTouchesUnsupportedContractSurface a
  | .ite cond thenVal elseVal =>
      exprTouchesUnsupportedContractSurface cond ||
        exprTouchesUnsupportedContractSurface thenVal ||
        exprTouchesUnsupportedContractSurface elseVal
  | .mapping _ _ | .mappingWord _ _ _ | .mappingPackedWord _ _ _ _
  | .mapping2 _ _ _ | .mapping2Word _ _ _ _ | .mappingUint _ _ | .mappingChain _ _
  | .structMember _ _ _ | .structMember2 _ _ _ _
  | .constructorArg _ | .blobbasefee | .mload _ | .tload _ | .keccak256 _ _
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _
  | .calldatasize | .calldataload _ | .returndataSize | .extcodesize _
  | .returndataOptionalBoolAt _ | .externalCall _ _ | .internalCall _ _
  | .arrayLength _ | .arrayElement _ _ | .storageArrayLength _ | .storageArrayElement _ _
  | .mulDivDown _ _ _ | .mulDivUp _ _ _ | .shl _ _
  | .shr _ _ | .sar _ _ | .signextend _ _
  | .dynamicBytesEq _ _ => true

mutual
/-- Observable/effect-rich surfaces outside the current generic whole-contract
theorem: richer returns, logs, typed errors, and raw external effect hooks. -/
def stmtTouchesUnsupportedEffectSurface : Stmt → Bool
  | .requireError _ _ _ | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .emit _ _ | .rawLog _ _ _
  | .externalCallBind _ _ _ | .ecm _ _ => true
  | .letVar _ _ | .assignVar _ _ | .setStorage _ _ | .setStorageAddr _ _
  | .require _ _ | .return _ | .mstore _ _ | .tstore _ _ | .stop
  | .setMapping _ _ _ | .setMappingWord _ _ _ _
  | .setMappingPackedWord _ _ _ _ _ | .setMapping2 _ _ _ _
  | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _ | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
  | .storageArrayPush _ _ | .storageArrayPop _ | .setStorageArrayElement _ _ _
  | .calldatacopy _ _ _ | .returndataCopy _ _ _ | .revertReturndata
  | .internalCall _ _ | .internalCallAssign _ _ _ => false
  | .ite _ thenBranch elseBranch =>
      stmtListTouchesUnsupportedEffectSurface thenBranch ||
        stmtListTouchesUnsupportedEffectSurface elseBranch
  | .forEach _ _ body =>
      stmtListTouchesUnsupportedEffectSurface body

/-- Statement forms intentionally still outside the current generic-induction
core, excluding richer state/call/effect surfaces that now have dedicated
interfaces of their own. -/
def stmtTouchesUnsupportedCoreSurface : Stmt → Bool
  | .letVar _ value | .assignVar _ value | .setStorage _ value =>
      exprTouchesUnsupportedCoreSurface value
  | .setStorageAddr _ value =>
      exprTouchesUnsupportedCoreSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedCoreSurface cond
  | .stop => false
  | .ite _ _ _ | .forEach _ _ _ => true
  | .mstore _ _ | .tstore _ _
  | .setMapping _ _ _ | .setMappingWord _ _ _ _ | .setMappingPackedWord _ _ _ _ _
  | .setMapping2 _ _ _ _ | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _
  | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
  | .storageArrayPush _ _ | .storageArrayPop _ | .setStorageArrayElement _ _ _
  | .requireError _ _ _ | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .calldatacopy _ _ _
  | .returndataCopy _ _ _ | .revertReturndata
  | .emit _ _ | .internalCall _ _ | .internalCallAssign _ _ _
  | .rawLog _ _ _ | .externalCallBind _ _ _ | .ecm _ _ => false

/-- State/layout-rich statement surfaces still outside the current whole-contract
theorem. -/
def stmtTouchesUnsupportedStateSurface : Stmt → Bool
  | .letVar _ value | .assignVar _ value | .setStorage _ value =>
      exprTouchesUnsupportedStateSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedStateSurface cond
  | .setStorageAddr _ value =>
      exprTouchesUnsupportedStateSurface value
  | .setMapping _ _ _ | .setMappingWord _ _ _ _ | .setMappingPackedWord _ _ _ _ _
  | .setMapping2 _ _ _ _ | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _
  | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
  | .storageArrayPush _ _ | .storageArrayPop _ | .setStorageArrayElement _ _ _ => true
  | .stop | .mstore _ _ | .tstore _ _
  | .requireError _ _ _ | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .calldatacopy _ _ _
  | .returndataCopy _ _ _ | .revertReturndata
  | .emit _ _ | .internalCall _ _ | .internalCallAssign _ _ _
  | .rawLog _ _ _ | .externalCallBind _ _ _ | .ecm _ _ => false
  | .ite cond thenBranch elseBranch =>
      exprTouchesUnsupportedStateSurface cond ||
        stmtListTouchesUnsupportedStateSurface thenBranch ||
        stmtListTouchesUnsupportedStateSurface elseBranch
  | .forEach _ count body =>
      exprTouchesUnsupportedStateSurface count ||
        stmtListTouchesUnsupportedStateSurface body

/-- Weaker Tier 2 state-surface gate used by the singleton storage-write bridge:
all existing unsupported stateful forms remain excluded except for the proved
singleton mapping-write heads. -/
def stmtTouchesUnsupportedStateSurfaceExceptMappingWrites : Stmt → Bool
  | .setMapping _ _ _ | .setMappingWord _ _ _ _ | .setMappingPackedWord _ _ _ _ _
  | .setMapping2 _ _ _ _
  | .setMapping2Word _ _ _ _ _ | .setStructMember _ _ _ _
  | .setStructMember2 _ _ _ _ _
  | .setMappingUint _ _ _ | .setMappingChain _ _ _ => false
  | stmt => stmtTouchesUnsupportedStateSurface stmt

/-- Helper/foreign/runtime-call statement surfaces still outside the current
generic theorem. -/
def stmtTouchesUnsupportedCallSurface : Stmt → Bool
  | .letVar _ value | .assignVar _ value | .setStorage _ value =>
      exprTouchesUnsupportedCallSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedCallSurface cond
  | .internalCall _ _ | .internalCallAssign _ _ _ => true
  | .calldatacopy _ _ _
  | .returndataCopy _ _ _ | .revertReturndata | .externalCallBind _ _ _
  | .ecm _ _ => true
  | .stop | .setStorageAddr _ _ | .mstore _ _ | .tstore _ _
  | .setMapping _ _ _ | .setMappingWord _ _ _ _ | .setMappingPackedWord _ _ _ _ _
  | .setMapping2 _ _ _ _ | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _
  | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
  | .storageArrayPush _ _ | .storageArrayPop _ | .setStorageArrayElement _ _ _
  | .requireError _ _ _ | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .emit _ _ | .rawLog _ _ _ => false
  | .ite cond thenBranch elseBranch =>
      exprTouchesUnsupportedCallSurface cond ||
        stmtListTouchesUnsupportedCallSurface thenBranch ||
        stmtListTouchesUnsupportedCallSurface elseBranch
  | .forEach _ count body =>
      exprTouchesUnsupportedCallSurface count ||
        stmtListTouchesUnsupportedCallSurface body

def stmtTouchesUnsupportedHelperSurface : Stmt → Bool
  | .letVar _ value | .assignVar _ value | .setStorage _ value =>
      exprTouchesUnsupportedHelperSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedHelperSurface cond
  | .internalCall _ _ | .internalCallAssign _ _ _ => true
  | .stop | .setStorageAddr _ _
  | .mstore _ _ | .tstore _ _ | .calldatacopy _ _ _
  | .returndataCopy _ _ _ | .revertReturndata | .externalCallBind _ _ _
  | .ecm _ _ | .setMapping _ _ _ | .setMappingWord _ _ _ _
  | .setMappingPackedWord _ _ _ _ _ | .setMapping2 _ _ _ _
  | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _ | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
  | .storageArrayPush _ _ | .storageArrayPop _ | .setStorageArrayElement _ _ _
  | .requireError _ _ _ | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .emit _ _ | .rawLog _ _ _ => false
  | .ite cond thenBranch elseBranch =>
      exprTouchesUnsupportedHelperSurface cond ||
        stmtListTouchesUnsupportedHelperSurface thenBranch ||
        stmtListTouchesUnsupportedHelperSurface elseBranch
  | .forEach _ count body =>
      exprTouchesUnsupportedHelperSurface count ||
        stmtListTouchesUnsupportedHelperSurface body

/-- Narrow helper-effect surface used by the exact helper-aware induction seam:
this isolates heads that genuinely execute internal helpers, leaving residual
non-helper unsupported cases to be tracked separately. -/
def stmtTouchesInternalHelperSurface : Stmt → Bool
  | .letVar _ value | .assignVar _ value | .setStorage _ value =>
      exprTouchesInternalHelperSurface value
  | .require cond _ | .return cond =>
      exprTouchesInternalHelperSurface cond
  | .internalCall _ _ | .internalCallAssign _ _ _ => true
  | .stop | .setStorageAddr _ _
  | .mstore _ _ | .tstore _ _ | .calldatacopy _ _ _
  | .returndataCopy _ _ _ | .revertReturndata | .externalCallBind _ _ _
  | .ecm _ _ | .setMapping _ _ _ | .setMappingWord _ _ _ _
  | .setMappingPackedWord _ _ _ _ _ | .setMapping2 _ _ _ _
  | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _ | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
  | .storageArrayPush _ _ | .storageArrayPop _
  | .setStorageArrayElement _ _ _ | .requireError _ _ _
  | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .emit _ _
  | .rawLog _ _ _ => false
  | .ite cond thenBranch elseBranch =>
      exprTouchesInternalHelperSurface cond ||
        stmtListTouchesInternalHelperSurface thenBranch ||
        stmtListTouchesInternalHelperSurface elseBranch
  | .forEach _ count body =>
      exprTouchesInternalHelperSurface count ||
        stmtListTouchesInternalHelperSurface body

/-- Direct statement-position internal helper execution. This is the part of the
exact helper seam that should consume the existing statement-level helper
summary lemmas from `SourceSemantics.lean`. -/
def stmtTouchesDirectInternalHelperSurface : Stmt → Bool
  | .internalCall _ _ =>
      true
  | .internalCallAssign _ _ _ =>
      true
  | _ => false

/-- Direct helper statements with no source-level return binding. These match
the `Stmt.internalCall` source-summary shape exactly. -/
def stmtTouchesDirectInternalHelperCallSurface : Stmt → Bool
  | .internalCall _ _ => true
  | _ => false

/-- Direct helper statements that bind helper returns into source locals. These
match the `Stmt.internalCallAssign` source-summary shape exactly. -/
def stmtTouchesDirectInternalHelperAssignSurface : Stmt → Bool
  | .internalCallAssign _ _ _ => true
  | _ => false

/-- Expression-position internal helper execution at the current statement head.
This isolates the cases that should consume the expression-level helper-summary
soundness and world-preservation lemmas directly, rather than bundling them
with direct helper statements or recursive structural transport. -/
def stmtTouchesExprInternalHelperSurface : Stmt → Bool
  | .letVar _ value | .assignVar _ value | .setStorage _ value =>
      exprTouchesInternalHelperSurface value
  | .require cond _ | .return cond =>
      exprTouchesInternalHelperSurface cond
  | .ite cond _ _ =>
      exprTouchesInternalHelperSurface cond
  | .forEach _ count _ =>
      exprTouchesInternalHelperSurface count
  | .internalCall _ _ | .internalCallAssign _ _ _ | .stop
  | .setStorageAddr _ _ | .mstore _ _ | .tstore _ _
  | .calldatacopy _ _ _ | .returndataCopy _ _ _
  | .revertReturndata | .externalCallBind _ _ _ | .ecm _ _
  | .setMapping _ _ _ | .setMappingWord _ _ _ _
  | .setMappingPackedWord _ _ _ _ _ | .setMapping2 _ _ _ _
  | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _
  | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
  | .storageArrayPush _ _ | .storageArrayPop _
  | .setStorageArrayElement _ _ _ | .requireError _ _ _
  | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .emit _ _
  | .rawLog _ _ _ => false

/-- Recursive structural internal-helper transport at the current statement
head. This isolates `ite` / `forEach` obligations whose proof burden is mainly
list-level recursion rather than direct helper-summary consumption. -/
def stmtTouchesStructuralInternalHelperSurface : Stmt → Bool
  | .ite _ thenBranch elseBranch =>
      stmtListTouchesInternalHelperSurface thenBranch ||
        stmtListTouchesInternalHelperSurface elseBranch
  | .forEach _ _ body =>
      stmtListTouchesInternalHelperSurface body
  | .letVar _ _ | .assignVar _ _ | .setStorage _ _ | .require _ _
  | .return _ | .internalCall _ _ | .internalCallAssign _ _ _
  | .stop | .setStorageAddr _ _ | .mstore _ _ | .tstore _ _
  | .calldatacopy _ _ _ | .returndataCopy _ _ _
  | .revertReturndata | .externalCallBind _ _ _ | .ecm _ _
  | .setMapping _ _ _ | .setMappingWord _ _ _ _
  | .setMappingPackedWord _ _ _ _ _ | .setMapping2 _ _ _ _
  | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _
  | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
  | .storageArrayPush _ _ | .storageArrayPop _
  | .setStorageArrayElement _ _ _ | .requireError _ _ _
  | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .emit _ _
  | .rawLog _ _ _ => false

def stmtTouchesUnsupportedForeignSurface : Stmt → Bool
  | .letVar _ value | .assignVar _ value | .setStorage _ value =>
      exprTouchesUnsupportedForeignSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedForeignSurface cond
  | .externalCallBind _ _ _ | .ecm _ _ => true
  | .stop | .setStorageAddr _ _
  | .internalCall _ _ | .internalCallAssign _ _ _ | .mstore _ _ | .tstore _ _
  | .calldatacopy _ _ _ | .returndataCopy _ _ _ | .revertReturndata
  | .setMapping _ _ _ | .setMappingWord _ _ _ _ | .setMappingPackedWord _ _ _ _ _
  | .setMapping2 _ _ _ _ | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _
  | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
  | .storageArrayPush _ _ | .storageArrayPop _ | .setStorageArrayElement _ _ _
  | .requireError _ _ _ | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .emit _ _ | .rawLog _ _ _ => false
  | .ite cond thenBranch elseBranch =>
      exprTouchesUnsupportedForeignSurface cond ||
        stmtListTouchesUnsupportedForeignSurface thenBranch ||
        stmtListTouchesUnsupportedForeignSurface elseBranch
  | .forEach _ count body =>
      exprTouchesUnsupportedForeignSurface count ||
        stmtListTouchesUnsupportedForeignSurface body

def stmtTouchesUnsupportedLowLevelSurface : Stmt → Bool
  | .letVar _ value | .assignVar _ value | .setStorage _ value =>
      exprTouchesUnsupportedLowLevelSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedLowLevelSurface cond
  | .calldatacopy _ _ _
  | .returndataCopy _ _ _ | .revertReturndata => true
  | .stop | .setStorageAddr _ _ | .mstore _ _ | .tstore _ _
  | .internalCall _ _ | .internalCallAssign _ _ _ | .externalCallBind _ _ _
  | .ecm _ _ | .setMapping _ _ _ | .setMappingWord _ _ _ _
  | .setMappingPackedWord _ _ _ _ _ | .setMapping2 _ _ _ _
  | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _ | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
  | .storageArrayPush _ _ | .storageArrayPop _ | .setStorageArrayElement _ _ _
  | .requireError _ _ _ | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .emit _ _ | .rawLog _ _ _ => false
  | .ite cond thenBranch elseBranch =>
      exprTouchesUnsupportedLowLevelSurface cond ||
        stmtListTouchesUnsupportedLowLevelSurface thenBranch ||
        stmtListTouchesUnsupportedLowLevelSurface elseBranch
  | .forEach _ count body =>
      exprTouchesUnsupportedLowLevelSurface count ||
        stmtListTouchesUnsupportedLowLevelSurface body

def stmtTouchesUnsupportedContractSurface (stmt : Stmt) : Bool :=
  match stmt with
  | .letVar _ value | .assignVar _ value | .setStorage _ value =>
      exprTouchesUnsupportedContractSurface value
  | .setStorageAddr _ value =>
      exprTouchesUnsupportedContractSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedContractSurface cond
  | .stop | .mstore _ _ | .tstore _ _ => false
  | .ite _ _ _ => true
  | .setMapping _ _ _ | .setMappingWord _ _ _ _ | .setMappingPackedWord _ _ _ _ _
  | .setMapping2 _ _ _ _ | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _
  | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
  | .storageArrayPush _ _ | .storageArrayPop _ | .setStorageArrayElement _ _ _
  | .requireError _ _ _ | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .calldatacopy _ _ _
  | .returndataCopy _ _ _ | .revertReturndata | .forEach _ _ _
  | .emit _ _ | .internalCall _ _ | .internalCallAssign _ _ _
  | .rawLog _ _ _ | .externalCallBind _ _ _ | .ecm _ _ => true

/-- Weaker contract-surface gate used by the Tier 2 singleton storage-write
bridge: ordinary unsupported contract effects remain excluded, but the proved
singleton mapping-write heads are admitted. -/
def stmtTouchesUnsupportedContractSurfaceExceptMappingWrites (stmt : Stmt) : Bool :=
  match stmt with
  | .setMapping _ _ _ | .setMappingWord _ _ _ _ | .setMappingPackedWord _ _ _ _ _
  | .setMapping2 _ _ _ _ | .setMapping2Word _ _ _ _ _
  | .setMappingUint _ _ _ | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _ => false
  | _ => stmtTouchesUnsupportedContractSurface stmt

def stmtListTouchesUnsupportedCoreSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedCoreSurface stmt ||
        stmtListTouchesUnsupportedCoreSurface rest

def stmtListTouchesUnsupportedStateSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedStateSurface stmt ||
        stmtListTouchesUnsupportedStateSurface rest

def stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedStateSurfaceExceptMappingWrites stmt ||
        stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites rest

def stmtListTouchesUnsupportedCallSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedCallSurface stmt ||
        stmtListTouchesUnsupportedCallSurface rest

def stmtListTouchesUnsupportedHelperSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedHelperSurface stmt ||
        stmtListTouchesUnsupportedHelperSurface rest

/-- List-level narrow helper-effect surface used to target only genuine
internal-helper execution in the exact helper-aware induction seam. -/
def stmtListTouchesInternalHelperSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesInternalHelperSurface stmt ||
        stmtListTouchesInternalHelperSurface rest

def stmtListTouchesDirectInternalHelperSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesDirectInternalHelperSurface stmt ||
        stmtListTouchesDirectInternalHelperSurface rest

def stmtListTouchesDirectInternalHelperCallSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesDirectInternalHelperCallSurface stmt ||
        stmtListTouchesDirectInternalHelperCallSurface rest

def stmtListTouchesDirectInternalHelperAssignSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesDirectInternalHelperAssignSurface stmt ||
        stmtListTouchesDirectInternalHelperAssignSurface rest

def stmtListTouchesExprInternalHelperSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesExprInternalHelperSurface stmt ||
        stmtListTouchesExprInternalHelperSurface rest

def stmtListTouchesStructuralInternalHelperSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesStructuralInternalHelperSurface stmt ||
        stmtListTouchesStructuralInternalHelperSurface rest

def stmtListTouchesUnsupportedForeignSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedForeignSurface stmt ||
        stmtListTouchesUnsupportedForeignSurface rest

def stmtListTouchesUnsupportedLowLevelSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedLowLevelSurface stmt ||
        stmtListTouchesUnsupportedLowLevelSurface rest

def stmtListTouchesUnsupportedEffectSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedEffectSurface stmt ||
        stmtListTouchesUnsupportedEffectSurface rest

/-- List-level weakening of `stmtListTouchesUnsupportedContractSurface` used by
the Tier 2 singleton mapping-write bridge. -/
def stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt ||
        stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites rest
end

mutual
  /-- Collect direct internal-helper callee names mentioned by an expression. This
  inventory is used to define a compositional helper-summary interface without yet
  changing the current generic theorem's fail-closed helper boundary. -/
  def exprInternalHelperCallNames : Expr → List String
    | .internalCall calleeName args =>
        calleeName :: exprListInternalHelperCallNames args
    | .mapping _ key | .mappingWord _ key _ | .mappingPackedWord _ key _ _
    | .mappingUint _ key | .structMember _ key _ | .arrayElement _ key
    | .storageArrayElement _ key | .mload key | .tload key | .calldataload key
    | .extcodesize key | .returndataOptionalBoolAt key =>
        exprInternalHelperCallNames key
    | .mappingChain _ keys =>
        exprListInternalHelperCallNames keys
    | .mapping2 _ key1 key2 | .mapping2Word _ key1 key2 _
    | .structMember2 _ key1 key2 _ =>
        exprInternalHelperCallNames key1 ++ exprInternalHelperCallNames key2
    | .call gas target value inOffset inSize outOffset outSize =>
        exprInternalHelperCallNames gas ++ exprInternalHelperCallNames target ++
          exprInternalHelperCallNames value ++ exprInternalHelperCallNames inOffset ++
          exprInternalHelperCallNames inSize ++ exprInternalHelperCallNames outOffset ++
          exprInternalHelperCallNames outSize
    | .staticcall gas target inOffset inSize outOffset outSize =>
        exprInternalHelperCallNames gas ++ exprInternalHelperCallNames target ++
          exprInternalHelperCallNames inOffset ++ exprInternalHelperCallNames inSize ++
          exprInternalHelperCallNames outOffset ++ exprInternalHelperCallNames outSize
    | .delegatecall gas target inOffset inSize outOffset outSize =>
        exprInternalHelperCallNames gas ++ exprInternalHelperCallNames target ++
          exprInternalHelperCallNames inOffset ++ exprInternalHelperCallNames inSize ++
          exprInternalHelperCallNames outOffset ++ exprInternalHelperCallNames outSize
    | .keccak256 offset size =>
        exprInternalHelperCallNames offset ++ exprInternalHelperCallNames size
    | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
    | .bitAnd a b | .bitOr a b | .bitXor a b | .shl a b | .shr a b | .sar a b
    | .signextend a b | .eq a b | .ge a b | .gt a b | .sgt a b | .lt a b
    | .slt a b | .le a b | .logicalAnd a b | .logicalOr a b | .wMulDown a b
    | .wDivUp a b | .min a b | .max a b =>
        exprInternalHelperCallNames a ++ exprInternalHelperCallNames b
    | .mulDivDown a b c | .mulDivUp a b c =>
        exprInternalHelperCallNames a ++ exprInternalHelperCallNames b ++
          exprInternalHelperCallNames c
    | .bitNot a | .logicalNot a =>
        exprInternalHelperCallNames a
    | .ite cond thenVal elseVal =>
        exprInternalHelperCallNames cond ++ exprInternalHelperCallNames thenVal ++
          exprInternalHelperCallNames elseVal
    | .externalCall _ args =>
        exprListInternalHelperCallNames args
    | _ =>
        []
  termination_by e => sizeOf e
  decreasing_by all_goals simp_wf; all_goals omega

  def exprListInternalHelperCallNames : List Expr → List String
    | [] => []
    | expr :: rest =>
        exprInternalHelperCallNames expr ++ exprListInternalHelperCallNames rest
  termination_by es => sizeOf es
  decreasing_by all_goals simp_wf; all_goals omega
end

mutual
  /-- Collect direct internal-helper callee names that occur specifically in expression
  positions. These calls must preserve the world on success because the current
  helper-aware expression semantics returns only a value. -/
  def stmtExprHelperCallNames : Stmt → List String
    | .letVar _ value | .assignVar _ value | .setStorage _ value | .setStorageAddr _ value
    | .storageArrayPush _ value | .return value | .require value _ =>
        exprInternalHelperCallNames value
    | .setStorageArrayElement _ index value =>
        exprInternalHelperCallNames index ++ exprInternalHelperCallNames value
    | .requireError cond _ args =>
        exprInternalHelperCallNames cond ++ exprListInternalHelperCallNames args
    | .revertError _ args | .emit _ args | .returnValues args
    | .externalCallBind _ _ args | .ecm _ args =>
        exprListInternalHelperCallNames args
    | .mstore offset value | .tstore offset value =>
        exprInternalHelperCallNames offset ++ exprInternalHelperCallNames value
    | .calldatacopy destOffset sourceOffset size
    | .returndataCopy destOffset sourceOffset size =>
        exprInternalHelperCallNames destOffset ++ exprInternalHelperCallNames sourceOffset ++
          exprInternalHelperCallNames size
    | .setMapping _ key value | .setMappingWord _ key _ value
    | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
    | .setStructMember _ key _ value =>
        exprInternalHelperCallNames key ++ exprInternalHelperCallNames value
    | .setMappingChain _ keys value =>
        exprListInternalHelperCallNames keys ++ exprInternalHelperCallNames value
    | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
    | .setStructMember2 _ key1 key2 _ value =>
        exprInternalHelperCallNames key1 ++ exprInternalHelperCallNames key2 ++
          exprInternalHelperCallNames value
    | .ite cond thenBranch elseBranch =>
        exprInternalHelperCallNames cond ++ stmtListExprHelperCallNames thenBranch ++
          stmtListExprHelperCallNames elseBranch
    | .forEach _ count body =>
        exprInternalHelperCallNames count ++ stmtListExprHelperCallNames body
    | .internalCall _ args | .internalCallAssign _ _ args =>
        exprListInternalHelperCallNames args
    | .rawLog topics dataOffset dataSize =>
        exprListInternalHelperCallNames topics ++ exprInternalHelperCallNames dataOffset ++
          exprInternalHelperCallNames dataSize
    | .storageArrayPop _ | .returnArray _ | .returnBytes _ | .returnStorageWords _
    | .revertReturndata | .stop =>
        []
  termination_by s => sizeOf s
  decreasing_by all_goals simp_wf; all_goals omega

  def stmtListExprHelperCallNames : List Stmt → List String
    | [] => []
    | stmt :: rest =>
        stmtExprHelperCallNames stmt ++ stmtListExprHelperCallNames rest
  termination_by stmts => sizeOf stmts
  decreasing_by all_goals simp_wf; all_goals omega
end

mutual
  /-- Collect direct internal-helper callee names mentioned by a statement list. -/
  def stmtInternalHelperCallNames : Stmt → List String
    | .letVar _ value | .assignVar _ value | .setStorage _ value | .setStorageAddr _ value
    | .storageArrayPush _ value | .return value | .require value _ =>
        exprInternalHelperCallNames value
    | .setStorageArrayElement _ index value =>
        exprInternalHelperCallNames index ++ exprInternalHelperCallNames value
    | .requireError cond _ args =>
        exprInternalHelperCallNames cond ++ exprListInternalHelperCallNames args
    | .revertError _ args | .emit _ args | .returnValues args
    | .externalCallBind _ _ args | .ecm _ args =>
        exprListInternalHelperCallNames args
    | .mstore offset value | .tstore offset value =>
        exprInternalHelperCallNames offset ++ exprInternalHelperCallNames value
    | .calldatacopy destOffset sourceOffset size
    | .returndataCopy destOffset sourceOffset size =>
        exprInternalHelperCallNames destOffset ++ exprInternalHelperCallNames sourceOffset ++
          exprInternalHelperCallNames size
    | .setMapping _ key value | .setMappingWord _ key _ value
    | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
    | .setStructMember _ key _ value =>
        exprInternalHelperCallNames key ++ exprInternalHelperCallNames value
    | .setMappingChain _ keys value =>
        exprListInternalHelperCallNames keys ++ exprInternalHelperCallNames value
    | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
    | .setStructMember2 _ key1 key2 _ value =>
        exprInternalHelperCallNames key1 ++ exprInternalHelperCallNames key2 ++
          exprInternalHelperCallNames value
    | .ite cond thenBranch elseBranch =>
        exprInternalHelperCallNames cond ++ stmtListInternalHelperCallNames thenBranch ++
          stmtListInternalHelperCallNames elseBranch
    | .forEach _ count body =>
        exprInternalHelperCallNames count ++ stmtListInternalHelperCallNames body
    | .internalCall calleeName args =>
        calleeName :: exprListInternalHelperCallNames args
    | .internalCallAssign _ calleeName args =>
        calleeName :: exprListInternalHelperCallNames args
    | .rawLog topics dataOffset dataSize =>
        exprListInternalHelperCallNames topics ++ exprInternalHelperCallNames dataOffset ++
          exprInternalHelperCallNames dataSize
    | .storageArrayPop _ | .returnArray _ | .returnBytes _ | .returnStorageWords _
    | .revertReturndata | .stop =>
        []
  termination_by s => sizeOf s
  decreasing_by all_goals simp_wf; all_goals omega

  def stmtListInternalHelperCallNames : List Stmt → List String
    | [] => []
    | stmt :: rest =>
        stmtInternalHelperCallNames stmt ++ stmtListInternalHelperCallNames rest
  termination_by stmts => sizeOf stmts
  decreasing_by all_goals simp_wf; all_goals omega
end

private theorem nodup_reverse' {l : List α} (h : l.Nodup) : l.reverse.Nodup := by
  rw [show l.reverse.Nodup ↔ List.Pairwise (fun a b => a ≠ b) l.reverse from Iff.rfl]
  rw [List.pairwise_reverse]
  exact h.imp (fun h1 h2 => h1 h2.symm)

private theorem nodup_eraseDupsBy_loop [BEq α] [LawfulBEq α]
    (l acc : List α)
    (hacc : acc.Nodup) :
    (List.eraseDupsBy.loop (· == ·) l acc).Nodup := by
  induction l generalizing acc with
  | nil =>
    simp [List.eraseDupsBy.loop]
    exact nodup_reverse' hacc
  | cons a t ih =>
    simp only [List.eraseDupsBy.loop]
    split
    · exact ih acc hacc
    · rename_i hnotin
      apply ih
      rw [List.nodup_cons]
      refine ⟨?_, hacc⟩
      intro hmem
      have : (acc.any fun x2 => a == x2) = true := by
        rw [List.any_eq_true]
        exact ⟨a, hmem, beq_self_eq_true a⟩
      simp [this] at hnotin

theorem List.nodup_eraseDups [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.Nodup := by
  simp only [List.eraseDups]
  exact nodup_eraseDupsBy_loop l [] List.Pairwise.nil

private theorem mem_eraseDups_iff [BEq α] [LawfulBEq α] {a : α} {l : List α} :
    a ∈ l.eraseDups ↔ a ∈ l := by
  constructor
  · intro h
    simp only [List.eraseDups] at h
    have loop_sub : ∀ (l acc : List α) (x : α),
      x ∈ (List.eraseDupsBy.loop (· == ·) l acc) → x ∈ acc ∨ x ∈ l := by
      intro l; induction l with
      | nil =>
        intro acc x hx; simp [List.eraseDupsBy.loop] at hx
        left; exact hx
      | cons b t ih =>
        intro acc x hx; simp only [List.eraseDupsBy.loop] at hx
        split at hx
        · rcases ih acc x hx with hacc | ht
          · left; exact hacc
          · right; exact List.mem_cons_of_mem _ ht
        · rcases ih (b :: acc) x hx with hacc | ht
          · rw [List.mem_cons] at hacc
            rcases hacc with rfl | hmem
            · right; simp
            · left; exact hmem
          · right; exact List.mem_cons_of_mem _ ht
    rcases loop_sub l [] a h with hacc | hl
    · simp at hacc
    · exact hl
  · intro h
    simp only [List.eraseDups]
    have loop_mem : ∀ (l acc : List α) (x : α),
      (x ∈ l ∨ x ∈ acc) → x ∈ (List.eraseDupsBy.loop (· == ·) l acc) := by
      intro l; induction l with
      | nil =>
        intro acc x hx; simp [List.eraseDupsBy.loop]
        rcases hx with hx | hx
        · simp at hx
        · exact hx
      | cons b t ih =>
        intro acc x hx; simp only [List.eraseDupsBy.loop]
        split
        · apply ih acc x
          rcases hx with hx | hx
          · rw [List.mem_cons] at hx
            rcases hx with rfl | ht
            · right
              rename_i hany
              rw [List.any_eq_true] at hany
              obtain ⟨y, hy, hbeq⟩ := hany
              rw [beq_iff_eq] at hbeq
              rw [hbeq]; exact hy
            · left; exact ht
          · right; exact hx
        · apply ih (b :: acc) x
          rcases hx with hx | hx
          · rw [List.mem_cons] at hx
            rcases hx with rfl | ht
            · right; simp
            · left; exact ht
          · right; rw [List.mem_cons]; right; exact hx
    exact loop_mem l [] a (Or.inl h)

/-- Deduplicated direct helper-callee inventory for a function body. -/
def helperCallNames (fn : FunctionSpec) : List String :=
  (stmtListInternalHelperCallNames fn.body).eraseDups

theorem helperCallNames_nodup (fn : FunctionSpec) :
    (helperCallNames fn).Nodup := by
  simpa [helperCallNames] using List.nodup_eraseDups (stmtListInternalHelperCallNames fn.body)

/-- Deduplicated direct helper-callee inventory for expression-position helper uses. -/
def exprHelperCallNames (fn : FunctionSpec) : List String :=
  (stmtListExprHelperCallNames fn.body).eraseDups

theorem exprHelperCallNames_nodup (fn : FunctionSpec) :
    (exprHelperCallNames fn).Nodup := by
  simpa [exprHelperCallNames] using List.nodup_eraseDups (stmtListExprHelperCallNames fn.body)

private def stmtExprHelperCallNames_subset_stmtInternalHelperCallNames_aux :
    (stmts : List Stmt) →
    ∀ {calleeName : String},
      calleeName ∈ stmtListExprHelperCallNames stmts →
        calleeName ∈ stmtListInternalHelperCallNames stmts
  | [], _, hmem => by simpa [stmtListExprHelperCallNames, stmtListInternalHelperCallNames] using hmem
  | stmt :: rest, calleeName, hmem => by
      simp only [stmtListExprHelperCallNames, stmtListInternalHelperCallNames, List.mem_append] at hmem ⊢
      rcases hmem with hstmt | hrest
      · left
        revert hstmt
        cases stmt with
        | ite cond thenBranch elseBranch =>
            intro hstmt
            simp only [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_append] at hstmt ⊢
            rcases hstmt with (hcond | hthen) | helse
            · left; left; exact hcond
            · left; right
              exact stmtExprHelperCallNames_subset_stmtInternalHelperCallNames_aux _ hthen
            · right
              exact stmtExprHelperCallNames_subset_stmtInternalHelperCallNames_aux _ helse
        | forEach var count body =>
            intro hstmt
            simp only [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_append] at hstmt ⊢
            rcases hstmt with hcount | hbody
            · exact Or.inl hcount
            · exact Or.inr <| stmtExprHelperCallNames_subset_stmtInternalHelperCallNames_aux _ hbody
        | internalCall calleeName args =>
            intro hstmt
            simp [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_cons] at hstmt ⊢
            exact Or.inr hstmt
        | internalCallAssign names calleeName args =>
            intro hstmt
            simp [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_cons] at hstmt ⊢
            exact Or.inr hstmt
        | _ =>
            intro hstmt
            all_goals
              first
              | simpa [stmtExprHelperCallNames, stmtInternalHelperCallNames] using hstmt
              | simpa [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_append] using hstmt
              | simpa [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_append,
                  or_left_comm, or_assoc] using hstmt
      · exact Or.inr (stmtExprHelperCallNames_subset_stmtInternalHelperCallNames_aux rest hrest)
  termination_by l => sizeOf l

theorem stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames
    (stmts : List Stmt) :
    ∀ {calleeName : String},
      calleeName ∈ stmtListExprHelperCallNames stmts →
        calleeName ∈ stmtListInternalHelperCallNames stmts :=
  stmtExprHelperCallNames_subset_stmtInternalHelperCallNames_aux stmts

theorem stmtExprHelperCallNames_subset_stmtInternalHelperCallNames
    (stmt : Stmt) :
    ∀ {calleeName : String},
      calleeName ∈ stmtExprHelperCallNames stmt →
        calleeName ∈ stmtInternalHelperCallNames stmt := by
  intro calleeName hmem
  have h := @stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames [stmt] calleeName
  simp only [stmtListExprHelperCallNames, stmtListInternalHelperCallNames,
    List.mem_append, List.not_mem_nil, or_false] at h
  exact h hmem

theorem exprHelperCallNames_subset_helperCallNames
    {fn : FunctionSpec}
    {calleeName : String}
    (hmem : calleeName ∈ exprHelperCallNames fn) :
    calleeName ∈ helperCallNames fn := by
  have hexpr : calleeName ∈ stmtListExprHelperCallNames fn.body :=
    mem_eraseDups_iff.mp hmem
  have hhelper : calleeName ∈ stmtListInternalHelperCallNames fn.body :=
    stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames fn.body hexpr
  exact mem_eraseDups_iff.mpr hhelper

/-- Compatibility scan retained for the existing generic-induction library.
Its meaning is now derived from smaller feature-local interfaces rather than a
single undifferentiated exclusion bag. -/
def stmtListTouchesUnsupportedContractSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedContractSurface stmt ||
        stmtListTouchesUnsupportedContractSurface rest

example :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.ite (.literal 1) [Stmt.internalCall "helper" []] []] = true := by
  decide

example :
    stmtListTouchesUnsupportedForeignSurface
      [Stmt.forEach "i" (.literal 1) [Stmt.externalCallBind [] "ext" []]] = true := by
  decide

example :
    stmtListTouchesUnsupportedEffectSurface
      [Stmt.ite (.literal 1) [Stmt.emit "Evt" []] []] = true := by
  decide

example :
    exprTouchesUnsupportedHelperSurface
      (.mappingChain "balances" [Expr.internalCall "helper" []]) = true := by
  decide

example :
    exprTouchesInternalHelperSurface
      (.mappingChain "balances" [Expr.literal 1]) = false := by
  decide

example :
    exprTouchesInternalHelperSurface
      (.mappingChain "balances" [Expr.internalCall "helper" []]) = true := by
  decide

example :
    exprTouchesUnsupportedCallSurface
      (.mappingChain "balances" [Expr.internalCall "helper" []]) = true := by
  decide

structure SupportedBodyCoreInterface (fn : FunctionSpec) : Prop where
  surfaceClosed : stmtListTouchesUnsupportedCoreSurface fn.body = false

structure SupportedBodyStateInterface (fn : FunctionSpec) : Prop where
  surfaceClosed : stmtListTouchesUnsupportedStateSurface fn.body = false

structure SupportedBodyStateInterfaceExceptMappingWrites (fn : FunctionSpec) : Prop where
  surfaceClosed : stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites fn.body = false

structure InternalHelperSummaryContract where
  post : Nat → Verity.ContractState → List Nat → Bool → Option Nat → Verity.ContractState → Prop

def InternalHelperSummaryPreservesWorldOnSuccess
    (summary : InternalHelperSummaryContract) : Prop :=
  ∀ fuel initialWorld args success returnValue finalWorld,
    summary.post fuel initialWorld args success returnValue finalWorld →
      success = true →
      finalWorld = initialWorld

structure SupportedBodyEffectInterface (fn : FunctionSpec) : Prop where
  surfaceClosed : stmtListTouchesUnsupportedEffectSurface fn.body = false

structure SupportedInternalHelperSummary (spec : CompilationModel) (callee : FunctionSpec) where
  present : callee ∈ spec.functions
  internal : callee.isInternal = true
  nonSpecialEntrypoint : isInteropEntrypointName callee.name = false
  helperRank : Nat
  params : SupportedParamProfile callee.params
  returns : SupportedReturnProfile callee
  core : SupportedBodyCoreInterface callee
  state : SupportedBodyStateInterface callee
  foreign : stmtListTouchesUnsupportedForeignSurface callee.body = false
  lowLevel : stmtListTouchesUnsupportedLowLevelSurface callee.body = false
  effects : SupportedBodyEffectInterface callee
  contract : InternalHelperSummaryContract
  noLocalObligations : callee.localObligations = []

structure SupportedInternalHelperWitness
    (spec : CompilationModel) (calleeName : String) where
  callee : FunctionSpec
  summary : SupportedInternalHelperSummary spec callee
  nameEq : callee.name = calleeName

/-- Compiled-side witness for a source-defined internal helper inside a runtime
contract's helper table. This is the compositional bridge between the
source-side helper summary inventory and the helper-aware IR interpreter target:
it records exactly which internal-function definition in `runtimeContract`
came from compiling a supported source helper. -/
structure SupportedCompiledInternalHelperWitness
    (spec : CompilationModel)
    (runtimeContract : IRContract)
    (calleeName : String) where
  sourceWitness : SupportedInternalHelperWitness spec calleeName
  compiledStmt : YulStmt
  compileOk :
    compileInternalFunction
        (applySlotAliasRanges spec.fields spec.slotAliasRanges)
        spec.events
        spec.errors
        sourceWitness.callee =
      Except.ok compiledStmt
  presentInRuntime :
    compiledStmt ∈ runtimeContract.internalFunctions

/-- Runtime-contract inventory of source-defined internal helpers.
This keeps future exact helper-step proofs generic: they can require a
compositional mapping from source helper witnesses to compiled helper bodies,
instead of baking ad hoc assumptions about a particular runtime contract's
internal helper table into each theorem. -/
structure SupportedRuntimeHelperTableInterface
    (spec : CompilationModel)
    (runtimeContract : IRContract) where
  compiledOfWitness :
    ∀ calleeName (witness : SupportedInternalHelperWitness spec calleeName),
      SupportedCompiledInternalHelperWitness spec runtimeContract calleeName

/-- Helper-call boundary for the current generic theorem.
It already inventories helper callees via positive summary witnesses, but it
still carries the helper-excluding body fragment witness, so the generic theorem
shape and trusted boundary remain unchanged until helper semantics are modeled. -/
structure SupportedBodyHelperInterface (spec : CompilationModel) (fn : FunctionSpec) where
  helperRank : Nat
  callNamesNodup : (helperCallNames fn).Nodup
  summaryOf :
    ∀ calleeName, calleeName ∈ helperCallNames fn →
      SupportedInternalHelperWitness spec calleeName
  calleeRanksDecrease :
    ∀ calleeName (hmem : calleeName ∈ helperCallNames fn),
      (summaryOf calleeName hmem).summary.helperRank < helperRank
  exprCallsPreserveWorld :
    ∀ calleeName (hmem : calleeName ∈ exprHelperCallNames fn),
      let hcall : calleeName ∈ helperCallNames fn :=
        exprHelperCallNames_subset_helperCallNames hmem
      InternalHelperSummaryPreservesWorldOnSuccess
        ((summaryOf calleeName hcall).summary.contract)

structure SupportedBodyCallInterface (spec : CompilationModel) (fn : FunctionSpec) where
  helpers : SupportedBodyHelperInterface spec fn
  foreign : stmtListTouchesUnsupportedForeignSurface fn.body = false
  lowLevel : stmtListTouchesUnsupportedLowLevelSurface fn.body = false


/-- Body-level interface for the initial theorem boundary. This keeps the current
syntactic support inventory local to the body witness instead of baking it
directly into the top-level `SupportedSpec` inventory. Each sub-interface is a
feature-local place to hang future widening work. -/
structure SupportedBodyInterface (spec : CompilationModel) (fn : FunctionSpec) where
  stmtList : SupportedStmtList spec.fields (fn.params.map (·.name)) fn.body
  core : SupportedBodyCoreInterface fn
  state : SupportedBodyStateInterface fn
  calls : SupportedBodyCallInterface spec fn
  effects : SupportedBodyEffectInterface fn
  noLocalObligations : fn.localObligations = []

/-- Tier 2 body-level interface that weakens only the state-surface closure to
admit the currently proved singleton storage-write shapes; all other fail-closed
boundaries remain unchanged. -/
structure SupportedBodyInterfaceExceptMappingWrites
    (spec : CompilationModel) (fn : FunctionSpec) where
  stmtList : SupportedStmtList spec.fields (fn.params.map (·.name)) fn.body
  core : SupportedBodyCoreInterface fn
  state : SupportedBodyStateInterfaceExceptMappingWrites fn
  calls : SupportedBodyCallInterface spec fn
  effects : SupportedBodyEffectInterface fn
  noLocalObligations : fn.localObligations = []

/-- Supported external function for the first whole-contract Layer 2 theorem.
This lifts the raw `SupportedStmtList` witness to the function boundary and
makes the whole-contract scope auditable without proof-internal inspection. -/
structure SupportedFunction (spec : CompilationModel) (fn : FunctionSpec) where
  nonInternal : fn.isInternal = false
  nonSpecialEntrypoint : isInteropEntrypointName fn.name = false
  params : SupportedParamProfile fn.params
  returns : SupportedReturnProfile fn
  body : SupportedBodyInterface spec fn

/-- Tier 2 function-level support witness that weakens only the body state
surface closure to admit the currently proved singleton storage-write shapes. -/
structure SupportedFunctionExceptMappingWrites
    (spec : CompilationModel) (fn : FunctionSpec) where
  nonInternal : fn.isInternal = false
  nonSpecialEntrypoint : isInteropEntrypointName fn.name = false
  params : SupportedParamProfile fn.params
  returns : SupportedReturnProfile fn
  body : SupportedBodyInterfaceExceptMappingWrites spec fn

/-- Whole-contract invariants that should remain global preconditions for the
current generic theorem, independent of feature-local proof interfaces. -/
structure SupportedSpecInvariants (spec : CompilationModel) (selectors : List Nat) : Prop where
  normalizedFields :
    applySlotAliasRanges spec.fields spec.slotAliasRanges = spec.fields
  noPackedFields :
    ∀ field ∈ spec.fields, field.packedBits = none
  selectorCount : selectors.length = (selectorDispatchedFunctions spec).length
  selectorsDistinct : firstDuplicateSelector selectors = none
  functionNamesNodup : (spec.functions.map (·.name)).Nodup

/-- Whole-contract surfaces intentionally still outside the initial theorem,
kept separate from global normalization/dispatch invariants so future widening
can replace these by dedicated proof interfaces feature-by-feature. -/
structure SupportedSpecSurface (spec : CompilationModel) : Prop where
  noConstructor : spec.constructor = none
  noEvents : spec.events = []
  noErrors : spec.errors = []
  noExternals : spec.externals = []
  noFallback :
    ∀ fn ∈ spec.functions, fn.name != "fallback"
  noReceive :
    ∀ fn ∈ spec.functions, fn.name != "receive"

/-- Whole-contract support witness for the first generic Layer 2 theorem.
The initial scope is deliberately narrow: selector-dispatched external entrypoints only,
no constructor, no fallback/receive, no foreign/linking surface, and every function body
must already live inside the explicit supported statement fragment. -/
structure SupportedSpec (spec : CompilationModel) (selectors : List Nat) where
  invariants : SupportedSpecInvariants spec selectors
  surface : SupportedSpecSurface spec
  functions :
    ∀ fn, fn ∈ spec.functions → SupportedFunction spec fn

/-- Tier 2 whole-contract support witness that weakens only the function-body
state closure to admit the currently proved singleton storage-write shapes. -/
structure SupportedSpecExceptMappingWrites
    (spec : CompilationModel) (selectors : List Nat) where
  invariants : SupportedSpecInvariants spec selectors
  surface : SupportedSpecSurface spec
  functions :
    ∀ fn, fn ∈ spec.functions → SupportedFunctionExceptMappingWrites spec fn

theorem SupportedFunction.paramNamesNodup
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunction spec fn) :
    (fn.params.map (·.name)).Nodup :=
  hSupported.params.namesNodup

theorem SupportedFunction.paramsSupported
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunction spec fn) :
    ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
  hSupported.params.supported

theorem SupportedFunction.returnsSupported
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunction spec fn) :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns :=
  hSupported.returns.resolved

theorem SupportedFunctionExceptMappingWrites.paramNamesNodup
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunctionExceptMappingWrites spec fn) :
    (fn.params.map (·.name)).Nodup :=
  hSupported.params.namesNodup

theorem SupportedFunctionExceptMappingWrites.paramsSupported
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunctionExceptMappingWrites spec fn) :
    ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
  hSupported.params.supported

theorem SupportedFunctionExceptMappingWrites.returnsSupported
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunctionExceptMappingWrites spec fn) :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns :=
  hSupported.returns.resolved

def SupportedFunction.helperFuel
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunction spec fn) : Nat :=
  hSupported.body.calls.helpers.helperRank

def SupportedFunctionExceptMappingWrites.helperFuel
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunctionExceptMappingWrites spec fn) : Nat :=
  hSupported.body.calls.helpers.helperRank

private theorem exprCompileCore_helperSurfaceClosed
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    exprTouchesUnsupportedHelperSurface expr = false := by
  induction hcore with
  | literal | param | localVar | caller | contractAddress | msgValue
    | blockTimestamp | blockNumber | chainid =>
      simp [exprTouchesUnsupportedHelperSurface]
  | add _ _ ihL ihR
    | sub _ _ ihL ihR
    | mul _ _ ihL ihR
    | div _ _ ihL ihR
    | mod _ _ ihL ihR
    | eq _ _ ihL ihR
    | lt _ _ ihL ihR
    | gt _ _ ihL ihR
    | ge _ _ ihL ihR
    | le _ _ ihL ihR
    | logicalAnd _ _ ihL ihR
    | logicalOr _ _ ihL ihR =>
      simp [exprTouchesUnsupportedHelperSurface, ihL, ihR]
  | logicalNot _ ih =>
      simp [exprTouchesUnsupportedHelperSurface, ih]

private theorem exprCompileCore_internalHelperCallNames_nil
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    exprInternalHelperCallNames expr = [] := by
  induction hcore with
  | literal | param | localVar | caller | contractAddress | msgValue
    | blockTimestamp | blockNumber | chainid =>
      simp [exprInternalHelperCallNames]
  | add _ _ ihL ihR
    | sub _ _ ihL ihR
    | mul _ _ ihL ihR
    | div _ _ ihL ihR
    | mod _ _ ihL ihR
    | eq _ _ ihL ihR
    | lt _ _ ihL ihR
    | gt _ _ ihL ihR
    | ge _ _ ihL ihR
    | le _ _ ihL ihR
    | logicalAnd _ _ ihL ihR
    | logicalOr _ _ ihL ihR =>
      simp [exprInternalHelperCallNames, ihL, ihR]
  | logicalNot _ ih =>
      simp [exprInternalHelperCallNames, ih]

private theorem exprListCompileCore_helperSurfaceClosed
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    exprListTouchesUnsupportedHelperSurface exprs = false := by
  induction exprs with
  | nil =>
      simp [exprListTouchesUnsupportedHelperSurface]
  | cons expr rest ih =>
      have hhead : FunctionBody.ExprCompileCore expr := hcore expr (by simp)
      have htail : ∀ e ∈ rest, FunctionBody.ExprCompileCore e := by
        intro e he
        exact hcore e (by simp [he])
      simp [exprListTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hhead,
        ih htail]

private theorem exprListCompileCore_internalHelperCallNames_nil
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    exprListInternalHelperCallNames exprs = [] := by
  induction exprs with
  | nil =>
      simp [exprListInternalHelperCallNames]
  | cons expr rest ih =>
      have hhead : FunctionBody.ExprCompileCore expr := hcore expr (by simp)
      have htail : ∀ e ∈ rest, FunctionBody.ExprCompileCore e := by
        intro e he
        exact hcore e (by simp [he])
      simp [exprListInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hhead,
        ih htail]

private theorem stmtListCompileCore_helperSurfaceClosed
    {scope : List String}
    {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  induction hcore with
  | nil =>
      simp [stmtListTouchesUnsupportedHelperSurface]
  | letVar hcore _ _ ih
    | assignVar hcore _ _ ih
    | return_ hcore _ _ ih =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hcore,
        ih]
  | require_ hcore _ _ ih =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hcore,
        ih]
  | stop _ ih =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        ih]

private theorem stmtListCompileCore_internalHelperCallNames_nil
    {scope : List String}
    {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    stmtListInternalHelperCallNames stmts = [] := by
  induction hcore with
  | nil =>
      simp [stmtListInternalHelperCallNames]
  | letVar hexpr _ _ ih
    | assignVar hexpr _ _ ih
    | return_ hexpr _ _ ih
    | require_ hexpr _ _ ih =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hexpr,
        ih]
  | stop _ ih =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames, ih]

private theorem stmtListTerminalCore_helperSurfaceClosed
    {scope : List String}
    {stmts : List Stmt}
    (hterminal : FunctionBody.StmtListTerminalCore scope stmts) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  induction hterminal with
  | letVar hcore _ _ ih
    | assignVar hcore _ _ ih =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hcore,
        ih]
  | require_ hcore _ _ ih =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hcore,
        ih]
  | return_ hcore _ hrest =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hcore,
        stmtListCompileCore_helperSurfaceClosed hrest]
  | stop hrest =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        stmtListCompileCore_helperSurfaceClosed hrest]
  | ite hcond _ hthen helse hrest ihThen ihElse =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hcond,
        ihThen, ihElse,
        stmtListCompileCore_helperSurfaceClosed hrest]

private theorem supportedStmtList_returnMapping_helperSurfaceClosed
    {fieldName : String}
    {key : Expr}
    (hkey : FunctionBody.ExprCompileCore key) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.return (Expr.mapping fieldName key)] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey]

private theorem supportedStmtList_letStorageField_helperSurfaceClosed
    {tmp fieldName : String} :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.letVar tmp (Expr.storage fieldName)] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface]

private theorem supportedStmtList_setStorageAddrSingleSlot_helperSurfaceClosed
    {fieldName : String}
    {value : Expr}
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setStorageAddr fieldName value] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hvalue]

private theorem supportedStmtList_mstoreSingle_helperSurfaceClosed
    {offset value : Expr}
    (hoffset : FunctionBody.ExprCompileCore offset)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.mstore offset value] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hoffset,
    exprCompileCore_helperSurfaceClosed hvalue]

private theorem supportedStmtList_tstoreSingle_helperSurfaceClosed
    {offset value : Expr}
    (hoffset : FunctionBody.ExprCompileCore offset)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.tstore offset value] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hoffset,
    exprCompileCore_helperSurfaceClosed hvalue]

private theorem supportedStmtList_letMapping_helperSurfaceClosed
    {tmp fieldName : String}
    {key : Expr}
    (hkey : FunctionBody.ExprCompileCore key) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.letVar tmp (Expr.mapping fieldName key)] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey]

private theorem supportedStmtList_letMapping2_helperSurfaceClosed
    {tmp fieldName : String}
    {key1 key2 : Expr}
    (hkey1 : FunctionBody.ExprCompileCore key1)
    (hkey2 : FunctionBody.ExprCompileCore key2) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.letVar tmp (Expr.mapping2 fieldName key1 key2)] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey1,
    exprCompileCore_helperSurfaceClosed hkey2]

private theorem supportedStmtList_letMappingUint_helperSurfaceClosed
    {tmp fieldName : String}
    {key : Expr}
    (hkey : FunctionBody.ExprCompileCore key) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.letVar tmp (Expr.mappingUint fieldName key)] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey]

private theorem supportedStmtList_setMappingUintSingle_helperSurfaceClosed
    {fieldName : String}
    {key value : Expr}
    (hkey : FunctionBody.ExprCompileCore key)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setMappingUint fieldName key value] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey,
    exprCompileCore_helperSurfaceClosed hvalue]

private theorem supportedStmtList_setMappingChainSingle_helperSurfaceClosed
    {fieldName : String}
    {keys : List Expr}
    {value : Expr}
    (hkeys : ∀ key ∈ keys, FunctionBody.ExprCompileCore key)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setMappingChain fieldName keys value] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprListCompileCore_helperSurfaceClosed hkeys,
    exprCompileCore_helperSurfaceClosed hvalue]

private theorem supportedStmtList_setMappingSingle_helperSurfaceClosed
    {fieldName : String}
    {key value : Expr}
    (hkey : FunctionBody.ExprCompileCore key)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setMapping fieldName key value] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey,
    exprCompileCore_helperSurfaceClosed hvalue]

private theorem supportedStmtList_setMappingWordSingle_helperSurfaceClosed
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    (hkey : FunctionBody.ExprCompileCore key)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setMappingWord fieldName key wordOffset value] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey,
    exprCompileCore_helperSurfaceClosed hvalue]

private theorem supportedStmtList_setStructMemberSingle_helperSurfaceClosed
    {fieldName memberName : String}
    {key value : Expr}
    (hkey : FunctionBody.ExprCompileCore key)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setStructMember fieldName key memberName value] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey,
    exprCompileCore_helperSurfaceClosed hvalue]

private theorem supportedStmtList_setMapping2Single_helperSurfaceClosed
    {fieldName : String}
    {key1 key2 value : Expr}
    (hkey1 : FunctionBody.ExprCompileCore key1)
    (hkey2 : FunctionBody.ExprCompileCore key2)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setMapping2 fieldName key1 key2 value] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey1,
    exprCompileCore_helperSurfaceClosed hkey2,
    exprCompileCore_helperSurfaceClosed hvalue]

private theorem supportedStmtList_setMapping2WordSingle_helperSurfaceClosed
    {fieldName : String}
    {key1 key2 value : Expr}
    {wordOffset : Nat}
    (hkey1 : FunctionBody.ExprCompileCore key1)
    (hkey2 : FunctionBody.ExprCompileCore key2)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setMapping2Word fieldName key1 key2 wordOffset value] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey1,
    exprCompileCore_helperSurfaceClosed hkey2,
    exprCompileCore_helperSurfaceClosed hvalue]

private theorem supportedStmtList_setMappingPackedWordSingle_helperSurfaceClosed
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {packed : PackedBits}
    (hkey : FunctionBody.ExprCompileCore key)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setMappingPackedWord fieldName key wordOffset packed value] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey,
    exprCompileCore_helperSurfaceClosed hvalue]

private theorem supportedStmtList_setStructMember2Single_helperSurfaceClosed
    {fieldName memberName : String}
    {key1 key2 value : Expr}
    (hkey1 : FunctionBody.ExprCompileCore key1)
    (hkey2 : FunctionBody.ExprCompileCore key2)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setStructMember2 fieldName key1 key2 memberName value] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey1,
    exprCompileCore_helperSurfaceClosed hkey2,
    exprCompileCore_helperSurfaceClosed hvalue]

private theorem supportedStmtList_rawLogLiterals_helperSurfaceClosed
    {topics : List Nat}
    {dataOffset dataSize : Nat} :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.rawLog (topics.map Expr.literal) (Expr.literal dataOffset) (Expr.literal dataSize)] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface]

private theorem supportedStmtList_letCallerLetStorageReqEqReqNeqSetStorageParamStop_helperSurfaceClosed
    {ownerField senderVar ownerVar paramName msg1 msg2 : String} :
    stmtListTouchesUnsupportedHelperSurface
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar ownerVar (Expr.storage ownerField)
      , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
      , Stmt.require
          (Expr.logicalNot (Expr.eq (Expr.param paramName) (Expr.localVar ownerVar))) msg2
      , Stmt.setStorage ownerField (Expr.param paramName)
      , Stmt.stop
      ] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface]

private theorem supportedStmtList_letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop_helperSurfaceClosed
    {ownerField targetField senderVar ownerVar targetVar paramName msg1 msg2 : String} :
    stmtListTouchesUnsupportedHelperSurface
      [ Stmt.letVar senderVar Expr.caller
      , Stmt.letVar ownerVar (Expr.storage ownerField)
      , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
      , Stmt.letVar targetVar (Expr.storage targetField)
      , Stmt.require
          (Expr.logicalNot (Expr.eq (Expr.param paramName) (Expr.localVar targetVar))) msg2
      , Stmt.setStorage targetField (Expr.param paramName)
      , Stmt.stop
      ] = false := by
  simp [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface]

private theorem stmtListTouchesUnsupportedHelperSurface_append
    {pfx sfx : List Stmt} :
    stmtListTouchesUnsupportedHelperSurface (pfx ++ sfx) =
      (stmtListTouchesUnsupportedHelperSurface pfx ||
        stmtListTouchesUnsupportedHelperSurface sfx) := by
  induction pfx with
  | nil => simp [stmtListTouchesUnsupportedHelperSurface]
  | cons head rest ih =>
    simp [stmtListTouchesUnsupportedHelperSurface, ih, Bool.or_assoc]

theorem SupportedStmtList.helperSurfaceClosed
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hSupported : SupportedStmtList fields scope stmts) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  induction hSupported with
  | compileCore hcore => exact stmtListCompileCore_helperSurfaceClosed hcore
  | terminalCore hterminal => exact stmtListTerminalCore_helperSurfaceClosed hterminal
  | setStorageSingleSlot hcore hinScope hfind =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hcore]
  | setStorageAddrSingleSlot hcore hinScope hfind =>
      exact supportedStmtList_setStorageAddrSingleSlot_helperSurfaceClosed hcore
  | mstoreSingle hoffset hscopeOffset hvalue hscopeValue =>
      exact supportedStmtList_mstoreSingle_helperSurfaceClosed hoffset hvalue
  | tstoreSingle hoffset hscopeOffset hvalue hscopeValue =>
      exact supportedStmtList_tstoreSingle_helperSurfaceClosed hoffset hvalue
  | letStorageField hfind => exact supportedStmtList_letStorageField_helperSurfaceClosed
  | returnMapping hkey hscope hslot => exact supportedStmtList_returnMapping_helperSurfaceClosed hkey
  | letMapping hkey hscope hslot => exact supportedStmtList_letMapping_helperSurfaceClosed hkey
  | letMapping2 hkey1 hscope1 hkey2 hscope2 hslot => exact supportedStmtList_letMapping2_helperSurfaceClosed hkey1 hkey2
  | letMappingUint hkey hscope hslot => exact supportedStmtList_letMappingUint_helperSurfaceClosed hkey
  | setMappingUintSingle hkey hscopeKey hvalue hscopeValue hslot => exact supportedStmtList_setMappingUintSingle_helperSurfaceClosed hkey hvalue
  | setMappingChainSingle hkeys hscopeKeys hvalue hscopeValue hslot =>
      exact supportedStmtList_setMappingChainSingle_helperSurfaceClosed hkeys hvalue
  | setMappingSingle hkey hscopeKey hvalue hscopeValue hslot => exact supportedStmtList_setMappingSingle_helperSurfaceClosed hkey hvalue
  | setMappingWordSingle hkey hscopeKey hvalue hscopeValue hslot =>
      exact supportedStmtList_setMappingWordSingle_helperSurfaceClosed hkey hvalue
  | setMappingPackedWordSingle hkey hscopeKey hvalue hscopeValue
      hcompatValue hcompatPacked hcompatSlotWord hcompatSlotCleared hpacked hslot =>
      exact supportedStmtList_setMappingPackedWordSingle_helperSurfaceClosed hkey hvalue
  | setStructMemberSingle hkey hscopeKey hvalue hscopeValue hslot hmembers hmember =>
      exact supportedStmtList_setStructMemberSingle_helperSurfaceClosed hkey hvalue
  | setMapping2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot => exact supportedStmtList_setMapping2Single_helperSurfaceClosed hkey1 hkey2 hvalue
  | setMapping2WordSingle hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot =>
      exact supportedStmtList_setMapping2WordSingle_helperSurfaceClosed hkey1 hkey2 hvalue
  | setStructMember2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot hmembers hmember =>
      exact supportedStmtList_setStructMember2Single_helperSurfaceClosed hkey1 hkey2 hvalue
  | rawLogLiterals htopics => exact supportedStmtList_rawLogLiterals_helperSurfaceClosed
  | letCallerLetStorageReqEqReqNeqSetStorageParamStop hOwner hne_sv_p hne_ov_p hne_ov_sv =>
      exact supportedStmtList_letCallerLetStorageReqEqReqNeqSetStorageParamStop_helperSurfaceClosed
  | letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop
      hOwner hTarget hne_sv_p hne_ov_p hne_ov_sv hne_tv_p hne_tv_sv hne_tv_ov =>
      exact supportedStmtList_letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop_helperSurfaceClosed
  | requireClause clause hrest ih =>
      cases clause
      all_goals simp [stmtListTouchesUnsupportedHelperSurface,
        Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
        stmtTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedHelperSurface,
        ih]
  | ite hcond hscope hthen helse ihThen ihElse =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hcond,
        ihThen, ihElse]
  | append hprefix hsuffix ihPrefix ihSuffix =>
      simp [stmtListTouchesUnsupportedHelperSurface_append, ihPrefix, ihSuffix]

theorem SupportedStmtList.internalHelperCallNames_nil
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hSupported : SupportedStmtList fields scope stmts) :
    stmtListInternalHelperCallNames stmts = [] := by
  induction hSupported with
  | compileCore hcore =>
      exact stmtListCompileCore_internalHelperCallNames_nil hcore
  | terminalCore hterminal =>
      cases hterminal <;> simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames]
  | setStorageSingleSlot hcore hinScope hfind =>
      simp [stmtListInternalHelperCallNames, exprCompileCore_internalHelperCallNames_nil hcore]
  | setStorageAddrSingleSlot hcore hinScope hfind =>
      simp [stmtListInternalHelperCallNames, exprCompileCore_internalHelperCallNames_nil hcore]
  | mstoreSingle hoffset hscopeOffset hvalue hscopeValue =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hoffset,
        exprCompileCore_internalHelperCallNames_nil hvalue]
  | tstoreSingle hoffset hscopeOffset hvalue hscopeValue =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hoffset,
        exprCompileCore_internalHelperCallNames_nil hvalue]
  | letStorageField hfind =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames]
  | returnMapping hkey hscope hslot =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey]
  | letMapping hkey hscope hslot =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey]
  | letMapping2 hkey1 hscope1 hkey2 hscope2 hslot =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey1,
        exprCompileCore_internalHelperCallNames_nil hkey2]
  | letMappingUint hkey hscope hslot =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey]
  | setMappingUintSingle hkey hscopeKey hvalue hscopeValue hslot =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey,
        exprCompileCore_internalHelperCallNames_nil hvalue]
  | setMappingChainSingle hkeys hscopeKeys hvalue hscopeValue hslot =>
      simp [stmtListInternalHelperCallNames,
        exprListCompileCore_internalHelperCallNames_nil hkeys,
        exprCompileCore_internalHelperCallNames_nil hvalue]
  | setMappingSingle hkey hscopeKey hvalue hscopeValue hslot =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey,
        exprCompileCore_internalHelperCallNames_nil hvalue]
  | setMappingWordSingle hkey hscopeKey hvalue hscopeValue hslot =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey,
        exprCompileCore_internalHelperCallNames_nil hvalue]
  | setMappingPackedWordSingle hkey hscopeKey hvalue hscopeValue
      hcompatValue hcompatPacked hcompatSlotWord hcompatSlotCleared hpacked hslot =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey,
        exprCompileCore_internalHelperCallNames_nil hvalue]
  | setStructMemberSingle hkey hscopeKey hvalue hscopeValue hslot hmembers hmember =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey,
        exprCompileCore_internalHelperCallNames_nil hvalue]
  | setMapping2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey1,
        exprCompileCore_internalHelperCallNames_nil hkey2,
        exprCompileCore_internalHelperCallNames_nil hvalue]
  | setMapping2WordSingle hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey1,
        exprCompileCore_internalHelperCallNames_nil hkey2,
        exprCompileCore_internalHelperCallNames_nil hvalue]
  | setStructMember2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot hmembers hmember =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey1,
        exprCompileCore_internalHelperCallNames_nil hkey2,
        exprCompileCore_internalHelperCallNames_nil hvalue]
  | rawLogLiterals htopics =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames]
  | letCallerLetStorageReqEqReqNeqSetStorageParamStop hOwner hne_sv_p hne_ov_p hne_ov_sv =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames]
  | letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop
      hOwner hTarget hne_sv_p hne_ov_p hne_ov_sv hne_tv_p hne_tv_sv hne_tv_ov =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames]
  | requireClause clause hrest ih =>
      cases clause <;> simp [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt, stmtListInternalHelperCallNames, stmtInternalHelperCallNames, ih]
  | ite hcond hscope hthen helse ihThen ihElse =>
      simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hcond,
        ihThen, ihElse]
  | append hprefix hsuffix ihPrefix ihSuffix =>
      simp [stmtListInternalHelperCallNames, ihPrefix, ihSuffix]

theorem SupportedBodyInterface.helperCallNames_nil
    {spec : CompilationModel} {fn : FunctionSpec}
    (hBody : SupportedBodyInterface spec fn) :
    helperCallNames fn = [] := by
  simp [helperCallNames, hBody.stmtList.internalHelperCallNames_nil]

private def exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux :
    (expr : Expr) →
    exprTouchesUnsupportedHelperSurface expr = false →
    exprTouchesInternalHelperSurface expr = false
  | .literal _, _ | .param _, _ | .storage _, _ | .storageAddr _, _
  | .constructorArg _, _ | .caller, _ | .contractAddress, _ | .chainid, _
  | .msgValue, _ | .blockTimestamp, _ | .blockNumber, _ | .localVar _, _
  | .blobbasefee, _ | .mload _, _ | .tload _, _ | .calldatasize, _
  | .calldataload _, _ | .returndataSize, _ | .extcodesize _, _
  | .returndataOptionalBoolAt _, _ | .arrayLength _, _
  | .storageArrayLength _, _ | .externalCall _ _, _
  | .call _ _ _ _ _ _ _, _ | .staticcall _ _ _ _ _ _, _
  | .delegatecall _ _ _ _ _ _, _ | .internalCall _ _, _
  | .dynamicBytesEq _ _, _ => by
      simp_all [exprTouchesUnsupportedHelperSurface, exprTouchesInternalHelperSurface]
  | .add a b, hsurface | .sub a b, hsurface | .mul a b, hsurface
  | .div a b, hsurface | .sdiv a b, hsurface | .mod a b, hsurface
  | .smod a b, hsurface | .bitAnd a b, hsurface | .bitOr a b, hsurface
  | .bitXor a b, hsurface | .eq a b, hsurface | .ge a b, hsurface
  | .gt a b, hsurface | .sgt a b, hsurface | .lt a b, hsurface
  | .slt a b, hsurface | .le a b, hsurface
  | .logicalAnd a b, hsurface | .logicalOr a b, hsurface
  | .min a b, hsurface | .max a b, hsurface
  | .wMulDown a b, hsurface | .wDivUp a b, hsurface
  | .keccak256 a b, hsurface => by
      simp [exprTouchesUnsupportedHelperSurface, exprTouchesInternalHelperSurface,
        Bool.or_eq_false_iff] at hsurface ⊢
      exact ⟨exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux a hsurface.1,
             exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux b hsurface.2⟩
  | .logicalNot e, hsurface | .bitNot e, hsurface => by
      simp [exprTouchesUnsupportedHelperSurface, exprTouchesInternalHelperSurface] at hsurface ⊢
      exact exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux e hsurface
  | .mapping _ e, hsurface | .mappingUint _ e, hsurface
  | .arrayElement _ e, hsurface | .storageArrayElement _ e, hsurface => by
      simp [exprTouchesUnsupportedHelperSurface, exprTouchesInternalHelperSurface] at hsurface ⊢
      exact exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux e hsurface
  | .mappingWord _ e _, hsurface | .mappingPackedWord _ e _ _, hsurface
  | .structMember _ e _, hsurface => by
      simp [exprTouchesUnsupportedHelperSurface, exprTouchesInternalHelperSurface] at hsurface ⊢
      exact exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux e hsurface
  | .shl a b, hsurface | .shr a b, hsurface | .sar a b, hsurface
  | .signextend a b, hsurface => by
      simp [exprTouchesUnsupportedHelperSurface, exprTouchesInternalHelperSurface,
        Bool.or_eq_false_iff] at hsurface ⊢
      exact ⟨exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux a hsurface.1,
             exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux b hsurface.2⟩
  | .mapping2 _ a b, hsurface | .mapping2Word _ a b _, hsurface
  | .structMember2 _ a b _, hsurface => by
      simp [exprTouchesUnsupportedHelperSurface, exprTouchesInternalHelperSurface,
        Bool.or_eq_false_iff] at hsurface ⊢
      exact ⟨exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux a hsurface.1,
             exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux b hsurface.2⟩
  | .ite c t e, hsurface => by
      simp [exprTouchesUnsupportedHelperSurface, exprTouchesInternalHelperSurface,
        Bool.or_eq_false_iff] at hsurface ⊢
      exact ⟨exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux c hsurface.1,
             exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux t hsurface.2.1,
             exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux e hsurface.2.2⟩
  | .mulDivDown a b c, hsurface | .mulDivUp a b c, hsurface => by
      simp [exprTouchesUnsupportedHelperSurface, exprTouchesInternalHelperSurface,
        Bool.or_eq_false_iff] at hsurface ⊢
      exact ⟨exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux a hsurface.1,
             exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux b hsurface.2.1,
             exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux c hsurface.2.2⟩
  | .mappingChain _ keys, hsurface => by
      simp [exprTouchesUnsupportedHelperSurface, exprTouchesInternalHelperSurface,
        exprListTouchesInternalHelperSurface] at hsurface ⊢
  termination_by expr => sizeOf expr
  decreasing_by all_goals simp_wf; omega

theorem exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {expr : Expr}
    (hsurface : exprTouchesUnsupportedHelperSurface expr = false) :
    exprTouchesInternalHelperSurface expr = false :=
  exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed_aux expr hsurface

theorem stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    stmtTouchesInternalHelperSurface stmt = false := by
  cases stmt <;>
    simp [stmtTouchesUnsupportedHelperSurface, stmtTouchesInternalHelperSurface,
      exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed] at *

theorem stmtTouchesInternalHelperSurface_eq_split
    (stmt : Stmt) :
    stmtTouchesInternalHelperSurface stmt =
      (stmtTouchesDirectInternalHelperSurface stmt ||
        stmtTouchesExprInternalHelperSurface stmt ||
        stmtTouchesStructuralInternalHelperSurface stmt) := by
  cases stmt <;>
    simp [stmtTouchesInternalHelperSurface,
      stmtTouchesDirectInternalHelperSurface,
      stmtTouchesExprInternalHelperSurface,
      stmtTouchesStructuralInternalHelperSurface]

theorem stmtTouchesDirectInternalHelperSurface_eq_split
    (stmt : Stmt) :
    stmtTouchesDirectInternalHelperSurface stmt =
      (stmtTouchesDirectInternalHelperCallSurface stmt ||
        stmtTouchesDirectInternalHelperAssignSurface stmt) := by
  cases stmt <;>
    simp [stmtTouchesDirectInternalHelperSurface,
      stmtTouchesDirectInternalHelperCallSurface,
      stmtTouchesDirectInternalHelperAssignSurface]

theorem stmtTouchesDirectInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    stmtTouchesDirectInternalHelperSurface stmt = false := by
  have hinternal := stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface
  rw [stmtTouchesInternalHelperSurface_eq_split] at hinternal
  cases hdirect : stmtTouchesDirectInternalHelperSurface stmt <;>
    simp [hdirect] at hinternal ⊢

theorem stmtTouchesDirectInternalHelperCallSurface_eq_false_of_helperSurfaceClosed
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    stmtTouchesDirectInternalHelperCallSurface stmt = false := by
  have hdirect := stmtTouchesDirectInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface
  rw [stmtTouchesDirectInternalHelperSurface_eq_split] at hdirect
  cases hcall : stmtTouchesDirectInternalHelperCallSurface stmt <;>
    simp [hcall] at hdirect ⊢

theorem stmtTouchesDirectInternalHelperAssignSurface_eq_false_of_helperSurfaceClosed
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    stmtTouchesDirectInternalHelperAssignSurface stmt = false := by
  have hdirect := stmtTouchesDirectInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface
  rw [stmtTouchesDirectInternalHelperSurface_eq_split] at hdirect
  cases hcall : stmtTouchesDirectInternalHelperCallSurface stmt <;>
    cases hassign : stmtTouchesDirectInternalHelperAssignSurface stmt <;>
      simp [hcall, hassign] at hdirect ⊢

theorem stmtTouchesExprInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    stmtTouchesExprInternalHelperSurface stmt = false := by
  have hinternal := stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface
  rw [stmtTouchesInternalHelperSurface_eq_split] at hinternal
  cases hdirect : stmtTouchesDirectInternalHelperSurface stmt <;>
    cases hexpr : stmtTouchesExprInternalHelperSurface stmt <;>
      simp [hdirect, hexpr] at hinternal ⊢

theorem stmtTouchesStructuralInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    stmtTouchesStructuralInternalHelperSurface stmt = false := by
  have hinternal := stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface
  rw [stmtTouchesInternalHelperSurface_eq_split] at hinternal
  cases hdirect : stmtTouchesDirectInternalHelperSurface stmt <;>
    cases hexpr : stmtTouchesExprInternalHelperSurface stmt <;>
      cases hstruct : stmtTouchesStructuralInternalHelperSurface stmt <;>
        simp [hdirect, hexpr, hstruct] at hinternal ⊢

theorem stmtListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesInternalHelperSurface stmts = false := by
  induction stmts with
  | nil =>
      simp [stmtListTouchesUnsupportedHelperSurface, stmtListTouchesInternalHelperSurface]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedHelperSurface, stmtListTouchesInternalHelperSurface,
        stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed, ih] at hsurface ⊢

theorem stmtListTouchesDirectInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesDirectInternalHelperSurface stmts = false := by
  induction stmts with
  | nil =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtListTouchesDirectInternalHelperSurface]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtListTouchesDirectInternalHelperSurface,
        stmtTouchesDirectInternalHelperSurface_eq_false_of_helperSurfaceClosed, ih] at hsurface ⊢

theorem stmtListTouchesDirectInternalHelperCallSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesDirectInternalHelperCallSurface stmts = false := by
  induction stmts with
  | nil =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtListTouchesDirectInternalHelperCallSurface]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtListTouchesDirectInternalHelperCallSurface,
        stmtTouchesDirectInternalHelperCallSurface_eq_false_of_helperSurfaceClosed, ih] at hsurface ⊢

theorem stmtListTouchesDirectInternalHelperAssignSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesDirectInternalHelperAssignSurface stmts = false := by
  induction stmts with
  | nil =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtListTouchesDirectInternalHelperAssignSurface]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtListTouchesDirectInternalHelperAssignSurface,
        stmtTouchesDirectInternalHelperAssignSurface_eq_false_of_helperSurfaceClosed, ih] at hsurface ⊢

theorem stmtListTouchesExprInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesExprInternalHelperSurface stmts = false := by
  induction stmts with
  | nil =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtListTouchesExprInternalHelperSurface]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtListTouchesExprInternalHelperSurface,
        stmtTouchesExprInternalHelperSurface_eq_false_of_helperSurfaceClosed, ih] at hsurface ⊢

theorem stmtListTouchesStructuralInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesStructuralInternalHelperSurface stmts = false := by
  induction stmts with
  | nil =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtListTouchesStructuralInternalHelperSurface]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtListTouchesStructuralInternalHelperSurface,
        stmtTouchesStructuralInternalHelperSurface_eq_false_of_helperSurfaceClosed, ih] at hsurface ⊢

theorem SupportedStmtList.internalHelperSurfaceClosed
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hSupported : SupportedStmtList fields scope stmts) :
    stmtListTouchesInternalHelperSurface stmts = false := by
  exact stmtListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed
    hSupported.helperSurfaceClosed

theorem SupportedBodyInterface.helperSurfaceClosed
    {spec : CompilationModel} {fn : FunctionSpec}
    (hBody : SupportedBodyInterface spec fn) :
    stmtListTouchesUnsupportedHelperSurface fn.body = false := by
  exact hBody.stmtList.helperSurfaceClosed

theorem SupportedBodyInterfaceExceptMappingWrites.helperSurfaceClosed
    {spec : CompilationModel} {fn : FunctionSpec}
    (hBody : SupportedBodyInterfaceExceptMappingWrites spec fn) :
    stmtListTouchesUnsupportedHelperSurface fn.body = false := by
  exact hBody.stmtList.helperSurfaceClosed

def SupportedBodyHelperInterface.summaryOfCall
    {spec : CompilationModel} {fn : FunctionSpec}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    {calleeName : String}
    (hmem : calleeName ∈ helperCallNames fn) :
    SupportedInternalHelperWitness spec calleeName :=
  hHelpers.summaryOf calleeName hmem

def SupportedBodyHelperInterface.summaryContractOfCall
    {spec : CompilationModel} {fn : FunctionSpec}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    {calleeName : String}
    (hmem : calleeName ∈ helperCallNames fn) :
    InternalHelperSummaryContract :=
  (hHelpers.summaryOfCall hmem).summary.contract

theorem SupportedBodyHelperInterface.calleeRank_lt
    {spec : CompilationModel} {fn : FunctionSpec}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    {calleeName : String}
    (hmem : calleeName ∈ helperCallNames fn) :
    (hHelpers.summaryOfCall hmem).summary.helperRank < hHelpers.helperRank :=
  hHelpers.calleeRanksDecrease calleeName hmem

theorem SupportedBodyHelperInterface.exprSummaryPreservesWorld
    {spec : CompilationModel} {fn : FunctionSpec}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    {calleeName : String}
    (hmem : calleeName ∈ exprHelperCallNames fn) :
    let hcall : calleeName ∈ helperCallNames fn :=
      exprHelperCallNames_subset_helperCallNames hmem
    InternalHelperSummaryPreservesWorldOnSuccess
      (hHelpers.summaryContractOfCall hcall) :=
  hHelpers.exprCallsPreserveWorld calleeName hmem

def SupportedRuntimeHelperTableInterface.compiledOfCall
    {spec : CompilationModel}
    {runtimeContract : IRContract}
    {fn : FunctionSpec}
    (hRuntime : SupportedRuntimeHelperTableInterface spec runtimeContract)
    (hHelpers : SupportedBodyHelperInterface spec fn)
    {calleeName : String}
    (hmem : calleeName ∈ helperCallNames fn) :
    SupportedCompiledInternalHelperWitness spec runtimeContract calleeName :=
  hRuntime.compiledOfWitness calleeName (hHelpers.summaryOfCall hmem)

theorem stmtListTouchesUnsupportedContractSurface_eq_featureOr
    (stmts : List Stmt) :
    stmtListTouchesUnsupportedContractSurface stmts =
      (stmtListTouchesUnsupportedCoreSurface stmts ||
        stmtListTouchesUnsupportedStateSurface stmts ||
        stmtListTouchesUnsupportedCallSurface stmts ||
        stmtListTouchesUnsupportedEffectSurface stmts) := by
  induction stmts with
  | nil =>
      simp [stmtListTouchesUnsupportedContractSurface, stmtListTouchesUnsupportedCoreSurface,
        stmtListTouchesUnsupportedStateSurface, stmtListTouchesUnsupportedCallSurface,
        stmtListTouchesUnsupportedEffectSurface]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedContractSurface, stmtTouchesUnsupportedContractSurface,
        stmtListTouchesUnsupportedCoreSurface, stmtListTouchesUnsupportedStateSurface,
        stmtListTouchesUnsupportedCallSurface, stmtListTouchesUnsupportedEffectSurface,
        ih, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

theorem stmtListTouchesUnsupportedCallSurface_eq_featureOr
    (stmts : List Stmt) :
    stmtListTouchesUnsupportedCallSurface stmts =
      (stmtListTouchesUnsupportedHelperSurface stmts ||
        stmtListTouchesUnsupportedForeignSurface stmts ||
        stmtListTouchesUnsupportedLowLevelSurface stmts) := by
  induction stmts with
  | nil =>
      simp [stmtListTouchesUnsupportedCallSurface, stmtListTouchesUnsupportedHelperSurface,
        stmtListTouchesUnsupportedForeignSurface, stmtListTouchesUnsupportedLowLevelSurface]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedCallSurface, stmtTouchesUnsupportedCallSurface,
        stmtListTouchesUnsupportedHelperSurface, stmtTouchesUnsupportedHelperSurface,
        stmtListTouchesUnsupportedForeignSurface, stmtTouchesUnsupportedForeignSurface,
        stmtListTouchesUnsupportedLowLevelSurface, stmtTouchesUnsupportedLowLevelSurface,
        ih, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed
    (expr : Expr)
    (hcore : exprTouchesUnsupportedCoreSurface expr = false)
    (hstate : exprTouchesUnsupportedStateSurface expr = false)
    (hcalls : exprTouchesUnsupportedCallSurface expr = false) :
    exprTouchesUnsupportedContractSurface expr = false := by
  induction expr with
  | literal value
  | param name
  | localVar name
  | caller
  | contractAddress
  | chainid
  | msgValue
  | blockTimestamp
  | blockNumber =>
      simp [exprTouchesUnsupportedContractSurface]
  | storage field
  | storageAddr field
  | constructorArg idx
  | blobbasefee
  | calldatasize
  | returndataSize
  | arrayLength name
  | storageArrayLength field
  | returndataOptionalBoolAt outOffset
  | mload offset
  | tload offset
  | calldataload offset
  | extcodesize addr
  | dynamicBytesEq lhs rhs =>
      cases hcore
  | add lhs rhs ihL ihR
  | sub lhs rhs ihL ihR
  | mul lhs rhs ihL ihR
  | div lhs rhs ihL ihR
  | mod lhs rhs ihL ihR
  | eq lhs rhs ihL ihR
  | ge lhs rhs ihL ihR
  | gt lhs rhs ihL ihR
  | lt lhs rhs ihL ihR
  | le lhs rhs ihL ihR
  | logicalAnd lhs rhs ihL ihR
  | logicalOr lhs rhs ihL ihR =>
      have hcoreL : exprTouchesUnsupportedCoreSurface lhs = false := by
        simpa [exprTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).1
      have hcoreR : exprTouchesUnsupportedCoreSurface rhs = false := by
        simpa [exprTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).2
      have hstateL : exprTouchesUnsupportedStateSurface lhs = false := by
        simpa [exprTouchesUnsupportedStateSurface] using (Bool.or_eq_false_iff.mp hstate).1
      have hstateR : exprTouchesUnsupportedStateSurface rhs = false := by
        simpa [exprTouchesUnsupportedStateSurface] using (Bool.or_eq_false_iff.mp hstate).2
      have hcallsL : exprTouchesUnsupportedCallSurface lhs = false := by
        simpa [exprTouchesUnsupportedCallSurface] using (Bool.or_eq_false_iff.mp hcalls).1
      have hcallsR : exprTouchesUnsupportedCallSurface rhs = false := by
        simpa [exprTouchesUnsupportedCallSurface] using (Bool.or_eq_false_iff.mp hcalls).2
      have hleft : exprTouchesUnsupportedContractSurface lhs = false :=
        ihL hcoreL hstateL hcallsL
      have hright : exprTouchesUnsupportedContractSurface rhs = false :=
        ihR hcoreR hstateR hcallsR
      simp [exprTouchesUnsupportedContractSurface, hleft, hright]
  | sdiv lhs rhs ihL ihR
  | smod lhs rhs ihL ihR
  | bitAnd lhs rhs ihL ihR
  | bitOr lhs rhs ihL ihR
  | bitXor lhs rhs ihL ihR
  | sgt lhs rhs ihL ihR
  | slt lhs rhs ihL ihR
  | min lhs rhs ihL ihR
  | max lhs rhs ihL ihR
  | wMulDown lhs rhs ihL ihR
  | wDivUp lhs rhs ihL ihR =>
      cases hcore
  | bitNot expr ih =>
      cases hcore
  | logicalNot expr ih =>
      have hstate' : exprTouchesUnsupportedStateSurface expr = false := by
        simpa [exprTouchesUnsupportedStateSurface] using hstate
      have hcalls' : exprTouchesUnsupportedCallSurface expr = false := by
        simpa [exprTouchesUnsupportedCallSurface] using hcalls
      have hexpr : exprTouchesUnsupportedContractSurface expr = false :=
        ih (by simpa [exprTouchesUnsupportedCoreSurface] using hcore) hstate' hcalls'
      simp [exprTouchesUnsupportedContractSurface, hexpr]
  | ite cond thenVal elseVal ihCond ihThen ihElse =>
      have hstateCond : exprTouchesUnsupportedStateSurface cond = false := by
        simpa [exprTouchesUnsupportedStateSurface, Bool.or_eq_false_iff] using (Bool.or_eq_false_iff.mp hstate).1
      have hstateRest : exprTouchesUnsupportedStateSurface thenVal || exprTouchesUnsupportedStateSurface elseVal = false := by
        simpa [exprTouchesUnsupportedStateSurface, Bool.or_assoc] using (Bool.or_eq_false_iff.mp hstate).2
      have hstateThen : exprTouchesUnsupportedStateSurface thenVal = false := (Bool.or_eq_false_iff.mp hstateRest).1
      have hstateElse : exprTouchesUnsupportedStateSurface elseVal = false := (Bool.or_eq_false_iff.mp hstateRest).2
      have hcallsCond : exprTouchesUnsupportedCallSurface cond = false := by
        simpa [exprTouchesUnsupportedCallSurface, Bool.or_eq_false_iff] using (Bool.or_eq_false_iff.mp hcalls).1
      have hcallsRest : exprTouchesUnsupportedCallSurface thenVal || exprTouchesUnsupportedCallSurface elseVal = false := by
        simpa [exprTouchesUnsupportedCallSurface, Bool.or_assoc] using (Bool.or_eq_false_iff.mp hcalls).2
      have hcallsThen : exprTouchesUnsupportedCallSurface thenVal = false := (Bool.or_eq_false_iff.mp hcallsRest).1
      have hcallsElse : exprTouchesUnsupportedCallSurface elseVal = false := (Bool.or_eq_false_iff.mp hcallsRest).2
      have hcond : exprTouchesUnsupportedContractSurface cond = false :=
        ihCond (by simpa [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff] using (Bool.or_eq_false_iff.mp hcore).1) hstateCond hcallsCond
      have hthen : exprTouchesUnsupportedContractSurface thenVal = false :=
        ihThen (by
          have hcoreRest : exprTouchesUnsupportedCoreSurface thenVal || exprTouchesUnsupportedCoreSurface elseVal = false := by
            simpa [exprTouchesUnsupportedCoreSurface, Bool.or_assoc] using (Bool.or_eq_false_iff.mp hcore).2
          exact (Bool.or_eq_false_iff.mp hcoreRest).1) hstateThen hcallsThen
      have helse : exprTouchesUnsupportedContractSurface elseVal = false :=
        ihElse (by
          have hcoreRest : exprTouchesUnsupportedCoreSurface thenVal || exprTouchesUnsupportedCoreSurface elseVal = false := by
            simpa [exprTouchesUnsupportedCoreSurface, Bool.or_assoc] using (Bool.or_eq_false_iff.mp hcore).2
          exact (Bool.or_eq_false_iff.mp hcoreRest).2) hstateElse hcallsElse
      simp [exprTouchesUnsupportedContractSurface, hcond, hthen, helse]
  | shl lhs rhs ihL ihR
  | shr lhs rhs ihL ihR
  | sar lhs rhs ihL ihR
  | signextend lhs rhs ihL ihR
  | mulDivDown lhs rhs denom ihL ihR ihD
  | mulDivUp lhs rhs denom ihL ihR ihD
  | mapping field key ih
  | mappingWord field key offset ih
  | mappingPackedWord field key offset packed ih
  | mappingUint field key ih
  | mappingChain field keys ih
  | structMember field key memberName ih
  | arrayElement name index ih
  | storageArrayElement field index ih
  | call gas target value inOffset inSize outOffset outSize ih1 ih2 ih3 ih4 ih5 ih6 ih7
  | staticcall gas target inOffset inSize outOffset outSize ih1 ih2 ih3 ih4 ih5 ih6
  | delegatecall gas target inOffset inSize outOffset outSize ih1 ih2 ih3 ih4 ih5 ih6
  | externalCall name args ih
  | internalCall name args ih
  | mapping2 field key1 key2 ih1 ih2
  | mapping2Word field key1 key2 offset ih1 ih2
  | structMember2 field key1 key2 memberName ih1 ih2 =>
      cases hcore

private theorem stmtTouchesUnsupportedContractSurface_eq_false_of_featureClosed
    (stmt : Stmt)
    (hcore : stmtTouchesUnsupportedCoreSurface stmt = false)
    (hstate : stmtTouchesUnsupportedStateSurface stmt = false)
    (hcalls : stmtTouchesUnsupportedCallSurface stmt = false)
    (heffects : stmtTouchesUnsupportedEffectSurface stmt = false) :
    stmtTouchesUnsupportedContractSurface stmt = false := by
  cases stmt <;> simp [stmtTouchesUnsupportedContractSurface] at *
  case letVar name value =>
    exact exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed value hcore hstate hcalls
  case assignVar name value =>
    exact exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed value hcore hstate hcalls
  case setStorage fieldName value =>
    exact exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed value hcore hstate hcalls
  case require cond message =>
    exact exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed cond hcore hstate hcalls
  case «return» value =>
    exact exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed value hcore hstate hcalls
  all_goals
    cases hcore

private theorem stmtTouchesUnsupportedContractSurfaceExceptMappingWrites_eq_false_of_featureClosed
    (stmt : Stmt)
    (hcore : stmtTouchesUnsupportedCoreSurface stmt = false)
    (hstate : stmtTouchesUnsupportedStateSurfaceExceptMappingWrites stmt = false)
    (hcalls : stmtTouchesUnsupportedCallSurface stmt = false)
    (heffects : stmtTouchesUnsupportedEffectSurface stmt = false) :
    stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt = false := by
  cases stmt <;> simp [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites] at *
  case letVar name value =>
    exact exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed value hcore
      (by simpa [stmtTouchesUnsupportedStateSurfaceExceptMappingWrites] using hstate)
      hcalls
  case assignVar name value =>
    exact exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed value hcore
      (by simpa [stmtTouchesUnsupportedStateSurfaceExceptMappingWrites] using hstate)
      hcalls
  case setStorage fieldName value =>
    exact exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed value hcore
      (by simpa [stmtTouchesUnsupportedStateSurfaceExceptMappingWrites] using hstate)
      hcalls
  case require cond message =>
    exact exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed cond hcore
      (by simpa [stmtTouchesUnsupportedStateSurfaceExceptMappingWrites] using hstate)
      hcalls
  case «return» value =>
    exact exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed value hcore
      (by simpa [stmtTouchesUnsupportedStateSurfaceExceptMappingWrites] using hstate)
      hcalls
  all_goals
    first | rfl | cases hcore

private theorem stmtListFeatureClosed_cons_inv
    (stmt : Stmt)
    (rest : List Stmt)
    (hcore : stmtListTouchesUnsupportedCoreSurface (stmt :: rest) = false)
    (hstate : stmtListTouchesUnsupportedStateSurface (stmt :: rest) = false)
    (hcalls : stmtListTouchesUnsupportedCallSurface (stmt :: rest) = false)
    (heffects : stmtListTouchesUnsupportedEffectSurface (stmt :: rest) = false) :
    stmtTouchesUnsupportedCoreSurface stmt = false ∧
    stmtListTouchesUnsupportedCoreSurface rest = false ∧
    stmtTouchesUnsupportedStateSurface stmt = false ∧
    stmtListTouchesUnsupportedStateSurface rest = false ∧
    stmtTouchesUnsupportedCallSurface stmt = false ∧
    stmtListTouchesUnsupportedCallSurface rest = false ∧
    stmtTouchesUnsupportedEffectSurface stmt = false ∧
    stmtListTouchesUnsupportedEffectSurface rest = false := by
  constructor
  · simpa [stmtListTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).1
  constructor
  · simpa [stmtListTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).2
  constructor
  · simpa [stmtListTouchesUnsupportedStateSurface] using (Bool.or_eq_false_iff.mp hstate).1
  constructor
  · simpa [stmtListTouchesUnsupportedStateSurface] using (Bool.or_eq_false_iff.mp hstate).2
  constructor
  · simpa [stmtListTouchesUnsupportedCallSurface] using (Bool.or_eq_false_iff.mp hcalls).1
  constructor
  · simpa [stmtListTouchesUnsupportedCallSurface] using (Bool.or_eq_false_iff.mp hcalls).2
  constructor
  · simpa [stmtListTouchesUnsupportedEffectSurface] using (Bool.or_eq_false_iff.mp heffects).1
  · simpa [stmtListTouchesUnsupportedEffectSurface] using (Bool.or_eq_false_iff.mp heffects).2

private theorem stmtListFeatureClosedExceptMappingWrites_cons_inv
    (stmt : Stmt)
    (rest : List Stmt)
    (hcore : stmtListTouchesUnsupportedCoreSurface (stmt :: rest) = false)
    (hstate : stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites (stmt :: rest) = false)
    (hcalls : stmtListTouchesUnsupportedCallSurface (stmt :: rest) = false)
    (heffects : stmtListTouchesUnsupportedEffectSurface (stmt :: rest) = false) :
    stmtTouchesUnsupportedCoreSurface stmt = false ∧
    stmtListTouchesUnsupportedCoreSurface rest = false ∧
    stmtTouchesUnsupportedStateSurfaceExceptMappingWrites stmt = false ∧
    stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites rest = false ∧
    stmtTouchesUnsupportedCallSurface stmt = false ∧
    stmtListTouchesUnsupportedCallSurface rest = false ∧
    stmtTouchesUnsupportedEffectSurface stmt = false ∧
    stmtListTouchesUnsupportedEffectSurface rest = false := by
  constructor
  · simpa [stmtListTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).1
  constructor
  · simpa [stmtListTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).2
  constructor
  · simpa [stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites] using
      (Bool.or_eq_false_iff.mp hstate).1
  constructor
  · simpa [stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites] using
      (Bool.or_eq_false_iff.mp hstate).2
  constructor
  · simpa [stmtListTouchesUnsupportedCallSurface] using (Bool.or_eq_false_iff.mp hcalls).1
  constructor
  · simpa [stmtListTouchesUnsupportedCallSurface] using (Bool.or_eq_false_iff.mp hcalls).2
  constructor
  · simpa [stmtListTouchesUnsupportedEffectSurface] using (Bool.or_eq_false_iff.mp heffects).1
  · simpa [stmtListTouchesUnsupportedEffectSurface] using (Bool.or_eq_false_iff.mp heffects).2

theorem stmtListTouchesUnsupportedContractSurface_eq_false_of_featureClosed
    (stmts : List Stmt)
    (hcore : stmtListTouchesUnsupportedCoreSurface stmts = false)
    (hstate : stmtListTouchesUnsupportedStateSurface stmts = false)
    (hcalls : stmtListTouchesUnsupportedCallSurface stmts = false)
    (heffects : stmtListTouchesUnsupportedEffectSurface stmts = false) :
    stmtListTouchesUnsupportedContractSurface stmts = false := by
  induction stmts with
  | nil =>
      simp [stmtListTouchesUnsupportedContractSurface]
  | cons stmt rest ih =>
      rcases stmtListFeatureClosed_cons_inv stmt rest hcore hstate hcalls heffects with
        ⟨hcoreStmt, hcoreRest, hstateStmt, hstateRest,
          hcallsStmt, hcallsRest, heffectsStmt, heffectsRest⟩
      have hstmt :
          stmtTouchesUnsupportedContractSurface stmt = false :=
        stmtTouchesUnsupportedContractSurface_eq_false_of_featureClosed stmt
          hcoreStmt hstateStmt hcallsStmt heffectsStmt
      have hrest :
          stmtListTouchesUnsupportedContractSurface rest = false :=
        ih hcoreRest hstateRest hcallsRest heffectsRest
      simp [stmtListTouchesUnsupportedContractSurface, hstmt, hrest]

theorem stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_eq_false_of_featureClosed
    (stmts : List Stmt)
    (hcore : stmtListTouchesUnsupportedCoreSurface stmts = false)
    (hstate : stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites stmts = false)
    (hcalls : stmtListTouchesUnsupportedCallSurface stmts = false)
    (heffects : stmtListTouchesUnsupportedEffectSurface stmts = false) :
    stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false := by
  induction stmts with
  | nil =>
      simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites]
  | cons stmt rest ih =>
      rcases stmtListFeatureClosedExceptMappingWrites_cons_inv stmt rest hcore hstate hcalls heffects with
        ⟨hcoreStmt, hcoreRest, hstateStmt, hstateRest,
          hcallsStmt, hcallsRest, heffectsStmt, heffectsRest⟩
      have hstmt :
          stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt = false :=
        stmtTouchesUnsupportedContractSurfaceExceptMappingWrites_eq_false_of_featureClosed stmt
          hcoreStmt hstateStmt hcallsStmt heffectsStmt
      have hrest :
          stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites rest = false :=
        ih hcoreRest hstateRest hcallsRest heffectsRest
      simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites, hstmt, hrest]

private theorem
    exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed_mappingChain
    {fieldName : String}
    {keys : List Expr}
    (ih :
      ∀ key ∈ keys,
        exprTouchesUnsupportedContractSurface key = false →
          exprTouchesUnsupportedHelperSurface key = false)
    (hsurface : exprTouchesUnsupportedContractSurface (.mappingChain fieldName keys) = false) :
    exprTouchesUnsupportedHelperSurface (.mappingChain fieldName keys) = false := by
  induction keys with
  | nil =>
      simp [exprTouchesUnsupportedContractSurface,
        exprTouchesUnsupportedHelperSurface] at *
  | cons key rest ihKeys =>
      simp [exprTouchesUnsupportedContractSurface,
        exprTouchesUnsupportedHelperSurface] at hsurface ⊢
      constructor
      · exact ih key (by simp) hsurface.1
      · exact ihKeys (fun next hnext hnextSurface => ih next (by simp [hnext]) hnextSurface) hsurface.2

theorem exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed
    {expr : Expr}
    (hsurface : exprTouchesUnsupportedContractSurface expr = false) :
    exprTouchesUnsupportedHelperSurface expr = false := by
  induction expr with
  | literal | param | caller | contractAddress | chainid | msgValue
    | blockTimestamp | blockNumber | localVar | storage | storageAddr
    | constructorArg | blobbasefee | mload | tload | calldatasize
    | calldataload | returndataSize | extcodesize | returndataOptionalBoolAt
    | arrayLength | storageArrayLength | externalCall | call | staticcall
    | delegatecall | internalCall =>
      simp [exprTouchesUnsupportedContractSurface,
        exprTouchesUnsupportedHelperSurface] at *
  | add lhs rhs ihL ihR | sub lhs rhs ihL ihR | mul lhs rhs ihL ihR
    | div lhs rhs ihL ihR | sdiv lhs rhs ihL ihR | mod lhs rhs ihL ihR
    | smod lhs rhs ihL ihR | bitAnd lhs rhs ihL ihR | bitOr lhs rhs ihL ihR
    | bitXor lhs rhs ihL ihR | eq lhs rhs ihL ihR | ge lhs rhs ihL ihR
    | gt lhs rhs ihL ihR | sgt lhs rhs ihL ihR | lt lhs rhs ihL ihR
    | slt lhs rhs ihL ihR | le lhs rhs ihL ihR | logicalAnd lhs rhs ihL ihR
    | logicalOr lhs rhs ihL ihR | min lhs rhs ihL ihR | max lhs rhs ihL ihR
    | wMulDown lhs rhs ihL ihR | wDivUp lhs rhs ihL ihR
    | mapping2 _ lhs rhs ihL ihR | mapping2Word _ lhs rhs _ ihL ihR
    | structMember2 _ lhs rhs _ ihL ihR =>
      simp [exprTouchesUnsupportedContractSurface,
        exprTouchesUnsupportedHelperSurface, ihL, ihR, Bool.or_eq_false_iff] at *
  | logicalNot expr ih | bitNot expr ih | mapping _ expr ih | mappingUint _ expr ih
    | arrayElement _ expr ih | storageArrayElement _ expr ih
    | mappingWord _ expr _ ih | mappingPackedWord _ expr _ _ ih
    | structMember _ expr _ ih | shl expr _ ih | shr expr _ ih
    | sar expr _ ih | signextend expr _ ih =>
      simp [exprTouchesUnsupportedContractSurface, exprTouchesUnsupportedHelperSurface, ih] at *
  | ite cond thenVal elseVal ihCond ihThen ihElse =>
      simp [exprTouchesUnsupportedContractSurface,
        exprTouchesUnsupportedHelperSurface, ihCond, ihThen, ihElse,
        Bool.or_eq_false_iff] at *
  | mulDivDown a b c ihA ihB ihC | mulDivUp a b c ihA ihB ihC =>
      simp [exprTouchesUnsupportedContractSurface,
        exprTouchesUnsupportedHelperSurface, ihA, ihB, ihC,
        Bool.or_eq_false_iff] at *
  | keccak256 a b ihA ihB =>
      simp [exprTouchesUnsupportedContractSurface,
        exprTouchesUnsupportedHelperSurface, ihA, ihB, Bool.or_eq_false_iff] at *
  | mappingChain fieldName keys ih =>
      exact
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed_mappingChain
          (fieldName := fieldName)
          (keys := keys)
          (ih := fun key hkey => ih key hkey)
          hsurface

theorem stmtTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedContractSurface stmt = false) :
    stmtTouchesUnsupportedHelperSurface stmt = false := by
  cases stmt <;>
    simp [stmtTouchesUnsupportedContractSurface, stmtTouchesUnsupportedHelperSurface,
      exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed] at *

theorem stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  induction stmts with
  | nil =>
      simp [stmtListTouchesUnsupportedContractSurface,
        stmtListTouchesUnsupportedHelperSurface]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedContractSurface,
        stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed, ih] at hsurface ⊢

theorem stmtTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed_exceptMappingWrites
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt = false) :
    stmtTouchesUnsupportedHelperSurface stmt = false := by
  cases stmt <;>
    simp [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
      stmtTouchesUnsupportedContractSurface, stmtTouchesUnsupportedHelperSurface,
      exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed] at *

theorem stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed_exceptMappingWrites
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  induction stmts with
  | nil =>
      simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
        stmtListTouchesUnsupportedHelperSurface]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
        stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed_exceptMappingWrites,
        ih] at hsurface ⊢

theorem SupportedBodyCallInterface.surfaceClosed
    {spec : CompilationModel} {fn : FunctionSpec}
    (hBody : SupportedBodyInterface spec fn) :
    stmtListTouchesUnsupportedCallSurface fn.body = false := by
  rw [stmtListTouchesUnsupportedCallSurface_eq_featureOr]
  simp [hBody.helperSurfaceClosed, hBody.calls.foreign, hBody.calls.lowLevel]

theorem SupportedBodyCallInterface.surfaceClosed_exceptMappingWrites
    {spec : CompilationModel} {fn : FunctionSpec}
    (hBody : SupportedBodyInterfaceExceptMappingWrites spec fn) :
    stmtListTouchesUnsupportedCallSurface fn.body = false := by
  rw [stmtListTouchesUnsupportedCallSurface_eq_featureOr]
  simp [hBody.helperSurfaceClosed, hBody.calls.foreign, hBody.calls.lowLevel]

private theorem exprUsesArrayElement_eq_false_of_coreClosed
    {expr : Expr}
    (hcore : exprTouchesUnsupportedCoreSurface expr = false) :
    exprUsesArrayElement expr = false := by
  induction expr with
  | literal | param | constructorArg | storage | storageAddr
    | localVar | caller | contractAddress | chainid | msgValue
    | blockTimestamp | blockNumber | blobbasefee
    | calldatasize | returndataSize | arrayLength | storageArrayLength =>
      simp [exprUsesArrayElement]
  | dynamicBytesEq =>
      cases hcore
  | bitNot expr ih =>
      cases hcore
  | logicalNot expr ih =>
      simpa [exprTouchesUnsupportedCoreSurface, exprUsesArrayElement] using ih hcore
  | add lhs rhs ihL ihR | sub lhs rhs ihL ihR | mul lhs rhs ihL ihR
    | div lhs rhs ihL ihR | mod lhs rhs ihL ihR | eq lhs rhs ihL ihR
    | ge lhs rhs ihL ihR | gt lhs rhs ihL ihR | lt lhs rhs ihL ihR
    | le lhs rhs ihL ihR | logicalAnd lhs rhs ihL ihR | logicalOr lhs rhs ihL ihR =>
      have hleft : exprTouchesUnsupportedCoreSurface lhs = false := by
        simpa [exprTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).1
      have hright : exprTouchesUnsupportedCoreSurface rhs = false := by
        simpa [exprTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).2
      simp [exprUsesArrayElement, ihL hleft, ihR hright]
  | sdiv | smod | bitAnd | bitOr | bitXor | sgt | slt | min | max
    | wMulDown | wDivUp | shl | shr | sar | signextend | mulDivDown
    | mulDivUp | mapping | mappingWord | mappingPackedWord | mappingUint
    | mappingChain | structMember | arrayElement | storageArrayElement
    | call | staticcall | delegatecall | externalCall | internalCall
    | mapping2 | mapping2Word | structMember2 | mload | tload
    | calldataload | extcodesize | returndataOptionalBoolAt | keccak256
    | ite =>
      cases hcore

private theorem exprUsesStorageArrayElement_eq_false_of_coreClosed
    {expr : Expr}
    (hcore : exprTouchesUnsupportedCoreSurface expr = false) :
    exprUsesStorageArrayElement expr = false := by
  induction expr with
  | literal | param | constructorArg | storage | storageAddr
    | localVar | caller | contractAddress | chainid | msgValue
    | blockTimestamp | blockNumber | blobbasefee
    | calldatasize | returndataSize | arrayLength | storageArrayLength
    | arrayElement =>
      simp [exprUsesStorageArrayElement]
  | dynamicBytesEq =>
      cases hcore
  | bitNot expr ih =>
      cases hcore
  | logicalNot expr ih =>
      simpa [exprTouchesUnsupportedCoreSurface, exprUsesStorageArrayElement] using ih hcore
  | add lhs rhs ihL ihR | sub lhs rhs ihL ihR | mul lhs rhs ihL ihR
    | div lhs rhs ihL ihR | mod lhs rhs ihL ihR | eq lhs rhs ihL ihR
    | ge lhs rhs ihL ihR | gt lhs rhs ihL ihR | lt lhs rhs ihL ihR
    | le lhs rhs ihL ihR | logicalAnd lhs rhs ihL ihR | logicalOr lhs rhs ihL ihR =>
      have hleft : exprTouchesUnsupportedCoreSurface lhs = false := by
        simpa [exprTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).1
      have hright : exprTouchesUnsupportedCoreSurface rhs = false := by
        simpa [exprTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).2
      simp [exprUsesStorageArrayElement, ihL hleft, ihR hright]
  | sdiv | smod | bitAnd | bitOr | bitXor | sgt | slt | min | max
    | wMulDown | wDivUp | shl | shr | sar | signextend | mulDivDown
    | mulDivUp | mapping | mappingWord | mappingPackedWord | mappingUint
    | mappingChain | structMember | storageArrayElement
    | call | staticcall | delegatecall | externalCall | internalCall
    | mapping2 | mapping2Word | structMember2 | mload | tload
    | calldataload | extcodesize | returndataOptionalBoolAt | keccak256
    | ite =>
      cases hcore

private theorem exprUsesDynamicBytesEq_eq_false_of_coreClosed
    {expr : Expr}
    (hcore : exprTouchesUnsupportedCoreSurface expr = false) :
    exprUsesDynamicBytesEq expr = false := by
  induction expr with
  | literal | param | constructorArg | storage | storageAddr
    | localVar | caller | contractAddress | chainid | msgValue
    | blockTimestamp | blockNumber | blobbasefee
    | calldatasize | returndataSize | arrayLength | storageArrayLength =>
      simp [exprUsesDynamicBytesEq]
  | dynamicBytesEq =>
      cases hcore
  | bitNot expr ih =>
      cases hcore
  | logicalNot expr ih =>
      simpa [exprTouchesUnsupportedCoreSurface, exprUsesDynamicBytesEq] using ih hcore
  | add lhs rhs ihL ihR | sub lhs rhs ihL ihR | mul lhs rhs ihL ihR
    | div lhs rhs ihL ihR | mod lhs rhs ihL ihR | eq lhs rhs ihL ihR
    | ge lhs rhs ihL ihR | gt lhs rhs ihL ihR | lt lhs rhs ihL ihR
    | le lhs rhs ihL ihR | logicalAnd lhs rhs ihL ihR | logicalOr lhs rhs ihL ihR =>
      have hleft : exprTouchesUnsupportedCoreSurface lhs = false := by
        simpa [exprTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).1
      have hright : exprTouchesUnsupportedCoreSurface rhs = false := by
        simpa [exprTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).2
      simp [exprUsesDynamicBytesEq, ihL hleft, ihR hright]
  | sdiv | smod | bitAnd | bitOr | bitXor | sgt | slt | min | max
    | wMulDown | wDivUp | shl | shr | sar | signextend | mulDivDown
    | mulDivUp | mapping | mappingWord | mappingPackedWord | mappingUint
    | mappingChain | structMember | arrayElement | storageArrayElement
    | call | staticcall | delegatecall | externalCall | internalCall
    | mapping2 | mapping2Word | structMember2 | mload | tload
    | calldataload | extcodesize | returndataOptionalBoolAt | keccak256
    | ite =>
      cases hcore

private theorem stmtUsesArrayElement_eq_false_of_coreClosed
    {stmt : Stmt}
    (hcore : stmtTouchesUnsupportedCoreSurface stmt = false) :
    stmtUsesArrayElement stmt = false := by
  cases stmt <;> simp [stmtTouchesUnsupportedCoreSurface, stmtUsesArrayElement] at *
  case letVar name value | assignVar name value | setStorage field value
    | «return» value | require value message =>
      exact exprUsesArrayElement_eq_false_of_coreClosed hcore

private theorem stmtUsesStorageArrayElement_eq_false_of_coreClosed
    {stmt : Stmt}
    (hcore : stmtTouchesUnsupportedCoreSurface stmt = false) :
    stmtUsesStorageArrayElement stmt = false := by
  cases stmt <;> simp [stmtTouchesUnsupportedCoreSurface, stmtUsesStorageArrayElement] at *
  case letVar name value | assignVar name value | setStorage field value
    | «return» value | require value message =>
      exact exprUsesStorageArrayElement_eq_false_of_coreClosed hcore

private theorem stmtUsesDynamicBytesEq_eq_false_of_coreClosed
    {stmt : Stmt}
    (hcore : stmtTouchesUnsupportedCoreSurface stmt = false) :
    stmtUsesDynamicBytesEq stmt = false := by
  cases stmt <;> simp [stmtTouchesUnsupportedCoreSurface, stmtUsesDynamicBytesEq] at *
  case letVar name value | assignVar name value | setStorage field value
    | «return» value | require value message =>
      exact exprUsesDynamicBytesEq_eq_false_of_coreClosed hcore

private theorem stmtListUsesArrayElement_eq_false_of_coreClosed
    {stmts : List Stmt}
    (hcore : stmtListTouchesUnsupportedCoreSurface stmts = false) :
    stmtListUsesArrayElement stmts = false := by
  induction stmts with
  | nil =>
      rfl
  | cons stmt rest ih =>
      have hstmt : stmtTouchesUnsupportedCoreSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).1
      have hrest : stmtListTouchesUnsupportedCoreSurface rest = false := by
        simpa [stmtListTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).2
      simp [stmtListUsesArrayElement, stmtUsesArrayElement_eq_false_of_coreClosed hstmt, ih hrest]

private theorem stmtListUsesStorageArrayElement_eq_false_of_coreClosed
    {stmts : List Stmt}
    (hcore : stmtListTouchesUnsupportedCoreSurface stmts = false) :
    stmtListUsesStorageArrayElement stmts = false := by
  induction stmts with
  | nil =>
      rfl
  | cons stmt rest ih =>
      have hstmt : stmtTouchesUnsupportedCoreSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).1
      have hrest : stmtListTouchesUnsupportedCoreSurface rest = false := by
        simpa [stmtListTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).2
      simp [stmtListUsesStorageArrayElement,
        stmtUsesStorageArrayElement_eq_false_of_coreClosed hstmt, ih hrest]

private theorem stmtListUsesDynamicBytesEq_eq_false_of_coreClosed
    {stmts : List Stmt}
    (hcore : stmtListTouchesUnsupportedCoreSurface stmts = false) :
    stmtListUsesDynamicBytesEq stmts = false := by
  induction stmts with
  | nil =>
      rfl
  | cons stmt rest ih =>
      have hstmt : stmtTouchesUnsupportedCoreSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).1
      have hrest : stmtListTouchesUnsupportedCoreSurface rest = false := by
        simpa [stmtListTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).2
      simp [stmtListUsesDynamicBytesEq,
        stmtUsesDynamicBytesEq_eq_false_of_coreClosed hstmt, ih hrest]

private theorem listAny_eq_false_of_mem_eq_false
    {α : Type} (f : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = false) → xs.any f = false
  | [], _ => rfl
  | x :: xs, hmem => by
      have hx : f x = false := hmem x (by simp)
      have hxs : ∀ y ∈ xs, f y = false := by
        intro y hy
        exact hmem y (by simp [hy])
      simp [List.any_cons, hx, listAny_eq_false_of_mem_eq_false f xs hxs]

theorem SupportedSpec.noInternalFunctions
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ fn ∈ spec.functions, fn.isInternal = false := by
  intro fn hmem
  exact (hSupported.functions fn hmem).nonInternal

theorem SupportedSpecExceptMappingWrites.noInternalFunctions
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    ∀ fn ∈ spec.functions, fn.isInternal = false := by
  intro fn hmem
  exact (hSupported.functions fn hmem).nonInternal

theorem SupportedSpec.noConstructor
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    spec.constructor = none :=
  hSupported.surface.noConstructor

theorem SupportedSpec.contractUsesArrayElement_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    contractUsesArrayElement spec = false := by
  have hctor : constructorUsesArrayElement spec.constructor = false := by
    simp [SupportedSpec.noConstructor hSupported]
  have hfunctions :
      spec.functions.any functionUsesArrayElement = false := by
    apply listAny_eq_false_of_mem_eq_false
    intro fn hmem
    exact stmtListUsesArrayElement_eq_false_of_coreClosed
      ((hSupported.functions fn hmem).body.core.surfaceClosed)
  simp [contractUsesArrayElement, hctor, hfunctions]

theorem SupportedSpecExceptMappingWrites.contractUsesArrayElement_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    contractUsesArrayElement spec = false := by
  have hctor : constructorUsesArrayElement spec.constructor = false := by
    simp [hSupported.surface.noConstructor]
  have hfunctions :
      spec.functions.any functionUsesArrayElement = false := by
    apply listAny_eq_false_of_mem_eq_false
    intro fn hmem
    exact stmtListUsesArrayElement_eq_false_of_coreClosed
      ((hSupported.functions fn hmem).body.core.surfaceClosed)
  simp [contractUsesArrayElement, hctor, hfunctions]

theorem SupportedSpec.contractUsesStorageArrayElement_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    contractUsesStorageArrayElement spec = false := by
  have hctor : constructorUsesStorageArrayElement spec.constructor = false := by
    simp [SupportedSpec.noConstructor hSupported]
  have hfunctions :
      spec.functions.any functionUsesStorageArrayElement = false := by
    apply listAny_eq_false_of_mem_eq_false
    intro fn hmem
    exact stmtListUsesStorageArrayElement_eq_false_of_coreClosed
      ((hSupported.functions fn hmem).body.core.surfaceClosed)
  simp [contractUsesStorageArrayElement, hctor, hfunctions]

theorem SupportedSpecExceptMappingWrites.contractUsesStorageArrayElement_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    contractUsesStorageArrayElement spec = false := by
  have hctor : constructorUsesStorageArrayElement spec.constructor = false := by
    simp [hSupported.surface.noConstructor]
  have hfunctions :
      spec.functions.any functionUsesStorageArrayElement = false := by
    apply listAny_eq_false_of_mem_eq_false
    intro fn hmem
    exact stmtListUsesStorageArrayElement_eq_false_of_coreClosed
      ((hSupported.functions fn hmem).body.core.surfaceClosed)
  simp [contractUsesStorageArrayElement, hctor, hfunctions]

theorem SupportedSpec.contractUsesDynamicBytesEq_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    contractUsesDynamicBytesEq spec = false := by
  have hctor : (spec.constructor.map (fun ctor => ctor.body.any stmtUsesDynamicBytesEq) |>.getD false) = false := by
    simp [SupportedSpec.noConstructor hSupported]
  have hfunctions :
      spec.functions.any (fun fn => fn.body.any stmtUsesDynamicBytesEq) = false := by
    apply listAny_eq_false_of_mem_eq_false
    intro fn hmem
    exact stmtListUsesDynamicBytesEq_eq_false_of_coreClosed
      ((hSupported.functions fn hmem).body.core.surfaceClosed)
  simp [contractUsesDynamicBytesEq, hctor, hfunctions]

theorem SupportedSpecExceptMappingWrites.contractUsesDynamicBytesEq_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    contractUsesDynamicBytesEq spec = false := by
  have hctor : (spec.constructor.map (fun ctor => ctor.body.any stmtUsesDynamicBytesEq) |>.getD false) = false := by
    simp [hSupported.surface.noConstructor]
  have hfunctions :
      spec.functions.any (fun fn => fn.body.any stmtUsesDynamicBytesEq) = false := by
    apply listAny_eq_false_of_mem_eq_false
    intro fn hmem
    exact stmtListUsesDynamicBytesEq_eq_false_of_coreClosed
      ((hSupported.functions fn hmem).body.core.surfaceClosed)
  simp [contractUsesDynamicBytesEq, hctor, hfunctions]

theorem SupportedSpec.normalizedFields
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    applySlotAliasRanges spec.fields spec.slotAliasRanges = spec.fields :=
  hSupported.invariants.normalizedFields

theorem SupportedSpecExceptMappingWrites.normalizedFields
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    applySlotAliasRanges spec.fields spec.slotAliasRanges = spec.fields :=
  hSupported.invariants.normalizedFields

theorem SupportedSpec.noPackedFields
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ field ∈ spec.fields, field.packedBits = none :=
  hSupported.invariants.noPackedFields

theorem SupportedSpecExceptMappingWrites.noPackedFields
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    ∀ field ∈ spec.fields, field.packedBits = none :=
  hSupported.invariants.noPackedFields

theorem SupportedSpec.selectorCount
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    selectors.length = (selectorDispatchedFunctions spec).length :=
  hSupported.invariants.selectorCount

theorem SupportedSpecExceptMappingWrites.selectorCount
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    selectors.length = (selectorDispatchedFunctions spec).length :=
  hSupported.invariants.selectorCount

theorem SupportedSpec.selectorsDistinct
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    firstDuplicateSelector selectors = none :=
  hSupported.invariants.selectorsDistinct

theorem SupportedSpecExceptMappingWrites.selectorsDistinct
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    firstDuplicateSelector selectors = none :=
  hSupported.invariants.selectorsDistinct

theorem SupportedSpec.functionNamesNodup
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    (spec.functions.map (·.name)).Nodup :=
  hSupported.invariants.functionNamesNodup

theorem SupportedSpecExceptMappingWrites.functionNamesNodup
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    (spec.functions.map (·.name)).Nodup :=
  hSupported.invariants.functionNamesNodup

theorem SupportedSpecExceptMappingWrites.noConstructor
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    spec.constructor = none :=
  hSupported.surface.noConstructor

theorem SupportedSpec.noEvents
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    spec.events = [] :=
  hSupported.surface.noEvents

theorem SupportedSpecExceptMappingWrites.noEvents
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    spec.events = [] :=
  hSupported.surface.noEvents

theorem SupportedSpec.noErrors
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    spec.errors = [] :=
  hSupported.surface.noErrors

theorem SupportedSpecExceptMappingWrites.noErrors
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    spec.errors = [] :=
  hSupported.surface.noErrors

theorem SupportedSpec.noExternals
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    spec.externals = [] :=
  hSupported.surface.noExternals

theorem SupportedSpecExceptMappingWrites.noExternals
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    spec.externals = [] :=
  hSupported.surface.noExternals

theorem SupportedSpec.noFallback
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ fn ∈ spec.functions, fn.name != "fallback" :=
  hSupported.surface.noFallback

theorem SupportedSpecExceptMappingWrites.noFallback
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    ∀ fn ∈ spec.functions, fn.name != "fallback" :=
  hSupported.surface.noFallback

theorem SupportedSpec.noReceive
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ fn ∈ spec.functions, fn.name != "receive" :=
  hSupported.surface.noReceive

theorem SupportedSpecExceptMappingWrites.noReceive
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    ∀ fn ∈ spec.functions, fn.name != "receive" :=
  hSupported.surface.noReceive

def SupportedSpec.supportedFunctionOfSelectorDispatched
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    SupportedFunction spec fn := by
  have hfiltered : fn ∈ spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name) := by
    simpa [selectorDispatchedFunctions] using hfn
  have hmem : fn ∈ spec.functions := (List.mem_filter.mp hfiltered).1
  exact hSupported.functions fn hmem

def SupportedSpecExceptMappingWrites.supportedFunctionOfSelectorDispatched
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    SupportedFunctionExceptMappingWrites spec fn := by
  have hfiltered : fn ∈ spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name) := by
    simpa [selectorDispatchedFunctions] using hfn
  have hmem : fn ∈ spec.functions := (List.mem_filter.mp hfiltered).1
  exact hSupported.functions fn hmem

def SupportedSpec.helperFuelOfFunction
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (fn : FunctionSpec) : Nat :=
  if hfn : fn ∈ selectorDispatchedFunctions spec then
    (hSupported.supportedFunctionOfSelectorDispatched hfn).helperFuel
  else
    0

def SupportedSpecExceptMappingWrites.helperFuelOfFunction
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (fn : FunctionSpec) : Nat :=
  if hfn : fn ∈ selectorDispatchedFunctions spec then
    (hSupported.supportedFunctionOfSelectorDispatched hfn).helperFuel
  else
    0

def SupportedSpec.helperFuel
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) : Nat :=
  (selectorDispatchedFunctions spec).foldl
    (fun fuel fn => max fuel (hSupported.helperFuelOfFunction fn))
    0

def SupportedSpecExceptMappingWrites.helperFuel
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) : Nat :=
  (selectorDispatchedFunctions spec).foldl
    (fun fuel fn => max fuel (hSupported.helperFuelOfFunction fn))
    0

theorem SupportedSpec.selectorFunctionParamsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).paramsSupported

theorem SupportedSpecExceptMappingWrites.selectorFunctionParamsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).paramsSupported

theorem SupportedSpec.selectorFunctionParamNamesNodup
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    (fn.params.map (·.name)).Nodup :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).paramNamesNodup

theorem SupportedSpecExceptMappingWrites.selectorFunctionParamNamesNodup
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    (fn.params.map (·.name)).Nodup :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).paramNamesNodup

theorem SupportedSpec.selectorFunctionReturnsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).returnsSupported

theorem SupportedSpecExceptMappingWrites.selectorFunctionReturnsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).returnsSupported

@[simp] theorem stmtListTouchesUnsupportedContractSurface_nil :
    stmtListTouchesUnsupportedContractSurface [] = false := rfl

@[simp] theorem exprTouchesUnsupportedContractSurface_storage
    (field : String) :
    exprTouchesUnsupportedContractSurface (.storage field) = true := by
  simp [exprTouchesUnsupportedContractSurface, exprTouchesUnsupportedCoreSurface,
    exprTouchesUnsupportedStateSurface, exprTouchesUnsupportedCallSurface]

@[simp] theorem exprTouchesUnsupportedContractSurface_storageAddr
    (field : String) :
    exprTouchesUnsupportedContractSurface (.storageAddr field) = true := by
  simp [exprTouchesUnsupportedContractSurface, exprTouchesUnsupportedCoreSurface,
    exprTouchesUnsupportedStateSurface, exprTouchesUnsupportedCallSurface]

@[simp] theorem stmtTouchesUnsupportedContractSurface_storageArrayPush
    (field : String) (value : Expr) :
    stmtTouchesUnsupportedContractSurface (.storageArrayPush field value) = true := by
  simp [stmtTouchesUnsupportedContractSurface, stmtTouchesUnsupportedCoreSurface,
    stmtTouchesUnsupportedStateSurface, stmtTouchesUnsupportedCallSurface,
    stmtTouchesUnsupportedEffectSurface]

@[simp] theorem stmtTouchesUnsupportedContractSurface_mstore
    (offset value : Expr) :
    stmtTouchesUnsupportedContractSurface (.mstore offset value) = false := by
  simp [stmtTouchesUnsupportedContractSurface, stmtTouchesUnsupportedCoreSurface,
    stmtTouchesUnsupportedStateSurface, stmtTouchesUnsupportedCallSurface,
    stmtTouchesUnsupportedEffectSurface]

@[simp] theorem stmtTouchesUnsupportedContractSurface_setStorageAddr
    (field : String) (value : Expr) :
    stmtTouchesUnsupportedContractSurface (.setStorageAddr field value) =
      exprTouchesUnsupportedContractSurface value := by
  simp [stmtTouchesUnsupportedContractSurface, stmtTouchesUnsupportedCoreSurface,
    stmtTouchesUnsupportedStateSurface, stmtTouchesUnsupportedCallSurface,
    stmtTouchesUnsupportedEffectSurface]

@[simp] theorem stmtTouchesUnsupportedContractSurface_ite
    (cond : Expr) (thenBranch elseBranch : List Stmt) :
    stmtTouchesUnsupportedContractSurface (.ite cond thenBranch elseBranch) = true := by
  simp [stmtTouchesUnsupportedContractSurface, stmtTouchesUnsupportedCoreSurface,
    stmtTouchesUnsupportedStateSurface, stmtTouchesUnsupportedCallSurface,
    stmtTouchesUnsupportedEffectSurface]

@[simp] theorem stmtTouchesUnsupportedContractSurface_tstore
    (offset value : Expr) :
    stmtTouchesUnsupportedContractSurface (.tstore offset value) = false := by
  simp [stmtTouchesUnsupportedContractSurface, stmtTouchesUnsupportedCoreSurface,
    stmtTouchesUnsupportedStateSurface, stmtTouchesUnsupportedCallSurface,
    stmtTouchesUnsupportedEffectSurface]

@[simp] theorem stmtTouchesUnsupportedContractSurface_storageArrayPop
    (field : String) :
    stmtTouchesUnsupportedContractSurface (.storageArrayPop field) = true := by
  simp [stmtTouchesUnsupportedContractSurface, stmtTouchesUnsupportedCoreSurface,
    stmtTouchesUnsupportedStateSurface, stmtTouchesUnsupportedCallSurface,
    stmtTouchesUnsupportedEffectSurface]

@[simp] theorem stmtTouchesUnsupportedContractSurface_setStorageArrayElement
    (field : String) (index value : Expr) :
    stmtTouchesUnsupportedContractSurface (.setStorageArrayElement field index value) = true := by
  simp [stmtTouchesUnsupportedContractSurface, stmtTouchesUnsupportedCoreSurface,
    stmtTouchesUnsupportedStateSurface, stmtTouchesUnsupportedCallSurface,
    stmtTouchesUnsupportedEffectSurface]

@[simp] theorem selectorDispatchedFunctions_nil :
    selectorDispatchedFunctions
      { name := "Empty", fields := [], reservedSlotRanges := [], slotAliasRanges := [],
        constructor := none, functions := [], events := [], errors := [], externals := [] } = [] := rfl

def counterSupportedSpecModel : CompilationModel :=
  { name := "Counter"
    fields := []
    constructor := none
    functions :=
      [ { name := "getCount"
          params := []
          returnType := some .uint256
          body := [Stmt.return (Expr.literal 42)] } ] }

private theorem counter_noPackedFields :
    ∀ field ∈ counterSupportedSpecModel.fields, field.packedBits = none := by
  intro field hfield
  simp [counterSupportedSpecModel] at hfield

private theorem counter_noFallback :
    ∀ fn ∈ counterSupportedSpecModel.functions, fn.name != "fallback" := by
  intro fn hfn
  simp [counterSupportedSpecModel] at hfn
  rcases hfn with rfl <;> decide

private theorem counter_noReceive :
    ∀ fn ∈ counterSupportedSpecModel.functions, fn.name != "receive" := by
  intro fn hfn
  simp [counterSupportedSpecModel] at hfn
  rcases hfn with rfl <;> decide

private theorem counter_supported_function :
    ∀ fn, fn ∈ counterSupportedSpecModel.functions →
      SupportedFunction counterSupportedSpecModel fn := by
  intro fn hfn
  simp [counterSupportedSpecModel] at hfn
  rcases hfn with rfl
  refine
    { nonInternal := rfl
      nonSpecialEntrypoint := rfl
      params :=
        { namesNodup := by decide
          supported := by intro param hparam; cases hparam }
      returns := { resolved := ⟨[.uint256], rfl, trivial⟩ }
      body :=
        { stmtList := by
            refine .compileCore ?_
            refine FunctionBody.StmtListCompileCore.return_ (.literal 42) ?_ ?_
            · exact FunctionBody.ExprCompileCore.literal 42
            · intro name hname
              simp at hname
            · exact FunctionBody.StmtListCompileCore.nil
          core := { surfaceClosed := by decide }
          state := { surfaceClosed := by decide }
            calls :=
              { helpers :=
                 { helperRank := 0
                   callNamesNodup := helperCallNames_nodup _
                   summaryOf := by
                     intro calleeName hmem
                     simp [helperCallNames] at hmem
                   calleeRanksDecrease := by
                     intro calleeName hmem
                     simp [helperCallNames] at hmem
                   exprCallsPreserveWorld := by
                     intro calleeName hmem
                     simp [exprHelperCallNames] at hmem }
                foreign := by decide
                lowLevel := by decide }
           effects := { surfaceClosed := by decide }
           noLocalObligations := rfl } }

def counter_supported_spec : SupportedSpec counterSupportedSpecModel
    [0xa87d942c] := by
  refine
    { invariants :=
        { normalizedFields := by
            rfl
          noPackedFields := counter_noPackedFields
          selectorCount := by
            decide
          selectorsDistinct := by
            decide
          functionNamesNodup := by
            decide }
      surface :=
        { noConstructor := rfl
          noEvents := rfl
          noErrors := rfl
          noExternals := rfl
          noFallback := counter_noFallback
          noReceive := counter_noReceive }
      functions := counter_supported_function }

def simpleStorageSupportedSpecModel : CompilationModel :=
  { name := "SimpleStorage"
    fields := []
    constructor := none
    functions :=
      [ { name := "retrieve"
          params := []
          returnType := some .uint256
          body := [Stmt.return (Expr.literal 11)] } ] }

private theorem simpleStorage_noPackedFields :
    ∀ field ∈ simpleStorageSupportedSpecModel.fields, field.packedBits = none := by
  intro field hfield
  simp [simpleStorageSupportedSpecModel] at hfield

private theorem simpleStorage_noFallback :
    ∀ fn ∈ simpleStorageSupportedSpecModel.functions, fn.name != "fallback" := by
  intro fn hfn
  simp [simpleStorageSupportedSpecModel] at hfn
  rcases hfn with rfl <;> decide

private theorem simpleStorage_noReceive :
    ∀ fn ∈ simpleStorageSupportedSpecModel.functions, fn.name != "receive" := by
  intro fn hfn
  simp [simpleStorageSupportedSpecModel] at hfn
  rcases hfn with rfl <;> decide

private theorem simpleStorage_supported_function :
    ∀ fn, fn ∈ simpleStorageSupportedSpecModel.functions →
      SupportedFunction simpleStorageSupportedSpecModel fn := by
  intro fn hfn
  simp [simpleStorageSupportedSpecModel] at hfn
  rcases hfn with rfl
  refine
    { nonInternal := rfl
      nonSpecialEntrypoint := rfl
      params :=
        { namesNodup := by decide
          supported := by intro param hparam; cases hparam }
      returns := { resolved := ⟨[.uint256], rfl, trivial⟩ }
      body :=
        { stmtList := by
            refine .compileCore ?_
            refine FunctionBody.StmtListCompileCore.return_ (.literal 11) ?_ ?_
            · exact FunctionBody.ExprCompileCore.literal 11
            · intro name hname
              simp at hname
            · exact FunctionBody.StmtListCompileCore.nil
          core := { surfaceClosed := by decide }
          state := { surfaceClosed := by decide }
            calls :=
              { helpers :=
                 { helperRank := 0
                   callNamesNodup := helperCallNames_nodup _
                   summaryOf := by
                     intro calleeName hmem
                     simp [helperCallNames] at hmem
                   calleeRanksDecrease := by
                     intro calleeName hmem
                     simp [helperCallNames] at hmem
                   exprCallsPreserveWorld := by
                     intro calleeName hmem
                     simp [exprHelperCallNames] at hmem }
                foreign := by decide
                lowLevel := by decide }
           effects := { surfaceClosed := by decide }
           noLocalObligations := rfl } }

def simpleStorage_supported_spec : SupportedSpec simpleStorageSupportedSpecModel
    [0x2e64cec1] := by
  refine
    { invariants :=
        { normalizedFields := by
            rfl
          noPackedFields := simpleStorage_noPackedFields
          selectorCount := by
            decide
          selectorsDistinct := by
            decide
          functionNamesNodup := by
            decide }
      surface :=
        { noConstructor := rfl
          noEvents := rfl
          noErrors := rfl
          noExternals := rfl
          noFallback := simpleStorage_noFallback
          noReceive := simpleStorage_noReceive }
      functions := simpleStorage_supported_function }

end Compiler.Proofs.IRGeneration
