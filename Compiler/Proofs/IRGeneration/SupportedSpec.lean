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
  | .uint256 | .int256 | .uint8 | .address | .bytes32 => True
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
  | .sgt a b | .slt a b | .min a b | .max a b | .wMulDown a b | .wDivUp a b
  | .ceilDiv a b =>
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
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b | .ceilDiv a b =>
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
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b | .ceilDiv a b =>
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
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b | .ceilDiv a b =>
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
  | expr :: rest =>
      exprTouchesUnsupportedHelperSurface expr ||
        exprListTouchesUnsupportedHelperSurface rest

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
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b | .ceilDiv a b =>
      exprTouchesInternalHelperSurface a || exprTouchesInternalHelperSurface b
  | .mapping _ b | .mappingUint _ b | .arrayElement _ b | .storageArrayElement _ b =>
      exprTouchesInternalHelperSurface b
  | .mappingChain _ [] => false
  | .mappingChain field (k :: ks) =>
      exprTouchesInternalHelperSurface k || exprTouchesInternalHelperSurface (.mappingChain field ks)
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
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b | .ceilDiv a b =>
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
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b | .ceilDiv a b =>
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
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b | .ceilDiv a b =>
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
  | .setMapping _ key value | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      exprTouchesUnsupportedCoreSurface key ||
        exprTouchesUnsupportedCoreSurface value
  | .setMappingChain _ keys value =>
      keys.any exprTouchesUnsupportedCoreSurface ||
        exprTouchesUnsupportedCoreSurface value
  | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      exprTouchesUnsupportedCoreSurface key1 ||
        exprTouchesUnsupportedCoreSurface key2 ||
        exprTouchesUnsupportedCoreSurface value
  | .storageArrayPush _ value =>
      exprTouchesUnsupportedCoreSurface value
  | .setStorageArrayElement _ index value =>
      exprTouchesUnsupportedCoreSurface index ||
        exprTouchesUnsupportedCoreSurface value
  | .mstore offset value | .tstore offset value =>
      exprTouchesUnsupportedCoreSurface offset ||
        exprTouchesUnsupportedCoreSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedCoreSurface cond
  | .stop => false
  | .ite _ _ _ | .forEach _ _ _ => true
  | .storageArrayPop _
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
  | .mstore offset value | .tstore offset value =>
      exprTouchesUnsupportedStateSurface offset ||
        exprTouchesUnsupportedStateSurface value
  | .stop
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
  | .setMappingUint _ _ _ | .setStructMember _ _ _ _ | .setMappingChain _ _ _
  | .setMapping2 _ _ _ _ | .setMapping2Word _ _ _ _ _ | .setStructMember2 _ _ _ _ _ =>
      false
  | stmt => stmtTouchesUnsupportedStateSurface stmt

/-- Helper/foreign/runtime-call statement surfaces still outside the current
generic theorem. -/
def stmtTouchesUnsupportedCallSurface : Stmt → Bool
  | .letVar _ value | .assignVar _ value | .setStorage _ value
  | .setStorageAddr _ value | .storageArrayPush _ value =>
      exprTouchesUnsupportedCallSurface value
  | .setMapping _ key value | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      exprTouchesUnsupportedCallSurface key ||
        exprTouchesUnsupportedCallSurface value
  | .setMappingChain _ keys value =>
      keys.any exprTouchesUnsupportedCallSurface ||
        exprTouchesUnsupportedCallSurface value
  | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      exprTouchesUnsupportedCallSurface key1 ||
        exprTouchesUnsupportedCallSurface key2 ||
        exprTouchesUnsupportedCallSurface value
  | .setStorageArrayElement _ index value
  | .mstore index value | .tstore index value =>
      exprTouchesUnsupportedCallSurface index ||
        exprTouchesUnsupportedCallSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedCallSurface cond
  | .internalCall _ _ | .internalCallAssign _ _ _ => true
  | .calldatacopy _ _ _
  | .returndataCopy _ _ _ | .revertReturndata | .externalCallBind _ _ _
  | .ecm _ _ => true
  | .stop | .storageArrayPop _
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
  | .letVar _ value | .assignVar _ value | .setStorage _ value
  | .setStorageAddr _ value | .storageArrayPush _ value =>
      exprTouchesUnsupportedHelperSurface value
  | .setMapping _ key value | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      exprTouchesUnsupportedHelperSurface key ||
        exprTouchesUnsupportedHelperSurface value
  | .setMappingChain _ keys value =>
      exprListTouchesUnsupportedHelperSurface keys ||
        exprTouchesUnsupportedHelperSurface value
  | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      exprTouchesUnsupportedHelperSurface key1 ||
        exprTouchesUnsupportedHelperSurface key2 ||
        exprTouchesUnsupportedHelperSurface value
  | .setStorageArrayElement _ index value
  | .mstore index value | .tstore index value =>
      exprTouchesUnsupportedHelperSurface index ||
        exprTouchesUnsupportedHelperSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedHelperSurface cond
  | .internalCall _ _ | .internalCallAssign _ _ _ => true
  | .stop | .calldatacopy _ _ _
  | .returndataCopy _ _ _ | .revertReturndata | .externalCallBind _ _ _
  | .ecm _ _ | .storageArrayPop _
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
  | .letVar _ value | .assignVar _ value | .setStorage _ value
  | .setStorageAddr _ value | .storageArrayPush _ value =>
      exprTouchesInternalHelperSurface value
  | .setMapping _ key value | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      exprTouchesInternalHelperSurface key ||
        exprTouchesInternalHelperSurface value
  | .setMappingChain _ keys value =>
      keys.any exprTouchesInternalHelperSurface ||
        exprTouchesInternalHelperSurface value
  | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      exprTouchesInternalHelperSurface key1 ||
        exprTouchesInternalHelperSurface key2 ||
        exprTouchesInternalHelperSurface value
  | .setStorageArrayElement _ index value
  | .mstore index value | .tstore index value =>
      exprTouchesInternalHelperSurface index ||
        exprTouchesInternalHelperSurface value
  | .require cond _ | .return cond =>
      exprTouchesInternalHelperSurface cond
  | .internalCall _ _ | .internalCallAssign _ _ _ => true
  | .stop | .calldatacopy _ _ _
  | .returndataCopy _ _ _ | .revertReturndata | .externalCallBind _ _ _
  | .ecm _ _ | .storageArrayPop _ | .requireError _ _ _
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
  | .letVar _ value | .assignVar _ value | .setStorage _ value
  | .setStorageAddr _ value | .storageArrayPush _ value =>
      exprTouchesInternalHelperSurface value
  | .setMapping _ key value | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      exprTouchesInternalHelperSurface key ||
        exprTouchesInternalHelperSurface value
  | .setMappingChain _ keys value =>
      keys.any exprTouchesInternalHelperSurface ||
        exprTouchesInternalHelperSurface value
  | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      exprTouchesInternalHelperSurface key1 ||
        exprTouchesInternalHelperSurface key2 ||
        exprTouchesInternalHelperSurface value
  | .setStorageArrayElement _ index value
  | .mstore index value | .tstore index value =>
      exprTouchesInternalHelperSurface index ||
        exprTouchesInternalHelperSurface value
  | .require cond _ | .return cond =>
      exprTouchesInternalHelperSurface cond
  | .ite cond _ _ =>
      exprTouchesInternalHelperSurface cond
  | .forEach _ count _ =>
      exprTouchesInternalHelperSurface count
  | .internalCall _ _ | .internalCallAssign _ _ _ | .stop
  | .calldatacopy _ _ _ | .returndataCopy _ _ _
  | .revertReturndata | .externalCallBind _ _ _ | .ecm _ _
  | .storageArrayPop _ | .requireError _ _ _
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
  | .letVar _ value | .assignVar _ value | .setStorage _ value
  | .setStorageAddr _ value | .storageArrayPush _ value =>
      exprTouchesUnsupportedForeignSurface value
  | .setMapping _ key value | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      exprTouchesUnsupportedForeignSurface key ||
        exprTouchesUnsupportedForeignSurface value
  | .setMappingChain _ keys value =>
      keys.any exprTouchesUnsupportedForeignSurface ||
        exprTouchesUnsupportedForeignSurface value
  | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      exprTouchesUnsupportedForeignSurface key1 ||
        exprTouchesUnsupportedForeignSurface key2 ||
        exprTouchesUnsupportedForeignSurface value
  | .setStorageArrayElement _ index value
  | .mstore index value | .tstore index value =>
      exprTouchesUnsupportedForeignSurface index ||
        exprTouchesUnsupportedForeignSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedForeignSurface cond
  | .externalCallBind _ _ _ | .ecm _ _ => true
  | .stop
  | .internalCall _ _ | .internalCallAssign _ _ _
  | .calldatacopy _ _ _ | .returndataCopy _ _ _ | .revertReturndata
  | .storageArrayPop _
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
  | .letVar _ value | .assignVar _ value | .setStorage _ value
  | .setStorageAddr _ value | .storageArrayPush _ value =>
      exprTouchesUnsupportedLowLevelSurface value
  | .setMapping _ key value | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      exprTouchesUnsupportedLowLevelSurface key ||
        exprTouchesUnsupportedLowLevelSurface value
  | .setMappingChain _ keys value =>
      keys.any exprTouchesUnsupportedLowLevelSurface ||
        exprTouchesUnsupportedLowLevelSurface value
  | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      exprTouchesUnsupportedLowLevelSurface key1 ||
        exprTouchesUnsupportedLowLevelSurface key2 ||
        exprTouchesUnsupportedLowLevelSurface value
  | .setStorageArrayElement _ index value
  | .mstore index value | .tstore index value =>
      exprTouchesUnsupportedLowLevelSurface index ||
        exprTouchesUnsupportedLowLevelSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedLowLevelSurface cond
  | .calldatacopy _ _ _
  | .returndataCopy _ _ _ | .revertReturndata => true
  | .stop
  | .internalCall _ _ | .internalCallAssign _ _ _ | .externalCallBind _ _ _
  | .ecm _ _ | .storageArrayPop _
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
  | .mstore offset value | .tstore offset value =>
      exprTouchesUnsupportedContractSurface offset ||
        exprTouchesUnsupportedContractSurface value
  | .stop => false
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
  | .setMappingUint _ _ _ | .setStructMember _ _ _ _ | .setMappingChain _ _ _
  | .setMapping2 _ _ _ _ | .setMapping2Word _ _ _ _ _ | .setStructMember2 _ _ _ _ _ =>
      false
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
    | .wDivUp a b | .min a b | .max a b | .ceilDiv a b =>
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

private theorem eraseDups_nodup_and_mem_aux [BEq α] [LawfulBEq α]
    (n : Nat) (l : List α) (hlen : l.length ≤ n) :
    (l.eraseDups).Nodup ∧ (∀ a, a ∈ l.eraseDups ↔ a ∈ l) := by
  induction n generalizing l with
  | zero =>
    have : l = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst this
    exact ⟨List.Pairwise.nil, fun _ => Iff.rfl⟩
  | succ n ih =>
    match l with
    | [] => exact ⟨List.Pairwise.nil, fun _ => Iff.rfl⟩
    | x :: xs =>
      rw [List.eraseDups_cons]
      have hfilt_len : (xs.filter fun b => !b == x).length ≤ n := by
        have := List.length_filter_le (fun b => !b == x) xs
        simp [List.length_cons] at hlen; omega
      have ⟨ihNd, ihMem⟩ := ih _ hfilt_len
      constructor
      · rw [List.nodup_cons]
        constructor
        · intro h
          have hmf := (ihMem x).mp h
          rw [List.mem_filter] at hmf
          have := hmf.2
          simp at this
        · exact ihNd
      · intro a; constructor
        · intro h; rw [List.mem_cons] at h ⊢
          rcases h with rfl | h
          · exact Or.inl rfl
          · exact Or.inr (List.mem_filter.mp ((ihMem a).mp h)).1
        · intro h; rw [List.mem_cons] at h ⊢
          rcases h with rfl | h
          · exact Or.inl rfl
          · by_cases heq : a == x
            · exact Or.inl (beq_iff_eq.mp heq)
            · exact Or.inr ((ihMem a).mpr (List.mem_filter.mpr ⟨h, by simp [heq]⟩))

private theorem List.eraseDups_nodup [BEq α] [LawfulBEq α]
    (l : List α) : (l.eraseDups).Nodup :=
  (eraseDups_nodup_and_mem_aux l.length l (Nat.le_refl _)).1

private theorem List.mem_eraseDups_iff [BEq α] [LawfulBEq α]
    {a : α} {l : List α} : a ∈ l.eraseDups ↔ a ∈ l :=
  (eraseDups_nodup_and_mem_aux l.length l (Nat.le_refl _)).2 a

private theorem List.mem_eraseDups_of_mem [BEq α] [LawfulBEq α]
    {a : α} {l : List α} (h : a ∈ l) : a ∈ l.eraseDups :=
  List.mem_eraseDups_iff.mpr h

private theorem List.mem_of_mem_eraseDups [BEq α] [LawfulBEq α]
    {a : α} {l : List α} (h : a ∈ l.eraseDups) : a ∈ l :=
  List.mem_eraseDups_iff.mp h

/-- Deduplicated direct helper-callee inventory for a function body. -/
def helperCallNames (fn : FunctionSpec) : List String :=
  (stmtListInternalHelperCallNames fn.body).eraseDups

theorem helperCallNames_nodup (fn : FunctionSpec) :
    (helperCallNames fn).Nodup := by
  simpa [helperCallNames] using List.eraseDups_nodup (stmtListInternalHelperCallNames fn.body)

/-- Deduplicated direct helper-callee inventory for expression-position helper uses. -/
def exprHelperCallNames (fn : FunctionSpec) : List String :=
  (stmtListExprHelperCallNames fn.body).eraseDups

theorem exprHelperCallNames_nodup (fn : FunctionSpec) :
    (exprHelperCallNames fn).Nodup := by
  simpa [exprHelperCallNames] using List.eraseDups_nodup (stmtListExprHelperCallNames fn.body)

private theorem stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames
    (stmts : List Stmt)
    {calleeName : String}
    (hmem : calleeName ∈ stmtListExprHelperCallNames stmts) :
    calleeName ∈ stmtListInternalHelperCallNames stmts := by
  match stmts with
  | [] =>
      simpa [stmtListExprHelperCallNames, stmtListInternalHelperCallNames] using hmem
  | stmt :: rest =>
      simp only [stmtListExprHelperCallNames, stmtListInternalHelperCallNames, List.mem_append] at hmem ⊢
      rcases hmem with hstmt | hrest
      · left
        cases stmt with
        | ite cond thenBranch elseBranch =>
            simp only [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_append] at hstmt ⊢
            rcases hstmt with (hcond | hthen) | helse
            · exact Or.inl (Or.inl hcond)
            · exact Or.inl <| Or.inr <|
                stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames thenBranch hthen
            · exact Or.inr <|
                stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames elseBranch helse
        | forEach var count body =>
            simp only [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_append] at hstmt ⊢
            rcases hstmt with hcount | hbody
            · exact Or.inl hcount
            · exact Or.inr <|
                stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames body hbody
        | internalCall calleeName args =>
            simp [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_cons] at hstmt ⊢
            exact Or.inr hstmt
        | internalCallAssign names calleeName args =>
            simp [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_cons] at hstmt ⊢
            exact Or.inr hstmt
        | requireError cond errorName args =>
            simp [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_append] at hstmt ⊢
            exact hstmt
        | revertError errorName args =>
            simpa [stmtExprHelperCallNames, stmtInternalHelperCallNames] using hstmt
        | _ =>
            all_goals
              simpa [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_append,
                or_left_comm, or_assoc] using hstmt
      · exact Or.inr (stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames rest hrest)
termination_by sizeOf stmts
decreasing_by all_goals (subst_vars; simp_wf; simp_all [List.cons.sizeOf_spec]; omega)

theorem stmtExprHelperCallNames_subset_stmtInternalHelperCallNames
    (stmt : Stmt) :
    ∀ {calleeName : String},
      calleeName ∈ stmtExprHelperCallNames stmt →
        calleeName ∈ stmtInternalHelperCallNames stmt := by
  intro calleeName hmem
  have : calleeName ∈ stmtListExprHelperCallNames [stmt] := by
    simp [stmtListExprHelperCallNames, hmem]
  have := stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames [stmt] this
  simp [stmtListInternalHelperCallNames] at this
  exact this

theorem exprHelperCallNames_subset_helperCallNames
    {fn : FunctionSpec}
    {calleeName : String}
    (hmem : calleeName ∈ exprHelperCallNames fn) :
    calleeName ∈ helperCallNames fn := by
  have hexpr : calleeName ∈ stmtListExprHelperCallNames fn.body := by
    exact List.mem_of_mem_eraseDups (show calleeName ∈ (stmtListExprHelperCallNames fn.body).eraseDups from hmem)
  have hhelper : calleeName ∈ stmtListInternalHelperCallNames fn.body :=
    stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames fn.body hexpr
  exact List.mem_eraseDups_of_mem hhelper

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

-- Helper/internal-surface smoke tests omitted: mutual recursion prevents
-- kernel-level `decide` reduction; runtime `native_decide` is not permitted
-- in proof modules by CI hygiene policy.

structure SupportedBodyCoreInterface (fn : FunctionSpec) : Prop where
  surfaceClosed : stmtListTouchesUnsupportedCoreSurface fn.body = false

structure SupportedBodyStateInterface (fn : FunctionSpec) : Prop where
  surfaceClosed : stmtListTouchesUnsupportedStateSurface fn.body = false

structure SupportedBodyStateInterfaceExceptMappingWrites (fn : FunctionSpec) : Prop where
  surfaceClosed : stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites fn.body = false

structure SupportedBodyEffectInterface (fn : FunctionSpec) : Prop where
  surfaceClosed : stmtListTouchesUnsupportedEffectSurface fn.body = false

structure InternalHelperSummaryContract where
  post : Nat → Verity.ContractState → List Nat → Bool → Option Nat → Verity.ContractState → Prop

def InternalHelperSummaryPreservesWorldOnSuccess
    (summary : InternalHelperSummaryContract) : Prop :=
  ∀ fuel initialWorld args success returnValue finalWorld,
    summary.post fuel initialWorld args success returnValue finalWorld →
      success = true →
      finalWorld = initialWorld

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
      simp only [exprTouchesUnsupportedHelperSurface]
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
      simp only [exprTouchesUnsupportedHelperSurface, ihL, ihR, Bool.or_false, Bool.false_or]
  | logicalNot _ ih =>
      simp only [exprTouchesUnsupportedHelperSurface, ih]

private theorem exprCompileCore_internalHelperCallNames_nil
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    exprInternalHelperCallNames expr = [] := by
  induction hcore with
  | literal | param | localVar | caller | contractAddress | msgValue
    | blockTimestamp | blockNumber | chainid =>
      simp only [exprInternalHelperCallNames]
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
      simp only [exprInternalHelperCallNames, ihL, ihR, List.nil_append]
  | logicalNot _ ih =>
      simp only [exprInternalHelperCallNames, ih]

private theorem exprListCompileCore_helperSurfaceClosed
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    exprListTouchesUnsupportedHelperSurface exprs = false := by
  induction exprs with
  | nil =>
      simp only [exprListTouchesUnsupportedHelperSurface,
        Bool.or_false, Bool.false_or]
  | cons expr rest ih =>
      have hhead : FunctionBody.ExprCompileCore expr := hcore expr (by simp)
      have htail : ∀ e ∈ rest, FunctionBody.ExprCompileCore e := by
        intro e he
        exact hcore e (by simp [he])
      simp only [exprListTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hhead,
        ih htail,
        Bool.or_false, Bool.false_or]

private theorem exprListCompileCore_internalHelperCallNames_nil
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    exprListInternalHelperCallNames exprs = [] := by
  induction exprs with
  | nil =>
      simp only [exprListInternalHelperCallNames]
  | cons expr rest ih =>
      have hhead : FunctionBody.ExprCompileCore expr := hcore expr (by simp)
      have htail : ∀ e ∈ rest, FunctionBody.ExprCompileCore e := by
        intro e he
        exact hcore e (by simp [he])
      simp only [exprListInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hhead,
        ih htail, List.nil_append]

private theorem stmtListCompileCore_helperSurfaceClosed
    {scope : List String}
    {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  induction hcore with
  | nil =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        Bool.or_false, Bool.false_or]
  | letVar hvalue _ _ ih
    | assignVar hvalue _ _ ih
    | return_ hvalue _ _ ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hvalue,
        ih,
        Bool.or_false, Bool.false_or]
  | require_ hcond _ _ ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hcond,
        ih,
        Bool.or_false, Bool.false_or]
  | stop _ ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        ih,
        Bool.or_false, Bool.false_or]

private theorem stmtListCompileCore_internalHelperCallNames_nil
    {scope : List String}
    {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    stmtListInternalHelperCallNames stmts = [] := by
  induction hcore with
  | nil =>
      simp only [stmtListInternalHelperCallNames]
  | letVar hvalue _ _ ih
    | assignVar hvalue _ _ ih
    | return_ hvalue _ _ ih =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        ih, List.nil_append, List.append_nil]
  | require_ hcond _ _ ih =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hcond,
        ih, List.nil_append, List.append_nil]
  | stop _ ih =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        ih, List.nil_append, List.append_nil]


private theorem stmtListTerminalCore_internalHelperCallNames_nil
    {scope : List String}
    {stmts : List Stmt}
    (hterminal : FunctionBody.StmtListTerminalCore scope stmts) :
    stmtListInternalHelperCallNames stmts = [] := by
  induction hterminal with
  | letVar hvalue _ _ ih
    | assignVar hvalue _ _ ih =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        ih, List.nil_append, List.append_nil]
  | require_ hcond _ _ ih =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hcond,
        ih, List.nil_append, List.append_nil]
  | return_ hvalue _ hrest =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        stmtListCompileCore_internalHelperCallNames_nil hrest,
        List.nil_append, List.append_nil]
  | stop hrest =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        stmtListCompileCore_internalHelperCallNames_nil hrest,
        List.nil_append, List.append_nil]
  | ite hcond _ hthen helse hrest ihThen ihElse =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hcond,
        ihThen, ihElse,
        stmtListCompileCore_internalHelperCallNames_nil hrest,
        List.nil_append, List.append_nil]


private theorem stmtListTerminalCore_helperSurfaceClosed
    {scope : List String}
    {stmts : List Stmt}
    (hterminal : FunctionBody.StmtListTerminalCore scope stmts) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  induction hterminal with
  | letVar hvalue _ _ ih
    | assignVar hvalue _ _ ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hvalue,
        ih,
        Bool.or_false, Bool.false_or]
  | require_ hcond _ _ ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hcond,
        ih,
        Bool.or_false, Bool.false_or]
  | return_ hvalue _ hrest =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hvalue,
        stmtListCompileCore_helperSurfaceClosed hrest,
        Bool.or_false, Bool.false_or]
  | stop hrest =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        stmtListCompileCore_helperSurfaceClosed hrest,
        Bool.or_false, Bool.false_or]
  | ite hcond _ hthen helse hrest ihThen ihElse =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hcond,
        ihThen, ihElse,
        stmtListCompileCore_helperSurfaceClosed hrest,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_returnMapping_helperSurfaceClosed
    {fieldName : String}
    {key : Expr}
    (hkey : FunctionBody.ExprCompileCore key) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.return (Expr.mapping fieldName key)] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_letStorageField_helperSurfaceClosed
    {tmp fieldName : String} :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.letVar tmp (Expr.storage fieldName)] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_setStorageAddrSingleSlot_helperSurfaceClosed
    {fieldName : String}
    {value : Expr}
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setStorageAddr fieldName value] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hvalue,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_mstoreSingle_helperSurfaceClosed
    {offset value : Expr}
    (hoffset : FunctionBody.ExprCompileCore offset)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.mstore offset value] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hoffset,
    exprCompileCore_helperSurfaceClosed hvalue,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_tstoreSingle_helperSurfaceClosed
    {offset value : Expr}
    (hoffset : FunctionBody.ExprCompileCore offset)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.tstore offset value] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hoffset,
    exprCompileCore_helperSurfaceClosed hvalue,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_letMapping_helperSurfaceClosed
    {tmp fieldName : String}
    {key : Expr}
    (hkey : FunctionBody.ExprCompileCore key) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.letVar tmp (Expr.mapping fieldName key)] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_letMapping2_helperSurfaceClosed
    {tmp fieldName : String}
    {key1 key2 : Expr}
    (hkey1 : FunctionBody.ExprCompileCore key1)
    (hkey2 : FunctionBody.ExprCompileCore key2) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.letVar tmp (Expr.mapping2 fieldName key1 key2)] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey1,
    exprCompileCore_helperSurfaceClosed hkey2,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_letMappingUint_helperSurfaceClosed
    {tmp fieldName : String}
    {key : Expr}
    (hkey : FunctionBody.ExprCompileCore key) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.letVar tmp (Expr.mappingUint fieldName key)] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_setMappingUintSingle_helperSurfaceClosed
    {fieldName : String}
    {key value : Expr}
    (hkey : FunctionBody.ExprCompileCore key)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setMappingUint fieldName key value] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey,
    exprCompileCore_helperSurfaceClosed hvalue,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_setMappingChainSingle_helperSurfaceClosed
    {fieldName : String}
    {keys : List Expr}
    {value : Expr}
    (hkeys : ∀ key ∈ keys, FunctionBody.ExprCompileCore key)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setMappingChain fieldName keys value] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprListCompileCore_helperSurfaceClosed hkeys,
    exprCompileCore_helperSurfaceClosed hvalue,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_setMappingSingle_helperSurfaceClosed
    {fieldName : String}
    {key value : Expr}
    (hkey : FunctionBody.ExprCompileCore key)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setMapping fieldName key value] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey,
    exprCompileCore_helperSurfaceClosed hvalue,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_setMappingWordSingle_helperSurfaceClosed
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    (hkey : FunctionBody.ExprCompileCore key)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setMappingWord fieldName key wordOffset value] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey,
    exprCompileCore_helperSurfaceClosed hvalue,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_setStructMemberSingle_helperSurfaceClosed
    {fieldName memberName : String}
    {key value : Expr}
    (hkey : FunctionBody.ExprCompileCore key)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setStructMember fieldName key memberName value] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey,
    exprCompileCore_helperSurfaceClosed hvalue,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_setMapping2Single_helperSurfaceClosed
    {fieldName : String}
    {key1 key2 value : Expr}
    (hkey1 : FunctionBody.ExprCompileCore key1)
    (hkey2 : FunctionBody.ExprCompileCore key2)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setMapping2 fieldName key1 key2 value] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey1,
    exprCompileCore_helperSurfaceClosed hkey2,
    exprCompileCore_helperSurfaceClosed hvalue,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_setMapping2WordSingle_helperSurfaceClosed
    {fieldName : String}
    {key1 key2 value : Expr}
    {wordOffset : Nat}
    (hkey1 : FunctionBody.ExprCompileCore key1)
    (hkey2 : FunctionBody.ExprCompileCore key2)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setMapping2Word fieldName key1 key2 wordOffset value] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey1,
    exprCompileCore_helperSurfaceClosed hkey2,
    exprCompileCore_helperSurfaceClosed hvalue,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_setMappingPackedWordSingle_helperSurfaceClosed
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {packed : PackedBits}
    (hkey : FunctionBody.ExprCompileCore key)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setMappingPackedWord fieldName key wordOffset packed value] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey,
    exprCompileCore_helperSurfaceClosed hvalue,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_setStructMember2Single_helperSurfaceClosed
    {fieldName memberName : String}
    {key1 key2 value : Expr}
    (hkey1 : FunctionBody.ExprCompileCore key1)
    (hkey2 : FunctionBody.ExprCompileCore key2)
    (hvalue : FunctionBody.ExprCompileCore value) :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.setStructMember2 fieldName key1 key2 memberName value] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
    exprCompileCore_helperSurfaceClosed hkey1,
    exprCompileCore_helperSurfaceClosed hkey2,
    exprCompileCore_helperSurfaceClosed hvalue,
        Bool.or_false, Bool.false_or]

private theorem supportedStmtList_rawLogLiterals_helperSurfaceClosed
    {topics : List Nat}
    {dataOffset dataSize : Nat} :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.rawLog (topics.map Expr.literal) (Expr.literal dataOffset) (Expr.literal dataSize)] = false := by
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
        Bool.or_false, Bool.false_or]

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
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
        Bool.or_false, Bool.false_or]

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
  simp only [stmtListTouchesUnsupportedHelperSurface,
    stmtTouchesUnsupportedHelperSurface,
    exprTouchesUnsupportedHelperSurface,
        Bool.or_false, Bool.false_or]

open Verity.Core.Free in
theorem SupportedStmtList.helperSurfaceClosed
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hSupported : SupportedStmtList fields scope stmts) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  induction hSupported with
  | compileCore hcore => exact stmtListCompileCore_helperSurfaceClosed hcore
  | terminalCore hterminal => exact stmtListTerminalCore_helperSurfaceClosed hterminal
  | setStorageSingleSlot hvalue _ _ =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hvalue,
        Bool.or_false, Bool.false_or]
  | setStorageAddrSingleSlot hvalue _ _ =>
      exact supportedStmtList_setStorageAddrSingleSlot_helperSurfaceClosed hvalue
  | mstoreSingle hoffset _ hvalue _ =>
      exact supportedStmtList_mstoreSingle_helperSurfaceClosed hoffset hvalue
  | tstoreSingle hoffset _ hvalue _ =>
      exact supportedStmtList_tstoreSingle_helperSurfaceClosed hoffset hvalue
  | letStorageField _ =>
      exact supportedStmtList_letStorageField_helperSurfaceClosed
  | returnMapping hkey _ _ =>
      exact supportedStmtList_returnMapping_helperSurfaceClosed hkey
  | letMapping hkey _ _ =>
      exact supportedStmtList_letMapping_helperSurfaceClosed hkey
  | letMapping2 hkey1 _ hkey2 _ _ =>
      exact supportedStmtList_letMapping2_helperSurfaceClosed hkey1 hkey2
  | letMappingUint hkey _ _ =>
      exact supportedStmtList_letMappingUint_helperSurfaceClosed hkey
  | setMappingUintSingle hkey _ hvalue _ _ =>
      exact supportedStmtList_setMappingUintSingle_helperSurfaceClosed hkey hvalue
  | setMappingChainSingle hkeys _ hvalue _ _ =>
      exact supportedStmtList_setMappingChainSingle_helperSurfaceClosed hkeys hvalue
  | setMappingSingle hkey _ hvalue _ _ =>
      exact supportedStmtList_setMappingSingle_helperSurfaceClosed hkey hvalue
  | setMappingWordSingle hkey _ hvalue _ _ =>
      exact supportedStmtList_setMappingWordSingle_helperSurfaceClosed hkey hvalue
  | setMappingPackedWordSingle hkey _ hvalue _ _ _ _ _ _ _ =>
      exact supportedStmtList_setMappingPackedWordSingle_helperSurfaceClosed hkey hvalue
  | setStructMemberSingle hkey _ hvalue _ _ _ _ =>
      exact supportedStmtList_setStructMemberSingle_helperSurfaceClosed hkey hvalue
  | setMapping2Single hkey1 _ hkey2 _ hvalue _ _ =>
      exact supportedStmtList_setMapping2Single_helperSurfaceClosed hkey1 hkey2 hvalue
  | setMapping2WordSingle hkey1 _ hkey2 _ hvalue _ _ =>
      exact supportedStmtList_setMapping2WordSingle_helperSurfaceClosed hkey1 hkey2 hvalue
  | setStructMember2Single hkey1 _ hkey2 _ hvalue _ _ _ _ =>
      exact supportedStmtList_setStructMember2Single_helperSurfaceClosed hkey1 hkey2 hvalue
  | rawLogLiterals _ =>
      exact supportedStmtList_rawLogLiterals_helperSurfaceClosed
  | letCallerLetStorageReqEqReqNeqSetStorageParamStop _ _ _ _ =>
      exact supportedStmtList_letCallerLetStorageReqEqReqNeqSetStorageParamStop_helperSurfaceClosed
  | letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop _ _ _ _ _ _ =>
      exact supportedStmtList_letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop_helperSurfaceClosed
  | requireClause clause _ ih =>
      simp [stmtListTouchesUnsupportedHelperSurface]
      constructor
      · cases clause with | mk family n m p q message =>
          cases family with
          | binary op =>
              cases op <;> simp [RequireLiteralGuardFamilyClause.toStmt,
                stmtTouchesUnsupportedHelperSurface, exprTouchesUnsupportedHelperSurface]
          | andEqLt =>
              simp [RequireLiteralGuardFamilyClause.toStmt,
                stmtTouchesUnsupportedHelperSurface, exprTouchesUnsupportedHelperSurface]
          | orEqLt =>
              simp [RequireLiteralGuardFamilyClause.toStmt,
                stmtTouchesUnsupportedHelperSurface, exprTouchesUnsupportedHelperSurface]
      · exact ih
  | ite hcond _ _ _ ihThen ihElse =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hcond,
        ihThen, ihElse,
        Bool.or_false, Bool.false_or]
  | @append _ _ pfx sfx _ _ ihPfx ihSfx =>
      suffices h : ∀ (xs ys : List Stmt),
          stmtListTouchesUnsupportedHelperSurface xs = false →
          stmtListTouchesUnsupportedHelperSurface ys = false →
          stmtListTouchesUnsupportedHelperSurface (xs ++ ys) = false from
        h pfx sfx ihPfx ihSfx
      intro xs ys hxs hys
      induction xs with
      | nil => simpa
      | cons x xs' ihx =>
          simp only [List.cons_append, stmtListTouchesUnsupportedHelperSurface]
          simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hxs
          simp [hxs.1, ihx hxs.2]


private theorem exprListInternalHelperCallNames_literals
    (xs : List Nat) :
    exprListInternalHelperCallNames (xs.map Expr.literal) = [] := by
  induction xs with
  | nil => simp [exprListInternalHelperCallNames]
  | cons x xs ih =>
      simp [List.map, exprListInternalHelperCallNames, exprInternalHelperCallNames, ih]

open Verity.Core.Free in
theorem SupportedStmtList.internalHelperCallNames_nil
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hSupported : SupportedStmtList fields scope stmts) :
    stmtListInternalHelperCallNames stmts = [] := by
  induction hSupported with
  | compileCore hcore => exact stmtListCompileCore_internalHelperCallNames_nil hcore
  | terminalCore hterminal => exact stmtListTerminalCore_internalHelperCallNames_nil hterminal
  | setStorageSingleSlot hvalue _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        List.nil_append, List.append_nil]
  | setStorageAddrSingleSlot hvalue _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        List.nil_append, List.append_nil]
  | mstoreSingle hoffset _ hvalue _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hoffset,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        List.nil_append, List.append_nil]
  | tstoreSingle hoffset _ hvalue _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hoffset,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        List.nil_append, List.append_nil]
  | letStorageField _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprInternalHelperCallNames,
        List.nil_append, List.append_nil]
  | returnMapping hkey _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey,
        List.nil_append, List.append_nil]
  | letMapping hkey _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey,
        List.nil_append, List.append_nil]
  | letMapping2 hkey1 _ hkey2 _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey1,
        exprCompileCore_internalHelperCallNames_nil hkey2,
        List.nil_append, List.append_nil]
  | letMappingUint hkey _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey,
        List.nil_append, List.append_nil]
  | setMappingUintSingle hkey _ hvalue _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        List.nil_append, List.append_nil]
  | setMappingChainSingle hkeys _ hvalue _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprListCompileCore_internalHelperCallNames_nil hkeys,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        List.nil_append, List.append_nil]
  | setMappingSingle hkey _ hvalue _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        List.nil_append, List.append_nil]
  | setMappingWordSingle hkey _ hvalue _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        List.nil_append, List.append_nil]
  | setMappingPackedWordSingle hkey _ hvalue _ _ _ _ _ _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        List.nil_append, List.append_nil]
  | setStructMemberSingle hkey _ hvalue _ _ _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        List.nil_append, List.append_nil]
  | setMapping2Single hkey1 _ hkey2 _ hvalue _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey1,
        exprCompileCore_internalHelperCallNames_nil hkey2,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        List.nil_append, List.append_nil]
  | setMapping2WordSingle hkey1 _ hkey2 _ hvalue _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey1,
        exprCompileCore_internalHelperCallNames_nil hkey2,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        List.nil_append, List.append_nil]
  | setStructMember2Single hkey1 _ hkey2 _ hvalue _ _ _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hkey1,
        exprCompileCore_internalHelperCallNames_nil hkey2,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        List.nil_append, List.append_nil]
  | rawLogLiterals _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprInternalHelperCallNames,
        exprListInternalHelperCallNames_literals,
        List.nil_append, List.append_nil]
  | letCallerLetStorageReqEqReqNeqSetStorageParamStop _ _ _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprInternalHelperCallNames,
        List.nil_append, List.append_nil]
  | letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop _ _ _ _ _ _ =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprInternalHelperCallNames,
        List.nil_append, List.append_nil]
  | requireClause clause _ ih =>
      simp [stmtListInternalHelperCallNames]
      constructor
      · cases clause with | mk family n m p q message =>
          cases family with
          | binary op =>
              cases op <;> simp [RequireLiteralGuardFamilyClause.toStmt,
                stmtInternalHelperCallNames, exprInternalHelperCallNames]
          | andEqLt =>
              simp [RequireLiteralGuardFamilyClause.toStmt,
                stmtInternalHelperCallNames, exprInternalHelperCallNames]
          | orEqLt =>
              simp [RequireLiteralGuardFamilyClause.toStmt,
                stmtInternalHelperCallNames, exprInternalHelperCallNames]
      · exact ih
  | ite hcond _ _ _ ihThen ihElse =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hcond,
        ihThen, ihElse, List.nil_append, List.append_nil]
  | @append _ _ pfx sfx _ _ ihPfx ihSfx =>
      suffices h : ∀ (xs ys : List Stmt),
          stmtListInternalHelperCallNames xs = [] →
          stmtListInternalHelperCallNames ys = [] →
          stmtListInternalHelperCallNames (xs ++ ys) = [] from
        h pfx sfx ihPfx ihSfx
      intro xs ys hxs hys
      induction xs with
      | nil => simpa
      | cons x xs' ihx =>
          simp only [List.cons_append, stmtListInternalHelperCallNames]
          have : stmtInternalHelperCallNames x ++ stmtListInternalHelperCallNames xs' = [] := by
            simpa [stmtListInternalHelperCallNames] using hxs
          have hx : stmtInternalHelperCallNames x = [] := List.append_eq_nil.mp this |>.1
          have hxs' : stmtListInternalHelperCallNames xs' = [] := List.append_eq_nil.mp this |>.2
          simp [hx, ihx hxs']


theorem SupportedBodyInterface.helperCallNames_nil
    {spec : CompilationModel} {fn : FunctionSpec}
    (hBody : SupportedBodyInterface spec fn) :
    helperCallNames fn = [] := by
  simp [helperCallNames, hBody.stmtList.internalHelperCallNames_nil]

mutual
  theorem exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed
      {expr : Expr}
      (hsurface : exprTouchesUnsupportedHelperSurface expr = false) :
      exprTouchesInternalHelperSurface expr = false := by
    cases expr with
    | internalCall _ _ => simp [exprTouchesUnsupportedHelperSurface] at hsurface
    | mappingChain _ _ => simp [exprTouchesUnsupportedHelperSurface] at hsurface
    | literal _ | param _ | caller | contractAddress | chainid | msgValue
    | blockTimestamp | blockNumber | localVar _ | storage _ | storageAddr _
    | constructorArg _ | blobbasefee | calldatasize | returndataSize
    | arrayLength _ | storageArrayLength _ | dynamicBytesEq _ _
    | externalCall _ _ =>
        simp [exprTouchesInternalHelperSurface]
    | mload a | tload a | calldataload a | extcodesize a
    | returndataOptionalBoolAt a =>
        simp [exprTouchesInternalHelperSurface]
    | keccak256 a b =>
        simp [exprTouchesInternalHelperSurface]
    | call g t v io is oo os =>
        simp [exprTouchesInternalHelperSurface]
    | staticcall g t io is oo os | delegatecall g t io is oo os =>
        simp [exprTouchesInternalHelperSurface]
    | add a b | sub a b | mul a b | div a b | mod a b
    | eq a b | ge a b | gt a b | lt a b | le a b
    | logicalAnd a b | logicalOr a b =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have ⟨ha, hb⟩ := Bool.or_eq_false_iff.mp hsurface
        simp [exprTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed ha,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hb]
    | sdiv a b | smod a b | bitAnd a b | bitOr a b | bitXor a b
    | sgt a b | slt a b | min a b | max a b | wMulDown a b | wDivUp a b =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have ⟨ha, hb⟩ := Bool.or_eq_false_iff.mp hsurface
        simp [exprTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed ha,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hb]
    | shl a b | shr a b | sar a b | signextend a b =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have ⟨ha, hb⟩ := Bool.or_eq_false_iff.mp hsurface
        simp [exprTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed ha,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hb]
    | bitNot a | logicalNot a =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        simp [exprTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface]
    | mapping _ b | mappingUint _ b | arrayElement _ b | storageArrayElement _ b
    | mappingWord _ b _ | mappingPackedWord _ b _ _ | structMember _ b _ =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        simp [exprTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface]
    | mapping2 _ a b | mapping2Word _ a b _ | structMember2 _ a b _ =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have ⟨ha, hb⟩ := Bool.or_eq_false_iff.mp hsurface
        simp [exprTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed ha,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hb]
    | ceilDiv a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ⟨ha, hb⟩ := hsurface
        simp [exprTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed ha,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hb]
    | mulDivDown a b c | mulDivUp a b c =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        simp [exprTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1.1,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1.2,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2]
    | ite c t e =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        simp [exprTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1.1,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1.2,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2]
  termination_by sizeOf expr

  theorem exprListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed
      {exprs : List Expr}
      (hsurface : exprListTouchesUnsupportedHelperSurface exprs = false) :
      exprs.any exprTouchesInternalHelperSurface = false := by
    cases exprs with
    | nil =>
        simp
    | cons expr rest =>
        simp only [exprListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        simp [exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
          exprListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2]
  termination_by sizeOf exprs

  theorem stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed
      {stmt : Stmt}
      (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
      stmtTouchesInternalHelperSurface stmt = false := by
    cases stmt with
    | letVar _ value | assignVar _ value | setStorage _ value
    | setStorageAddr _ value | storageArrayPush _ value =>
        simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
        simp [stmtTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface]
    | setMapping _ key value | setMappingWord _ key _ value
    | setMappingPackedWord _ key _ _ value | setMappingUint _ key value
    | setStructMember _ key _ value =>
        simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        simp [stmtTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2]
    | setMappingChain _ keys value =>
        simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        simp [stmtTouchesInternalHelperSurface,
          exprListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2]
    | setMapping2 _ key1 key2 value | setMapping2Word _ key1 key2 _ value
    | setStructMember2 _ key1 key2 _ value =>
        simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff, Bool.or_assoc] at hsurface
        simp [stmtTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2.1,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2.2]
    | setStorageArrayElement _ index value | mstore index value | tstore index value =>
        simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        simp [stmtTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2]
    | require cond _ | «return» cond =>
        simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
        simp [stmtTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface]
    | internalCall _ _ | internalCallAssign _ _ _ =>
        simp [stmtTouchesUnsupportedHelperSurface] at hsurface
    | ite cond thenBranch elseBranch =>
        simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        simp [stmtTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1.1,
          stmtListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1.2,
          stmtListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2]
    | forEach _ count body =>
        simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        simp [stmtTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
          stmtListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2]
    | stop | calldatacopy _ _ _ | returndataCopy _ _ _ | revertReturndata
    | externalCallBind _ _ _ | ecm _ _ | storageArrayPop _ | requireError _ _ _
    | revertError _ _ | returnValues _ | returnArray _ | returnBytes _
    | returnStorageWords _ | emit _ _ | rawLog _ _ _ =>
        simp [stmtTouchesInternalHelperSurface]
  termination_by sizeOf stmt

  theorem stmtListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed
      {stmts : List Stmt}
      (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
      stmtListTouchesInternalHelperSurface stmts = false := by
    cases stmts with
    | nil => simp [stmtListTouchesInternalHelperSurface]
    | cons stmt rest =>
        simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        simp [stmtListTouchesInternalHelperSurface,
          stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
          stmtListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2]
  termination_by sizeOf stmts
end

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
      stmtTouchesStructuralInternalHelperSurface,
      Bool.or_assoc]


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
  have := stmtTouchesDirectInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface
  rw [stmtTouchesDirectInternalHelperSurface_eq_split] at this
  exact (Bool.or_eq_false_iff.mp this).1

theorem stmtTouchesDirectInternalHelperAssignSurface_eq_false_of_helperSurfaceClosed
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    stmtTouchesDirectInternalHelperAssignSurface stmt = false := by
  have := stmtTouchesDirectInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface
  rw [stmtTouchesDirectInternalHelperSurface_eq_split] at this
  exact (Bool.or_eq_false_iff.mp this).2

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

theorem stmtListTouchesDirectInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesDirectInternalHelperSurface stmts = false := by
  induction stmts with
  | nil => simp [stmtListTouchesDirectInternalHelperSurface]
  | cons stmt rest ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      simp [stmtListTouchesDirectInternalHelperSurface,
        stmtTouchesDirectInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
        ih hsurface.2]

theorem stmtListTouchesDirectInternalHelperCallSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesDirectInternalHelperCallSurface stmts = false := by
  induction stmts with
  | nil => simp [stmtListTouchesDirectInternalHelperCallSurface]
  | cons stmt rest ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      simp [stmtListTouchesDirectInternalHelperCallSurface,
        stmtTouchesDirectInternalHelperCallSurface_eq_false_of_helperSurfaceClosed hsurface.1,
        ih hsurface.2]

theorem stmtListTouchesDirectInternalHelperAssignSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesDirectInternalHelperAssignSurface stmts = false := by
  induction stmts with
  | nil => simp [stmtListTouchesDirectInternalHelperAssignSurface]
  | cons stmt rest ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      simp [stmtListTouchesDirectInternalHelperAssignSurface,
        stmtTouchesDirectInternalHelperAssignSurface_eq_false_of_helperSurfaceClosed hsurface.1,
        ih hsurface.2]

theorem stmtListTouchesExprInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesExprInternalHelperSurface stmts = false := by
  induction stmts with
  | nil => simp [stmtListTouchesExprInternalHelperSurface]
  | cons stmt rest ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      simp [stmtListTouchesExprInternalHelperSurface,
        stmtTouchesExprInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
        ih hsurface.2]

theorem stmtListTouchesStructuralInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesStructuralInternalHelperSurface stmts = false := by
  induction stmts with
  | nil => simp [stmtListTouchesStructuralInternalHelperSurface]
  | cons stmt rest ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      simp [stmtListTouchesStructuralInternalHelperSurface,
        stmtTouchesStructuralInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
        ih hsurface.2]


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


-- NOTE: The theorem statement below claims an exact decomposition of the
-- monolithic contract surface into sub-surfaces.  However the current
-- definition of `exprTouchesUnsupportedContractSurface` treats some
-- constructors (sdiv, smod, bitAnd, …) differently from the per-surface
-- functions (the contract surface recurses while the core surface returns
-- true directly), making the equality unprovable as-is.
--
-- Concrete counterexample at the expression level:
--   exprTouchesUnsupportedContractSurface (Expr.sdiv (Expr.literal 1) (Expr.literal 2))
--     = (false || false) = false  (recurses on both arguments)
--   exprTouchesUnsupportedCoreSurface (Expr.sdiv (Expr.literal 1) (Expr.literal 2))
--     = true  (returns true directly for sdiv, without checking arguments)
--
-- Similarly, for `.ite` statements:
--   stmtTouchesUnsupportedContractSurface (.ite cond thenBranch elseBranch) = true
--   but the OR of sub-predicates recurses on cond and branches, giving different results.
--
-- The statement needs revision by project authors.
-- This theorem was removed because the stated equality is unprovable with the
-- current definitions and is not used in any downstream proof.

private theorem exprTouchesUnsupportedCallSurface_eq_featureOr
    (expr : Expr) :
    exprTouchesUnsupportedCallSurface expr =
      (exprTouchesUnsupportedHelperSurface expr ||
        exprTouchesUnsupportedForeignSurface expr ||
        exprTouchesUnsupportedLowLevelSurface expr) := by
  cases expr with
  | literal _ | param _ | caller | contractAddress
  | chainid | msgValue | blockTimestamp | blockNumber
  | localVar _ | storage _ | storageAddr _
  | constructorArg _ | blobbasefee | calldatasize | returndataSize =>
      simp [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface]
  | internalCall _ _ | externalCall _ _ =>
      simp [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface]
  | call _ _ _ _ _ _ _ | staticcall _ _ _ _ _ _ | delegatecall _ _ _ _ _ _ =>
      simp [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface]
  | mload _ | tload _ | calldataload _ | extcodesize _
  | returndataOptionalBoolAt _ | keccak256 _ _ | arrayLength _
  | storageArrayLength _ | dynamicBytesEq _ _ =>
      simp [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface]
  | add a b | sub a b | mul a b
  | div a b | mod a b
  | sdiv a b | smod a b
  | bitAnd a b | bitOr a b | bitXor a b
  | eq a b | ge a b | gt a b
  | sgt a b | lt a b | slt a b
  | le a b
  | logicalAnd a b | logicalOr a b
  | min a b | max a b | wMulDown a b | wDivUp a b =>
      simp only [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface]
      rw [exprTouchesUnsupportedCallSurface_eq_featureOr a,
          exprTouchesUnsupportedCallSurface_eq_featureOr b]
      simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  | bitNot a | logicalNot a =>
      simp only [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface]
      exact exprTouchesUnsupportedCallSurface_eq_featureOr a
  | mapping _ b | mappingUint _ b | arrayElement _ b
  | storageArrayElement _ b =>
      simp only [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface]
      exact exprTouchesUnsupportedCallSurface_eq_featureOr b
  | mappingWord _ a _ | mappingPackedWord _ a _ _
  | structMember _ a _ =>
      simp only [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface]
      exact exprTouchesUnsupportedCallSurface_eq_featureOr a
  | mappingChain _ _ =>
      simp [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface]
  | ite cond thenVal elseVal =>
      simp only [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface]
      rw [exprTouchesUnsupportedCallSurface_eq_featureOr cond,
          exprTouchesUnsupportedCallSurface_eq_featureOr thenVal,
          exprTouchesUnsupportedCallSurface_eq_featureOr elseVal]
      simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  | mapping2 _ a b | mapping2Word _ a b _
  | structMember2 _ a b _ =>
      simp only [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface]
      rw [exprTouchesUnsupportedCallSurface_eq_featureOr a,
          exprTouchesUnsupportedCallSurface_eq_featureOr b]
      simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  | ceilDiv a b =>
      simp only [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface]
      rw [exprTouchesUnsupportedCallSurface_eq_featureOr a,
          exprTouchesUnsupportedCallSurface_eq_featureOr b]
      simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  | mulDivDown a b c | mulDivUp a b c =>
      simp only [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface]
      rw [exprTouchesUnsupportedCallSurface_eq_featureOr a,
          exprTouchesUnsupportedCallSurface_eq_featureOr b,
          exprTouchesUnsupportedCallSurface_eq_featureOr c]
      simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  | shl a b | shr a b | sar a b | signextend a b =>
      simp only [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface]
      rw [exprTouchesUnsupportedCallSurface_eq_featureOr a,
          exprTouchesUnsupportedCallSurface_eq_featureOr b]
      simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
termination_by sizeOf expr
decreasing_by all_goals (subst_vars; simp_wf; try omega)

private theorem exprListTouchesUnsupportedCallSurface_eq_featureOr
    (exprs : List Expr) :
    exprs.any exprTouchesUnsupportedCallSurface =
      (exprs.any exprTouchesUnsupportedForeignSurface ||
        exprListTouchesUnsupportedHelperSurface exprs ||
        exprs.any exprTouchesUnsupportedLowLevelSurface) := by
  induction exprs with
  | nil =>
      simp [exprListTouchesUnsupportedHelperSurface]
  | cons expr rest ih =>
      simp only [List.any_cons, exprListTouchesUnsupportedHelperSurface]
      rw [exprTouchesUnsupportedCallSurface_eq_featureOr, ih]
      simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

theorem stmtListTouchesUnsupportedCallSurface_eq_featureOr
    (stmts : List Stmt) :
    stmtListTouchesUnsupportedCallSurface stmts =
      (stmtListTouchesUnsupportedHelperSurface stmts ||
        stmtListTouchesUnsupportedForeignSurface stmts ||
        stmtListTouchesUnsupportedLowLevelSurface stmts) := by
  match stmts with
  | [] =>
      simp [stmtListTouchesUnsupportedCallSurface, stmtListTouchesUnsupportedHelperSurface,
        stmtListTouchesUnsupportedForeignSurface, stmtListTouchesUnsupportedLowLevelSurface]
  | stmt :: rest =>
      unfold stmtListTouchesUnsupportedCallSurface
      unfold stmtListTouchesUnsupportedHelperSurface stmtListTouchesUnsupportedForeignSurface
        stmtListTouchesUnsupportedLowLevelSurface
      rw [stmtListTouchesUnsupportedCallSurface_eq_featureOr rest]
      cases stmt with
      | ite cond thenBranch elseBranch =>
          simp only [stmtTouchesUnsupportedCallSurface,
            stmtTouchesUnsupportedHelperSurface, stmtTouchesUnsupportedForeignSurface,
            stmtTouchesUnsupportedLowLevelSurface]
          rw [exprTouchesUnsupportedCallSurface_eq_featureOr,
              stmtListTouchesUnsupportedCallSurface_eq_featureOr thenBranch,
              stmtListTouchesUnsupportedCallSurface_eq_featureOr elseBranch]
          simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
      | forEach _ count body =>
          simp only [stmtTouchesUnsupportedCallSurface,
            stmtTouchesUnsupportedHelperSurface, stmtTouchesUnsupportedForeignSurface,
            stmtTouchesUnsupportedLowLevelSurface]
          rw [exprTouchesUnsupportedCallSurface_eq_featureOr,
              stmtListTouchesUnsupportedCallSurface_eq_featureOr body]
          simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
      | setMappingChain _ keys value =>
          simp only [stmtTouchesUnsupportedCallSurface,
            stmtTouchesUnsupportedHelperSurface, stmtTouchesUnsupportedForeignSurface,
            stmtTouchesUnsupportedLowLevelSurface]
          rw [exprListTouchesUnsupportedCallSurface_eq_featureOr,
              exprTouchesUnsupportedCallSurface_eq_featureOr value]
          simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
      | _ =>
          all_goals simp [stmtTouchesUnsupportedCallSurface,
            stmtTouchesUnsupportedHelperSurface, stmtTouchesUnsupportedForeignSurface,
            stmtTouchesUnsupportedLowLevelSurface,
            exprTouchesUnsupportedCallSurface_eq_featureOr,
            Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
termination_by sizeOf stmts
decreasing_by all_goals (subst_vars; simp_wf; simp_all [List.cons.sizeOf_spec]; omega)


private theorem exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed
    (expr : Expr)
    (hcore : exprTouchesUnsupportedCoreSurface expr = false)
    (hstate : exprTouchesUnsupportedStateSurface expr = false)
    (hcalls : exprTouchesUnsupportedCallSurface expr = false) :
    exprTouchesUnsupportedContractSurface expr = false := by
  cases expr with
  | literal _ | param _ | localVar _ | caller | contractAddress
  | chainid | msgValue | blockTimestamp | blockNumber =>
      simp [exprTouchesUnsupportedContractSurface]
  | storage _ | storageAddr _ =>
      cases hstate
  | constructorArg _ | blobbasefee
  | calldatasize | returndataSize | arrayLength _ | storageArrayLength _
  | returndataOptionalBoolAt _ | mload _ | tload _ | calldataload _ | extcodesize _
  | dynamicBytesEq _ _ | keccak256 _ _ =>
      cases hcore
  | add lhs rhs | sub lhs rhs | mul lhs rhs
  | div lhs rhs | mod lhs rhs
  | eq lhs rhs | ge lhs rhs | gt lhs rhs
  | lt lhs rhs | le lhs rhs
  | logicalAnd lhs rhs | logicalOr lhs rhs =>
      simp only [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff] at hcore
      simp only [exprTouchesUnsupportedStateSurface, Bool.or_eq_false_iff] at hstate
      simp only [exprTouchesUnsupportedCallSurface, Bool.or_eq_false_iff] at hcalls
      simp [exprTouchesUnsupportedContractSurface,
        exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed lhs hcore.1 hstate.1 hcalls.1,
        exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed rhs hcore.2 hstate.2 hcalls.2]
  | sdiv _ _ | smod _ _ | bitAnd _ _ | bitOr _ _
  | bitXor _ _ | sgt _ _ | slt _ _ | min _ _
  | max _ _ | wMulDown _ _ | wDivUp _ _ | ceilDiv _ _ | bitNot _
  | shl _ _ | shr _ _ | sar _ _ | signextend _ _
  | mulDivDown _ _ _ | mulDivUp _ _ _ =>
      cases hcore
  | logicalNot a =>
      simp only [exprTouchesUnsupportedCoreSurface] at hcore
      simp only [exprTouchesUnsupportedStateSurface] at hstate
      simp only [exprTouchesUnsupportedCallSurface] at hcalls
      simp [exprTouchesUnsupportedContractSurface,
        exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed a hcore hstate hcalls]
  | ite cond thenVal elseVal =>
      simp only [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff, Bool.or_assoc] at hcore
      simp only [exprTouchesUnsupportedStateSurface, Bool.or_eq_false_iff, Bool.or_assoc] at hstate
      simp only [exprTouchesUnsupportedCallSurface, Bool.or_eq_false_iff, Bool.or_assoc] at hcalls
      simp [exprTouchesUnsupportedContractSurface,
        exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed cond hcore.1 hstate.1 hcalls.1,
        exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed thenVal hcore.2.1 hstate.2.1 hcalls.2.1,
        exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed elseVal hcore.2.2 hstate.2.2 hcalls.2.2]
  | mapping _ _ | mappingWord _ _ _ | mappingPackedWord _ _ _ _
  | mapping2 _ _ _ | mapping2Word _ _ _ _ | mappingUint _ _
  | mappingChain _ _ | structMember _ _ _ | structMember2 _ _ _ _
  | arrayElement _ _ | storageArrayElement _ _
  | call _ _ _ _ _ _ _ | staticcall _ _ _ _ _ _ | delegatecall _ _ _ _ _ _
  | externalCall _ _ | internalCall _ _ =>
      cases hcore
termination_by sizeOf expr
decreasing_by all_goals (subst_vars; simp_wf; try omega)

private theorem exprListTouchesUnsupportedContractSurface_eq_false_of_featureClosed
    (exprs : List Expr)
    (hcore : exprs.any exprTouchesUnsupportedCoreSurface = false)
    (hstate : exprs.any exprTouchesUnsupportedStateSurface = false)
    (hcalls : exprs.any exprTouchesUnsupportedCallSurface = false) :
    exprs.any exprTouchesUnsupportedContractSurface = false := by
  induction exprs with
  | nil =>
      simp
  | cons expr rest ih =>
      simp only [List.any_cons, Bool.or_eq_false_iff] at hcore hstate hcalls ⊢
      exact ⟨exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed expr
          hcore.1 hstate.1 hcalls.1,
        ih hcore.2 hstate.2 hcalls.2⟩

private theorem exprTouchesUnsupportedCallSurface_eq_false_of_coreClosed
    (expr : Expr)
    (hcore : exprTouchesUnsupportedCoreSurface expr = false) :
    exprTouchesUnsupportedCallSurface expr = false := by
  cases expr with
  | literal _ | param _ | localVar _ | caller | contractAddress
  | chainid | msgValue | blockTimestamp | blockNumber
  | storage _ | storageAddr _ =>
      simp [exprTouchesUnsupportedCallSurface]
  | add a b | sub a b | mul a b | div a b | mod a b
  | eq a b | ge a b | gt a b | lt a b | le a b
  | logicalAnd a b | logicalOr a b =>
      simp only [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff] at hcore
      simp [exprTouchesUnsupportedCallSurface,
        exprTouchesUnsupportedCallSurface_eq_false_of_coreClosed a hcore.1,
        exprTouchesUnsupportedCallSurface_eq_false_of_coreClosed b hcore.2]
  | logicalNot a =>
      simp only [exprTouchesUnsupportedCoreSurface] at hcore
      simp [exprTouchesUnsupportedCallSurface,
        exprTouchesUnsupportedCallSurface_eq_false_of_coreClosed a hcore]
  | ite cond thenVal elseVal =>
      simp only [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff, Bool.or_assoc] at hcore
      simp [exprTouchesUnsupportedCallSurface,
        exprTouchesUnsupportedCallSurface_eq_false_of_coreClosed cond hcore.1,
        exprTouchesUnsupportedCallSurface_eq_false_of_coreClosed thenVal hcore.2.1,
        exprTouchesUnsupportedCallSurface_eq_false_of_coreClosed elseVal hcore.2.2]
  | _ => cases hcore
termination_by sizeOf expr
decreasing_by all_goals (subst_vars; simp_wf; try omega)

private theorem stmtTouchesUnsupportedContractSurface_eq_false_of_featureClosed
    (stmt : Stmt)
    (hcore : stmtTouchesUnsupportedCoreSurface stmt = false)
    (hstate : stmtTouchesUnsupportedStateSurface stmt = false)
    (hcalls : stmtTouchesUnsupportedCallSurface stmt = false)
    (heffects : stmtTouchesUnsupportedEffectSurface stmt = false) :
    stmtTouchesUnsupportedContractSurface stmt = false := by
  cases stmt with
  | letVar _ value | assignVar _ value | setStorage _ value =>
      simp only [stmtTouchesUnsupportedContractSurface]
      exact exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed value
        (by simpa [stmtTouchesUnsupportedCoreSurface] using hcore)
        (by simpa [stmtTouchesUnsupportedStateSurface] using hstate)
        (by simpa [stmtTouchesUnsupportedCallSurface] using hcalls)
  | setStorageAddr _ value =>
      simp only [stmtTouchesUnsupportedContractSurface]
      exact exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed value
        (by simpa [stmtTouchesUnsupportedCoreSurface] using hcore)
        (by simpa [stmtTouchesUnsupportedStateSurface] using hstate)
        (by exact exprTouchesUnsupportedCallSurface_eq_false_of_coreClosed value
              (by simpa [stmtTouchesUnsupportedCoreSurface] using hcore))
  | require cond _ | «return» cond =>
      simp only [stmtTouchesUnsupportedContractSurface]
      exact exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed cond
        (by simpa [stmtTouchesUnsupportedCoreSurface] using hcore)
        (by simpa [stmtTouchesUnsupportedStateSurface] using hstate)
        (by simpa [stmtTouchesUnsupportedCallSurface] using hcalls)
  | stop => simp [stmtTouchesUnsupportedContractSurface]
  | mstore offset value | tstore offset value =>
      simp only [stmtTouchesUnsupportedContractSurface, Bool.or_eq_false_iff]
      have hcore' :
          exprTouchesUnsupportedCoreSurface offset = false ∧
            exprTouchesUnsupportedCoreSurface value = false := by
        simpa [stmtTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff] using hcore
      have hstate' :
          exprTouchesUnsupportedStateSurface offset = false ∧
            exprTouchesUnsupportedStateSurface value = false := by
        simpa [stmtTouchesUnsupportedStateSurface, Bool.or_eq_false_iff] using hstate
      have hcalls' :
          exprTouchesUnsupportedCallSurface offset = false ∧
            exprTouchesUnsupportedCallSurface value = false := by
        simpa [stmtTouchesUnsupportedCallSurface, Bool.or_eq_false_iff] using hcalls
      constructor
      · exact exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed offset
          hcore'.1 hstate'.1 hcalls'.1
      · exact exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed value
          hcore'.2 hstate'.2 hcalls'.2
  | ite _ _ _ => cases hcore
  | forEach _ _ _ => cases hcore
  | _ =>
      all_goals (simp only [stmtTouchesUnsupportedContractSurface]; first | assumption | cases hcore | cases heffects | cases hcalls)

private theorem stmtTouchesUnsupportedContractSurfaceExceptMappingWrites_eq_false_of_featureClosed
    (stmt : Stmt)
    (hcore : stmtTouchesUnsupportedCoreSurface stmt = false)
    (hstate : stmtTouchesUnsupportedStateSurfaceExceptMappingWrites stmt = false)
    (hcalls : stmtTouchesUnsupportedCallSurface stmt = false)
    (heffects : stmtTouchesUnsupportedEffectSurface stmt = false) :
    stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt = false := by
  cases stmt with
  | setMapping _ key value | setMappingWord _ key _ value
  | setMappingPackedWord _ key _ _ value | setMappingUint _ key value
  | setStructMember _ key _ value =>
      simp [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites]
  | setMappingChain _ keys value =>
      simp [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites]
  | setMapping2 _ key1 key2 value | setMapping2Word _ key1 key2 _ value
  | setStructMember2 _ key1 key2 _ value =>
      simp [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites]
  | ite _ _ _ => cases hcore
  | forEach _ _ _ => cases hcore
  | _ =>
      simp only [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites]
      exact stmtTouchesUnsupportedContractSurface_eq_false_of_featureClosed _
        hcore
        (by simpa [stmtTouchesUnsupportedStateSurfaceExceptMappingWrites] using hstate)
        hcalls heffects


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
  | nil => simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites]
  | cons stmt rest ih =>
      rcases stmtListFeatureClosedExceptMappingWrites_cons_inv stmt rest hcore hstate hcalls heffects with
        ⟨hcoreStmt, hcoreRest, hstateStmt, hstateRest,
          hcallsStmt, hcallsRest, heffectsStmt, heffectsRest⟩
      have hstmt :=
        stmtTouchesUnsupportedContractSurfaceExceptMappingWrites_eq_false_of_featureClosed stmt
          hcoreStmt hstateStmt hcallsStmt heffectsStmt
      have hrest := ih hcoreRest hstateRest hcallsRest heffectsRest
      simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites, hstmt, hrest]


theorem exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed
    {expr : Expr}
    (hsurface : exprTouchesUnsupportedContractSurface expr = false) :
    exprTouchesUnsupportedHelperSurface expr = false := by
  cases expr with
  | literal _ | param _ | localVar _ | caller | contractAddress
  | chainid | msgValue | blockTimestamp | blockNumber =>
      simp [exprTouchesUnsupportedHelperSurface]
  | storage _ | storageAddr _ | internalCall _ _ | externalCall _ _
  | constructorArg _ | blobbasefee | mload _ | tload _ | keccak256 _ _
  | calldatasize | calldataload _ | returndataSize | extcodesize _
  | returndataOptionalBoolAt _ | arrayLength _ | storageArrayLength _
  | dynamicBytesEq _ _
  | call _ _ _ _ _ _ _ | staticcall _ _ _ _ _ _ | delegatecall _ _ _ _ _ _
  | mapping _ _ | mappingWord _ _ _ | mappingPackedWord _ _ _ _
  | mapping2 _ _ _ | mapping2Word _ _ _ _ | mappingUint _ _
  | structMember _ _ _ | structMember2 _ _ _ _
  | arrayElement _ _ | storageArrayElement _ _
  | mappingChain _ _ =>
      simp [exprTouchesUnsupportedContractSurface] at hsurface
  | add a b | sub a b | mul a b | div a b | mod a b
  | eq a b | ge a b | gt a b | lt a b | le a b
  | logicalAnd a b | logicalOr a b =>
      simp only [exprTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      simp [exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.1,
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.2]
  | sdiv a b | smod a b | bitAnd a b | bitOr a b
  | bitXor a b | sgt a b | slt a b
  | min a b | max a b | wMulDown a b | wDivUp a b | ceilDiv a b =>
      simp only [exprTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      simp [exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.1,
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.2]
  | shl a b | shr a b | sar a b | signextend a b =>
      simp [exprTouchesUnsupportedContractSurface] at hsurface
  | mulDivDown a b c | mulDivUp a b c =>
      simp [exprTouchesUnsupportedContractSurface] at hsurface
  | bitNot a =>
      simp only [exprTouchesUnsupportedContractSurface] at hsurface
      simp [exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface]
  | logicalNot a =>
      simp only [exprTouchesUnsupportedContractSurface] at hsurface
      simp [exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface]
  | ite cond thenVal elseVal =>
      simp only [exprTouchesUnsupportedContractSurface, Bool.or_eq_false_iff, Bool.or_assoc] at hsurface
      simp [exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.1,
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.2.1,
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.2.2]
termination_by sizeOf expr
decreasing_by all_goals (subst_vars; simp_wf; try omega)

private theorem exprListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed
    {exprs : List Expr}
    (hsurface : exprs.any exprTouchesUnsupportedContractSurface = false) :
    exprListTouchesUnsupportedHelperSurface exprs = false := by
  induction exprs with
  | nil =>
      simp [exprListTouchesUnsupportedHelperSurface]
  | cons expr rest ih =>
      simp only [List.any_cons, Bool.or_eq_false_iff] at hsurface
      simp [exprListTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.1,
        ih hsurface.2]

theorem stmtTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedContractSurface stmt = false) :
    stmtTouchesUnsupportedHelperSurface stmt = false := by
  cases stmt with
  | letVar _ value | assignVar _ value | setStorage _ value | setStorageAddr _ value
  | storageArrayPush _ value | require value _ | «return» value =>
      simp [stmtTouchesUnsupportedHelperSurface, stmtTouchesUnsupportedContractSurface] at hsurface ⊢
      all_goals exact exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface
  | mstore offset value | tstore offset value =>
      simp only [stmtTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface ⊢
      simp [exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.1,
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.2]
  | stop =>
      simp [stmtTouchesUnsupportedHelperSurface]
  | ite _ _ _ | setMapping _ _ _ | setMappingWord _ _ _ _
  | setMappingPackedWord _ _ _ _ _ | setMapping2 _ _ _ _
  | setMapping2Word _ _ _ _ _ | setMappingUint _ _ _
  | setMappingChain _ _ _ | setStructMember _ _ _ _ | setStructMember2 _ _ _ _ _
  | storageArrayPop _ | setStorageArrayElement _ _ _ | requireError _ _ _
  | revertError _ _ | returnValues _ | returnArray _ | returnBytes _
  | returnStorageWords _ | calldatacopy _ _ _ | returndataCopy _ _ _
  | revertReturndata | forEach _ _ _ | emit _ _ | internalCall _ _
  | internalCallAssign _ _ _ | rawLog _ _ _ | externalCallBind _ _ _ | ecm _ _ =>
      cases hsurface

theorem stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  induction stmts with
  | nil => simp [stmtListTouchesUnsupportedHelperSurface]
  | cons stmt rest ih =>
      simp only [stmtListTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.1,
        ih hsurface.2]

theorem stmtTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    (hsupported : SupportedStmtList fields scope [stmt]) :
    stmtTouchesUnsupportedHelperSurface stmt = false := by
  have hlist : stmtListTouchesUnsupportedHelperSurface [stmt] = false := by
    simpa using hsupported.helperSurfaceClosed
  simp [stmtListTouchesUnsupportedHelperSurface] at hlist
  exact hlist

theorem stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsupported : SupportedStmtList fields scope stmts) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  simpa using hsupported.helperSurfaceClosed


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
  cases expr with
  | literal _ | param _ | localVar _ | caller | contractAddress
  | chainid | msgValue | blockTimestamp | blockNumber =>
      simp [exprUsesArrayElement]
  | add a b | sub a b | mul a b | div a b | mod a b
  | eq a b | ge a b | gt a b | lt a b | le a b
  | logicalAnd a b | logicalOr a b =>
      simp only [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff] at hcore
      simp [exprUsesArrayElement,
        exprUsesArrayElement_eq_false_of_coreClosed hcore.1,
        exprUsesArrayElement_eq_false_of_coreClosed hcore.2]
  | logicalNot a =>
      simp only [exprTouchesUnsupportedCoreSurface] at hcore
      simp [exprUsesArrayElement, exprUsesArrayElement_eq_false_of_coreClosed hcore]
  | ite cond thenVal elseVal =>
      simp only [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff, Bool.or_assoc] at hcore
      simp [exprUsesArrayElement,
        exprUsesArrayElement_eq_false_of_coreClosed hcore.1,
        exprUsesArrayElement_eq_false_of_coreClosed hcore.2.1,
        exprUsesArrayElement_eq_false_of_coreClosed hcore.2.2]
  | storage _ | storageAddr _ => simp [exprUsesArrayElement]
  | _ => simp [exprTouchesUnsupportedCoreSurface] at hcore
termination_by sizeOf expr
decreasing_by all_goals (subst_vars; simp_wf; try omega)

private theorem exprUsesStorageArrayElement_eq_false_of_coreClosed
    {expr : Expr}
    (hcore : exprTouchesUnsupportedCoreSurface expr = false) :
    exprUsesStorageArrayElement expr = false := by
  cases expr with
  | literal _ | param _ | localVar _ | caller | contractAddress
  | chainid | msgValue | blockTimestamp | blockNumber =>
      simp [exprUsesStorageArrayElement]
  | add a b | sub a b | mul a b | div a b | mod a b
  | eq a b | ge a b | gt a b | lt a b | le a b
  | logicalAnd a b | logicalOr a b =>
      simp only [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff] at hcore
      simp [exprUsesStorageArrayElement,
        exprUsesStorageArrayElement_eq_false_of_coreClosed hcore.1,
        exprUsesStorageArrayElement_eq_false_of_coreClosed hcore.2]
  | logicalNot a =>
      simp only [exprTouchesUnsupportedCoreSurface] at hcore
      simp [exprUsesStorageArrayElement, exprUsesStorageArrayElement_eq_false_of_coreClosed hcore]
  | ite cond thenVal elseVal =>
      simp only [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff, Bool.or_assoc] at hcore
      simp [exprUsesStorageArrayElement,
        exprUsesStorageArrayElement_eq_false_of_coreClosed hcore.1,
        exprUsesStorageArrayElement_eq_false_of_coreClosed hcore.2.1,
        exprUsesStorageArrayElement_eq_false_of_coreClosed hcore.2.2]
  | storage _ | storageAddr _ | arrayElement _ _ => simp [exprUsesStorageArrayElement]
  | _ => simp [exprTouchesUnsupportedCoreSurface] at hcore
termination_by sizeOf expr
decreasing_by all_goals (subst_vars; simp_wf; try omega)

private theorem exprUsesDynamicBytesEq_eq_false_of_coreClosed
    {expr : Expr}
    (hcore : exprTouchesUnsupportedCoreSurface expr = false) :
    exprUsesDynamicBytesEq expr = false := by
  cases expr with
  | literal _ | param _ | localVar _ | caller | contractAddress
  | chainid | msgValue | blockTimestamp | blockNumber =>
      simp [exprUsesDynamicBytesEq]
  | add a b | sub a b | mul a b | div a b | mod a b
  | eq a b | ge a b | gt a b | lt a b | le a b
  | logicalAnd a b | logicalOr a b =>
      simp only [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff] at hcore
      simp [exprUsesDynamicBytesEq,
        exprUsesDynamicBytesEq_eq_false_of_coreClosed hcore.1,
        exprUsesDynamicBytesEq_eq_false_of_coreClosed hcore.2]
  | logicalNot a =>
      simp only [exprTouchesUnsupportedCoreSurface] at hcore
      simp [exprUsesDynamicBytesEq, exprUsesDynamicBytesEq_eq_false_of_coreClosed hcore]
  | ite cond thenVal elseVal =>
      simp only [exprTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff, Bool.or_assoc] at hcore
      simp [exprUsesDynamicBytesEq,
        exprUsesDynamicBytesEq_eq_false_of_coreClosed hcore.1,
        exprUsesDynamicBytesEq_eq_false_of_coreClosed hcore.2.1,
        exprUsesDynamicBytesEq_eq_false_of_coreClosed hcore.2.2]
  | storage _ | storageAddr _ => simp [exprUsesDynamicBytesEq]
  | _ => simp [exprTouchesUnsupportedCoreSurface] at hcore
termination_by sizeOf expr
decreasing_by all_goals (subst_vars; simp_wf; try omega)

-- Helper: ExprCompileCore expressions never use arrayElement
private theorem exprCompileCore_usesArrayElement_false
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    exprUsesArrayElement expr = false := by
  induction hcore with
  | literal | param | localVar | caller | contractAddress | msgValue
    | blockTimestamp | blockNumber | chainid =>
      simp only [exprUsesArrayElement, Bool.false_or]
  | add _ _ ihL ihR | sub _ _ ihL ihR | mul _ _ ihL ihR
    | div _ _ ihL ihR | mod _ _ ihL ihR | eq _ _ ihL ihR
    | lt _ _ ihL ihR | gt _ _ ihL ihR | ge _ _ ihL ihR
    | le _ _ ihL ihR | logicalAnd _ _ ihL ihR | logicalOr _ _ ihL ihR =>
      simp only [exprUsesArrayElement, ihL, ihR, Bool.false_or]
  | logicalNot _ ih =>
      simp only [exprUsesArrayElement, ih, Bool.false_or]

-- Helper: ExprCompileCore expressions never use storageArrayElement
private theorem exprCompileCore_usesStorageArrayElement_false
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    exprUsesStorageArrayElement expr = false := by
  induction hcore with
  | literal | param | localVar | caller | contractAddress | msgValue
    | blockTimestamp | blockNumber | chainid =>
      simp only [exprUsesStorageArrayElement, Bool.false_or]
  | add _ _ ihL ihR | sub _ _ ihL ihR | mul _ _ ihL ihR
    | div _ _ ihL ihR | mod _ _ ihL ihR | eq _ _ ihL ihR
    | lt _ _ ihL ihR | gt _ _ ihL ihR | ge _ _ ihL ihR
    | le _ _ ihL ihR | logicalAnd _ _ ihL ihR | logicalOr _ _ ihL ihR =>
      simp only [exprUsesStorageArrayElement, ihL, ihR, Bool.false_or]
  | logicalNot _ ih =>
      simp only [exprUsesStorageArrayElement, ih, Bool.false_or]

-- Helper: ExprCompileCore expressions never use dynamicBytesEq
private theorem exprCompileCore_usesDynamicBytesEq_false
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    exprUsesDynamicBytesEq expr = false := by
  induction hcore with
  | literal | param | localVar | caller | contractAddress | msgValue
    | blockTimestamp | blockNumber | chainid =>
      simp only [exprUsesDynamicBytesEq, Bool.false_or]
  | add _ _ ihL ihR | sub _ _ ihL ihR | mul _ _ ihL ihR
    | div _ _ ihL ihR | mod _ _ ihL ihR | eq _ _ ihL ihR
    | lt _ _ ihL ihR | gt _ _ ihL ihR | ge _ _ ihL ihR
    | le _ _ ihL ihR | logicalAnd _ _ ihL ihR | logicalOr _ _ ihL ihR =>
      simp only [exprUsesDynamicBytesEq, ihL, ihR, Bool.false_or]
  | logicalNot _ ih =>
      simp only [exprUsesDynamicBytesEq, ih, Bool.false_or]

-- Helper: ExprCompileCore lists never use arrayElement
private theorem exprListCompileCore_usesArrayElement_false
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    exprListUsesArrayElement exprs = false := by
  induction exprs with
  | nil => simp only [exprListUsesArrayElement, Bool.false_or]
  | cons e rest ih =>
      simp only [exprListUsesArrayElement,
        exprCompileCore_usesArrayElement_false (hcore e (List.mem_cons_self ..)),
        ih (fun e he => hcore e (List.mem_cons_of_mem _ he)), Bool.false_or]

-- Helper: ExprCompileCore lists never use storageArrayElement
private theorem exprListCompileCore_usesStorageArrayElement_false
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    exprListUsesStorageArrayElement exprs = false := by
  induction exprs with
  | nil => simp only [exprListUsesStorageArrayElement, Bool.false_or]
  | cons e rest ih =>
      simp only [exprListUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false (hcore e (List.mem_cons_self ..)),
        ih (fun e he => hcore e (List.mem_cons_of_mem _ he)), Bool.false_or]

-- Helper: ExprCompileCore lists never use dynamicBytesEq
private theorem exprListCompileCore_usesDynamicBytesEq_false
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    exprListUsesDynamicBytesEq exprs = false := by
  induction exprs with
  | nil => simp only [exprListUsesDynamicBytesEq, Bool.false_or]
  | cons e rest ih =>
      simp only [exprListUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false (hcore e (List.mem_cons_self ..)),
        ih (fun e he => hcore e (List.mem_cons_of_mem _ he)), Bool.false_or]

-- Helper: StmtListCompileCore never uses arrayElement
private theorem stmtListCompileCore_usesArrayElement_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    stmtListUsesArrayElement stmts = false := by
  induction hcore with
  | nil => simp only [stmtListUsesArrayElement, Bool.false_or]
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]; assumption
  | stop _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement, Bool.false_or]; assumption

-- Helper: StmtListTerminalCore never uses arrayElement
private theorem stmtListTerminalCore_usesArrayElement_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListTerminalCore scope stmts) :
    stmtListUsesArrayElement stmts = false := by
  induction hcore with
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hvalue,
        stmtListCompileCore_usesArrayElement_false ih, Bool.false_or]
  | stop ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        stmtListCompileCore_usesArrayElement_false ih, Bool.false_or]
  | ite hcond _ _ _ hCompile ih_then ih_else =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hcond, ih_then, ih_else,
        stmtListCompileCore_usesArrayElement_false hCompile, Bool.false_or]

-- Helper: StmtListCompileCore never uses storageArrayElement
private theorem stmtListCompileCore_usesStorageArrayElement_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    stmtListUsesStorageArrayElement stmts = false := by
  induction hcore with
  | nil => simp only [stmtListUsesStorageArrayElement, Bool.false_or]
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]; assumption
  | stop _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement, Bool.false_or]; assumption

-- Helper: StmtListTerminalCore never uses storageArrayElement
private theorem stmtListTerminalCore_usesStorageArrayElement_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListTerminalCore scope stmts) :
    stmtListUsesStorageArrayElement stmts = false := by
  induction hcore with
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hvalue,
        stmtListCompileCore_usesStorageArrayElement_false ih, Bool.false_or]
  | stop ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        stmtListCompileCore_usesStorageArrayElement_false ih, Bool.false_or]
  | ite hcond _ _ _ hCompile ih_then ih_else =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hcond, ih_then, ih_else,
        stmtListCompileCore_usesStorageArrayElement_false hCompile, Bool.false_or]

-- Helper: StmtListCompileCore never uses dynamicBytesEq
private theorem stmtListCompileCore_usesDynamicBytesEq_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    stmtListUsesDynamicBytesEq stmts = false := by
  induction hcore with
  | nil => simp only [stmtListUsesDynamicBytesEq, Bool.false_or]
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]; assumption
  | stop _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq, Bool.false_or]; assumption

-- Helper: StmtListTerminalCore never uses dynamicBytesEq
private theorem stmtListTerminalCore_usesDynamicBytesEq_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListTerminalCore scope stmts) :
    stmtListUsesDynamicBytesEq stmts = false := by
  induction hcore with
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hvalue,
        stmtListCompileCore_usesDynamicBytesEq_false ih, Bool.false_or]
  | stop ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        stmtListCompileCore_usesDynamicBytesEq_false ih, Bool.false_or]
  | ite hcond _ _ _ hCompile ih_then ih_else =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hcond, ih_then, ih_else,
        stmtListCompileCore_usesDynamicBytesEq_false hCompile, Bool.false_or]

-- Helper for append: stmtListUsesArrayElement distributes over append
private theorem stmtListUsesArrayElement_append (xs ys : List Stmt) :
    stmtListUsesArrayElement (xs ++ ys) =
      (stmtListUsesArrayElement xs || stmtListUsesArrayElement ys) := by
  induction xs with
  | nil => simp only [List.nil_append, stmtListUsesArrayElement, Bool.false_or]
  | cons x xs' ih =>
      simp only [List.cons_append, stmtListUsesArrayElement, Bool.false_or]
      rw [ih, Bool.or_assoc]

private theorem stmtListUsesStorageArrayElement_append (xs ys : List Stmt) :
    stmtListUsesStorageArrayElement (xs ++ ys) =
      (stmtListUsesStorageArrayElement xs || stmtListUsesStorageArrayElement ys) := by
  induction xs with
  | nil => simp only [List.nil_append, stmtListUsesStorageArrayElement, Bool.false_or]
  | cons x xs' ih =>
      simp only [List.cons_append, stmtListUsesStorageArrayElement, Bool.false_or]
      rw [ih, Bool.or_assoc]

private theorem stmtListUsesDynamicBytesEq_append (xs ys : List Stmt) :
    stmtListUsesDynamicBytesEq (xs ++ ys) =
      (stmtListUsesDynamicBytesEq xs || stmtListUsesDynamicBytesEq ys) := by
  induction xs with
  | nil => simp only [List.nil_append, stmtListUsesDynamicBytesEq, Bool.false_or]
  | cons x xs' ih =>
      simp only [List.cons_append, stmtListUsesDynamicBytesEq, Bool.false_or]
      rw [ih, Bool.or_assoc]

-- SupportedStmtList never uses arrayElement
open Verity.Core.Free in
private theorem supportedStmtList_usesArrayElement_false
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (h : SupportedStmtList fields scope stmts) :
    stmtListUsesArrayElement stmts = false := by
  induction h with
  | compileCore hcore => exact stmtListCompileCore_usesArrayElement_false hcore
  | terminalCore hterminal => exact stmtListTerminalCore_usesArrayElement_false hterminal
  | setStorageSingleSlot hvalue _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]
  | setStorageAddrSingleSlot hvalue _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]
  | mstoreSingle hoffset _ hvalue _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hoffset,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]
  | tstoreSingle hoffset _ hvalue _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hoffset,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]
  | letStorageField _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement, exprUsesArrayElement, Bool.false_or]
  | returnMapping hkey _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement, exprUsesArrayElement,
        exprCompileCore_usesArrayElement_false hkey, Bool.false_or]
  | letMapping hkey _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement, exprUsesArrayElement,
        exprCompileCore_usesArrayElement_false hkey, Bool.false_or]
  | letMapping2 hkey1 _ hkey2 _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement, exprUsesArrayElement,
        exprCompileCore_usesArrayElement_false hkey1,
        exprCompileCore_usesArrayElement_false hkey2, Bool.false_or]
  | letMappingUint hkey _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement, exprUsesArrayElement,
        exprCompileCore_usesArrayElement_false hkey, Bool.false_or]
  | setMappingUintSingle hkey _ hvalue _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hkey,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]
  | setMappingChainSingle hkeys _ hvalue _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprListCompileCore_usesArrayElement_false hkeys,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]
  | setMappingSingle hkey _ hvalue _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hkey,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]
  | setMappingWordSingle hkey _ hvalue _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hkey,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]
  | setMappingPackedWordSingle hkey _ hvalue _ _ _ _ _ _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hkey,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]
  | setStructMemberSingle hkey _ hvalue _ _ _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hkey,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]
  | setMapping2Single hkey1 _ hkey2 _ hvalue _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hkey1,
        exprCompileCore_usesArrayElement_false hkey2,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]
  | setMapping2WordSingle hkey1 _ hkey2 _ hvalue _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hkey1,
        exprCompileCore_usesArrayElement_false hkey2,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]
  | setStructMember2Single hkey1 _ hkey2 _ hvalue _ _ _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hkey1,
        exprCompileCore_usesArrayElement_false hkey2,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]
  | rawLogLiterals _ =>
      have hliterals : ∀ (ns : List Nat),
          exprListUsesArrayElement (ns.map Expr.literal) = false := by
        intro ns; induction ns with
        | nil => simp only [List.map_nil, exprListUsesArrayElement, Bool.false_or]
        | cons _ _ ih => simp only [List.map_cons, exprListUsesArrayElement, exprUsesArrayElement, ih, Bool.false_or]
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprUsesArrayElement, hliterals, Bool.false_or]
  | letCallerLetStorageReqEqReqNeqSetStorageParamStop _ _ _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprUsesArrayElement, exprListUsesArrayElement, Bool.false_or]
  | letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop _ _ _ _ _ _ =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprUsesArrayElement, exprListUsesArrayElement, Bool.false_or]
  | requireClause clause _ ih =>
      simp only [stmtListUsesArrayElement, Bool.or_eq_false_iff, Bool.false_or]
      exact ⟨by cases clause with | mk family n m p q message =>
          cases family with
          | binary op =>
              cases op <;> simp only [RequireLiteralGuardFamilyClause.toStmt,
                stmtUsesArrayElement, exprUsesArrayElement, Bool.false_or]
          | andEqLt =>
              simp only [RequireLiteralGuardFamilyClause.toStmt,
                stmtUsesArrayElement, exprUsesArrayElement, Bool.false_or]
          | orEqLt =>
              simp only [RequireLiteralGuardFamilyClause.toStmt,
                stmtUsesArrayElement, exprUsesArrayElement, Bool.false_or], ih⟩
  | ite hcond _ _ _ ihThen ihElse =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hcond, ihThen, ihElse, Bool.false_or]
  | @append _ _ pfx sfx _ _ ihPfx ihSfx =>
      rw [stmtListUsesArrayElement_append, ihPfx, ihSfx]
      simp

-- SupportedStmtList never uses storageArrayElement
open Verity.Core.Free in
private theorem supportedStmtList_usesStorageArrayElement_false
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (h : SupportedStmtList fields scope stmts) :
    stmtListUsesStorageArrayElement stmts = false := by
  induction h with
  | compileCore hcore => exact stmtListCompileCore_usesStorageArrayElement_false hcore
  | terminalCore hterminal => exact stmtListTerminalCore_usesStorageArrayElement_false hterminal
  | setStorageSingleSlot hvalue _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]
  | setStorageAddrSingleSlot hvalue _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]
  | mstoreSingle hoffset _ hvalue _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hoffset,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]
  | tstoreSingle hoffset _ hvalue _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hoffset,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]
  | letStorageField _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprUsesStorageArrayElement, Bool.false_or]
  | returnMapping hkey _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprUsesStorageArrayElement, exprCompileCore_usesStorageArrayElement_false hkey, Bool.false_or]
  | letMapping hkey _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprUsesStorageArrayElement, exprCompileCore_usesStorageArrayElement_false hkey, Bool.false_or]
  | letMapping2 hkey1 _ hkey2 _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hkey1,
        exprCompileCore_usesStorageArrayElement_false hkey2, Bool.false_or]
  | letMappingUint hkey _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprUsesStorageArrayElement, exprCompileCore_usesStorageArrayElement_false hkey, Bool.false_or]
  | setMappingUintSingle hkey _ hvalue _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hkey,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]
  | setMappingChainSingle hkeys _ hvalue _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprListCompileCore_usesStorageArrayElement_false hkeys,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]
  | setMappingSingle hkey _ hvalue _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hkey,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]
  | setMappingWordSingle hkey _ hvalue _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hkey,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]
  | setMappingPackedWordSingle hkey _ hvalue _ _ _ _ _ _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hkey,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]
  | setStructMemberSingle hkey _ hvalue _ _ _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hkey,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]
  | setMapping2Single hkey1 _ hkey2 _ hvalue _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hkey1,
        exprCompileCore_usesStorageArrayElement_false hkey2,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]
  | setMapping2WordSingle hkey1 _ hkey2 _ hvalue _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hkey1,
        exprCompileCore_usesStorageArrayElement_false hkey2,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]
  | setStructMember2Single hkey1 _ hkey2 _ hvalue _ _ _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hkey1,
        exprCompileCore_usesStorageArrayElement_false hkey2,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]
  | rawLogLiterals _ =>
      have hliterals : ∀ (ns : List Nat),
          exprListUsesStorageArrayElement (ns.map Expr.literal) = false := by
        intro ns; induction ns with
        | nil => simp only [List.map_nil, exprListUsesStorageArrayElement, Bool.false_or]
        | cons _ _ ih =>
          simp only [List.map_cons, exprListUsesStorageArrayElement, exprUsesStorageArrayElement, ih, Bool.false_or]
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprUsesStorageArrayElement, hliterals, Bool.false_or]
  | letCallerLetStorageReqEqReqNeqSetStorageParamStop _ _ _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprUsesStorageArrayElement, exprListUsesStorageArrayElement, Bool.false_or]
  | letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop _ _ _ _ _ _ =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprUsesStorageArrayElement, exprListUsesStorageArrayElement, Bool.false_or]
  | requireClause clause _ ih =>
      simp only [stmtListUsesStorageArrayElement, Bool.or_eq_false_iff, Bool.false_or]
      exact ⟨by cases clause with | mk family n m p q message =>
          cases family with
          | binary op =>
              cases op <;> simp only [RequireLiteralGuardFamilyClause.toStmt,
                stmtUsesStorageArrayElement, exprUsesStorageArrayElement, Bool.false_or]
          | andEqLt =>
              simp only [RequireLiteralGuardFamilyClause.toStmt,
                stmtUsesStorageArrayElement, exprUsesStorageArrayElement, Bool.false_or]
          | orEqLt =>
              simp only [RequireLiteralGuardFamilyClause.toStmt,
                stmtUsesStorageArrayElement, exprUsesStorageArrayElement, Bool.false_or], ih⟩
  | ite hcond _ _ _ ihThen ihElse =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hcond, ihThen, ihElse, Bool.false_or]
  | @append _ _ pfx sfx _ _ ihPfx ihSfx =>
      rw [stmtListUsesStorageArrayElement_append, ihPfx, ihSfx]
      simp

-- SupportedStmtList never uses dynamicBytesEq
open Verity.Core.Free in
private theorem supportedStmtList_usesDynamicBytesEq_false
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (h : SupportedStmtList fields scope stmts) :
    stmtListUsesDynamicBytesEq stmts = false := by
  induction h with
  | compileCore hcore => exact stmtListCompileCore_usesDynamicBytesEq_false hcore
  | terminalCore hterminal => exact stmtListTerminalCore_usesDynamicBytesEq_false hterminal
  | setStorageSingleSlot hvalue _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]
  | setStorageAddrSingleSlot hvalue _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]
  | mstoreSingle hoffset _ hvalue _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hoffset,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]
  | tstoreSingle hoffset _ hvalue _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hoffset,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]
  | letStorageField _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq, exprUsesDynamicBytesEq, Bool.false_or]
  | returnMapping hkey _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprUsesDynamicBytesEq, exprCompileCore_usesDynamicBytesEq_false hkey, Bool.false_or]
  | letMapping hkey _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprUsesDynamicBytesEq, exprCompileCore_usesDynamicBytesEq_false hkey, Bool.false_or]
  | letMapping2 hkey1 _ hkey2 _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hkey1,
        exprCompileCore_usesDynamicBytesEq_false hkey2, Bool.false_or]
  | letMappingUint hkey _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprUsesDynamicBytesEq, exprCompileCore_usesDynamicBytesEq_false hkey, Bool.false_or]
  | setMappingUintSingle hkey _ hvalue _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hkey,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]
  | setMappingChainSingle hkeys _ hvalue _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprListCompileCore_usesDynamicBytesEq_false hkeys,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]
  | setMappingSingle hkey _ hvalue _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hkey,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]
  | setMappingWordSingle hkey _ hvalue _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hkey,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]
  | setMappingPackedWordSingle hkey _ hvalue _ _ _ _ _ _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hkey,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]
  | setStructMemberSingle hkey _ hvalue _ _ _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hkey,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]
  | setMapping2Single hkey1 _ hkey2 _ hvalue _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hkey1,
        exprCompileCore_usesDynamicBytesEq_false hkey2,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]
  | setMapping2WordSingle hkey1 _ hkey2 _ hvalue _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hkey1,
        exprCompileCore_usesDynamicBytesEq_false hkey2,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]
  | setStructMember2Single hkey1 _ hkey2 _ hvalue _ _ _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hkey1,
        exprCompileCore_usesDynamicBytesEq_false hkey2,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]
  | rawLogLiterals _ =>
      have hliterals : ∀ (ns : List Nat),
          exprListUsesDynamicBytesEq (ns.map Expr.literal) = false := by
        intro ns; induction ns with
        | nil => simp only [List.map_nil, exprListUsesDynamicBytesEq, Bool.false_or]
        | cons _ _ ih =>
          simp only [List.map_cons, exprListUsesDynamicBytesEq, exprUsesDynamicBytesEq, ih, Bool.false_or]
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprUsesDynamicBytesEq, hliterals, Bool.false_or]
  | letCallerLetStorageReqEqReqNeqSetStorageParamStop _ _ _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprUsesDynamicBytesEq, exprListUsesDynamicBytesEq, Bool.false_or]
  | letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop _ _ _ _ _ _ =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprUsesDynamicBytesEq, exprListUsesDynamicBytesEq, Bool.false_or]
  | requireClause clause _ ih =>
      simp only [stmtListUsesDynamicBytesEq, Bool.or_eq_false_iff, Bool.false_or]
      exact ⟨by cases clause with | mk family n m p q message =>
          cases family with
          | binary op =>
              cases op <;> simp only [RequireLiteralGuardFamilyClause.toStmt,
                stmtUsesDynamicBytesEq, exprUsesDynamicBytesEq, Bool.false_or]
          | andEqLt =>
              simp only [RequireLiteralGuardFamilyClause.toStmt,
                stmtUsesDynamicBytesEq, exprUsesDynamicBytesEq, Bool.false_or]
          | orEqLt =>
              simp only [RequireLiteralGuardFamilyClause.toStmt,
                stmtUsesDynamicBytesEq, exprUsesDynamicBytesEq, Bool.false_or], ih⟩
  | ite hcond _ _ _ ihThen ihElse =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hcond, ihThen, ihElse, Bool.false_or]
  | @append _ _ pfx sfx _ _ ihPfx ihSfx =>
      rw [stmtListUsesDynamicBytesEq_append, ihPfx, ihSfx]
      simp

-- Bridge: stmtListUsesArrayElement is equivalent to List.any
private theorem stmtListUsesArrayElement_eq_any (stmts : List Stmt) :
    stmtListUsesArrayElement stmts = stmts.any stmtUsesArrayElement := by
  induction stmts with
  | nil => simp [stmtListUsesArrayElement, List.any]
  | cons s ss ih => simp [stmtListUsesArrayElement, List.any_cons, ih]

private theorem stmtListUsesStorageArrayElement_eq_any (stmts : List Stmt) :
    stmtListUsesStorageArrayElement stmts = stmts.any stmtUsesStorageArrayElement := by
  induction stmts with
  | nil => simp [stmtListUsesStorageArrayElement, List.any]
  | cons s ss ih => simp [stmtListUsesStorageArrayElement, List.any_cons, ih]

private theorem stmtListUsesDynamicBytesEq_eq_any (stmts : List Stmt) :
    stmtListUsesDynamicBytesEq stmts = stmts.any stmtUsesDynamicBytesEq := by
  induction stmts with
  | nil => simp [stmtListUsesDynamicBytesEq, List.any]
  | cons s ss ih => simp [stmtListUsesDynamicBytesEq, List.any_cons, ih]

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

theorem SupportedSpec.contractUsesArrayElement_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    contractUsesArrayElement spec = false := by
  simp [contractUsesArrayElement, hSupported.surface.noConstructor, constructorUsesArrayElement]
  intro fn hmem
  simp only [functionUsesArrayElement]
  rw [← stmtListUsesArrayElement_eq_any]
  exact supportedStmtList_usesArrayElement_false (hSupported.functions fn hmem).body.stmtList

theorem SupportedSpecExceptMappingWrites.contractUsesArrayElement_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    contractUsesArrayElement spec = false := by
  simp [contractUsesArrayElement, hSupported.surface.noConstructor, constructorUsesArrayElement]
  intro fn hmem
  simp only [functionUsesArrayElement]
  rw [← stmtListUsesArrayElement_eq_any]
  exact supportedStmtList_usesArrayElement_false (hSupported.functions fn hmem).body.stmtList

theorem SupportedSpec.contractUsesStorageArrayElement_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    contractUsesStorageArrayElement spec = false := by
  simp [contractUsesStorageArrayElement, hSupported.surface.noConstructor,
    constructorUsesStorageArrayElement]
  intro fn hmem
  simp only [functionUsesStorageArrayElement]
  rw [← stmtListUsesStorageArrayElement_eq_any]
  exact supportedStmtList_usesStorageArrayElement_false
    (hSupported.functions fn hmem).body.stmtList

theorem SupportedSpecExceptMappingWrites.contractUsesStorageArrayElement_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    contractUsesStorageArrayElement spec = false := by
  simp [contractUsesStorageArrayElement, hSupported.surface.noConstructor,
    constructorUsesStorageArrayElement]
  intro fn hmem
  simp only [functionUsesStorageArrayElement]
  rw [← stmtListUsesStorageArrayElement_eq_any]
  exact supportedStmtList_usesStorageArrayElement_false
    (hSupported.functions fn hmem).body.stmtList

theorem SupportedSpec.contractUsesDynamicBytesEq_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    contractUsesDynamicBytesEq spec = false := by
  simp [contractUsesDynamicBytesEq, hSupported.surface.noConstructor]
  intro fn hmem
  have := supportedStmtList_usesDynamicBytesEq_false
    (hSupported.functions fn hmem).body.stmtList
  rw [stmtListUsesDynamicBytesEq_eq_any] at this
  simp at this
  exact this

theorem SupportedSpecExceptMappingWrites.contractUsesDynamicBytesEq_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    contractUsesDynamicBytesEq spec = false := by
  simp [contractUsesDynamicBytesEq, hSupported.surface.noConstructor]
  intro fn hmem
  have := supportedStmtList_usesDynamicBytesEq_false
    (hSupported.functions fn hmem).body.stmtList
  rw [stmtListUsesDynamicBytesEq_eq_any] at this
  simp at this
  exact this


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

theorem SupportedSpec.noConstructor
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    spec.constructor = none :=
  hSupported.surface.noConstructor

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
    SupportedFunction spec fn :=
  hSupported.functions fn ((List.mem_filter.mp hfn).1)

def SupportedSpecExceptMappingWrites.supportedFunctionOfSelectorDispatched
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    SupportedFunctionExceptMappingWrites spec fn :=
  hSupported.functions fn ((List.mem_filter.mp hfn).1)

noncomputable def SupportedSpec.helperFuelOfFunction
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (fn : FunctionSpec) : Nat :=
  open Classical in
  if hfn : fn ∈ selectorDispatchedFunctions spec then
    (hSupported.supportedFunctionOfSelectorDispatched hfn).helperFuel
  else
    0

noncomputable def SupportedSpecExceptMappingWrites.helperFuelOfFunction
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (fn : FunctionSpec) : Nat :=
  open Classical in
  if hfn : fn ∈ selectorDispatchedFunctions spec then
    (hSupported.supportedFunctionOfSelectorDispatched hfn).helperFuel
  else
    0


noncomputable def SupportedSpec.helperFuel
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) : Nat :=
  (selectorDispatchedFunctions spec).foldl
    (fun fuel fn => max fuel (hSupported.helperFuelOfFunction fn))
    0

noncomputable def SupportedSpecExceptMappingWrites.helperFuel
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
  (hSupported.supportedFunctionOfSelectorDispatched hfn).params.supported

theorem SupportedSpecExceptMappingWrites.selectorFunctionParamsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).params.supported

theorem SupportedSpec.selectorFunctionParamNamesNodup
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    (fn.params.map (·.name)).Nodup :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).params.namesNodup

theorem SupportedSpecExceptMappingWrites.selectorFunctionParamNamesNodup
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    (fn.params.map (·.name)).Nodup :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).params.namesNodup

theorem SupportedSpec.selectorFunctionReturnsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).returns.resolved

theorem SupportedSpecExceptMappingWrites.selectorFunctionReturnsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).returns.resolved


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

private def counter_supported_function :
    ∀ fn, fn ∈ counterSupportedSpecModel.functions →
      SupportedFunction counterSupportedSpecModel fn := by
  intro fn hfn
  simp [counterSupportedSpecModel] at hfn
  rcases hfn with rfl
  exact
    { nonInternal := rfl
      nonSpecialEntrypoint := rfl
      params :=
        { namesNodup := by decide
          supported := by intro param hparam; cases hparam }
      returns := { resolved := ⟨[.uint256], rfl, trivial⟩ }
      body :=
        { stmtList := .terminalCore (.return_ (.literal 42) (by simp [FunctionBody.exprBoundNamesInScope, FunctionBody.exprBoundNames]) .nil)
          core := { surfaceClosed := by decide }
          state := { surfaceClosed := by decide }
          calls :=
            { helpers :=
                { helperRank := 0
                  callNamesNodup := helperCallNames_nodup _
                  summaryOf := by
                    intro calleeName hmem
                    simp [helperCallNames, stmtListInternalHelperCallNames, stmtInternalHelperCallNames, exprInternalHelperCallNames] at hmem
                  calleeRanksDecrease := by
                    intro calleeName hmem
                    simp [helperCallNames, stmtListInternalHelperCallNames, stmtInternalHelperCallNames, exprInternalHelperCallNames] at hmem
                  exprCallsPreserveWorld := by
                    intro calleeName hmem
                    simp [exprHelperCallNames, stmtListExprHelperCallNames, stmtExprHelperCallNames, exprInternalHelperCallNames] at hmem }
              foreign := by decide
              lowLevel := by decide }
          effects := { surfaceClosed := by decide }
          noLocalObligations := rfl } }

def counter_supported_spec : SupportedSpec counterSupportedSpecModel
    [0xa87d942c] :=
  { invariants :=
      { normalizedFields := rfl
        noPackedFields := counter_noPackedFields
        selectorCount := by decide
        selectorsDistinct := by decide
        functionNamesNodup := by decide }
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

private def simpleStorage_supported_function :
    ∀ fn, fn ∈ simpleStorageSupportedSpecModel.functions →
      SupportedFunction simpleStorageSupportedSpecModel fn := by
  intro fn hfn
  simp [simpleStorageSupportedSpecModel] at hfn
  rcases hfn with rfl
  exact
    { nonInternal := rfl
      nonSpecialEntrypoint := rfl
      params :=
        { namesNodup := by decide
          supported := by intro param hparam; cases hparam }
      returns := { resolved := ⟨[.uint256], rfl, trivial⟩ }
      body :=
        { stmtList := .terminalCore (.return_ (.literal 11) (by simp [FunctionBody.exprBoundNamesInScope, FunctionBody.exprBoundNames]) .nil)
          core := { surfaceClosed := by decide }
          state := { surfaceClosed := by decide }
          calls :=
            { helpers :=
                { helperRank := 0
                  callNamesNodup := helperCallNames_nodup _
                  summaryOf := by
                    intro calleeName hmem
                    simp [helperCallNames, stmtListInternalHelperCallNames, stmtInternalHelperCallNames, exprInternalHelperCallNames] at hmem
                  calleeRanksDecrease := by
                    intro calleeName hmem
                    simp [helperCallNames, stmtListInternalHelperCallNames, stmtInternalHelperCallNames, exprInternalHelperCallNames] at hmem
                  exprCallsPreserveWorld := by
                    intro calleeName hmem
                    simp [exprHelperCallNames, stmtListExprHelperCallNames, stmtExprHelperCallNames, exprInternalHelperCallNames] at hmem }
              foreign := by decide
              lowLevel := by decide }
          effects := { surfaceClosed := by decide }
          noLocalObligations := rfl } }

def simpleStorage_supported_spec : SupportedSpec simpleStorageSupportedSpecModel
    [0x2e64cec1] :=
  { invariants :=
      { normalizedFields := rfl
        noPackedFields := simpleStorage_noPackedFields
        selectorCount := by decide
        selectorsDistinct := by decide
        functionNamesNodup := by decide }
    surface :=
      { noConstructor := rfl
        noEvents := rfl
        noErrors := rfl
        noExternals := rfl
        noFallback := simpleStorage_noFallback
        noReceive := simpleStorage_noReceive }
    functions := simpleStorage_supported_function }


end Compiler.Proofs.IRGeneration
