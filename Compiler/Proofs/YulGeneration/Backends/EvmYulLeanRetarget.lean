/-
  Phase 4: Retarget the theorem stack to EVMYulLean.

  This module proves that the legacy Verity builtin backend and the
  `.evmYulLean` builtin backend are equivalent for programs that use only
  bridged builtins.

  **Key theorem**: `backends_agree_on_bridged_builtins` shows that
  `evalBuiltinCallWithBackendContext .verity ... func args =
   evalBuiltinCallWithBackendContext .evmYulLean ... func args`
  for every `func ∈ bridgedBuiltins`.

  This module also proves the expression-level lift for `BridgedExpr`:
  `evalYulExpr_evmYulLean_eq_on_bridged`, plus the recursive target lift
  `execYulFuelWithBackend_eq_on_bridged_target` for `BridgedTarget`
  executions. The Layer-3 runtime-code lift in this module remains parameterized
  by embedded-body `BridgedStmts` witnesses; `EvmYulLeanBodyClosure.lean` and
  `EndToEnd.lean` discharge those witnesses for the supported safe source-body
  fragment.

  **Trust boundary shift (pointwise)**: For any builtin call using a bridged
  name, the trust boundary moves from "Verity's custom Yul builtin semantics
  are correct" to "EVMYulLean's builtin semantics match the EVM" (backed by
  upstream conformance tests). Whole-program guarantees are exposed through the
  safe-body EndToEnd wrapper, with the external-call/function-table family left
  as the explicit carve-out.

  Run: lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanRetarget
-/

import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgePredicates
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas
import Compiler.Proofs.YulGeneration.Preservation

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Proofs.YulGeneration
open Compiler.Proofs.IRGeneration

/-! ## Per-builtin backend equivalence helpers

Each helper proves that `evalBuiltinCallWithBackendContext .verity` and
`.evmYulLean` agree for a single concrete builtin name with arbitrary `argVals`.
The proof strategy:
1. Unfold the backend dispatch via `simp only [evalBuiltinCallWithBackendContext]`
2. Case-split `argVals` by arity
3. Right arity: apply the context-lifted bridge lemma from `EvmYulLeanBridgeLemmas`
4. Wrong arity: both sides are definitionally equal (`rfl`)

This avoids unfolding the expensive `legacyEvalBuiltinCallWithContext` if-chain. -/

-- Binary builtins: argVals matches [a, b]
private theorem backends_agree_add s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "add" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "add" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_add_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_sub s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "sub" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "sub" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_sub_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_mul s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "mul" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "mul" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_mul_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_div s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "div" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "div" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_div_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_mod s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "mod" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "mod" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_mod_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_lt s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "lt" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "lt" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_lt_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_gt s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "gt" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "gt" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_gt_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_eq s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "eq" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "eq" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_eq_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

-- Unary builtin: iszero
private theorem backends_agree_iszero s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "iszero" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "iszero" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a] => exact (evalBuiltinCallWithBackendContext_evmYulLean_iszero_bridge s se mv ta bt bn ci bb sl cd a).symm
  | [] => rfl | _ :: _ :: _ => rfl

private theorem backends_agree_and s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "and" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "and" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_and_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_or s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "or" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "or" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_or_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_xor s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "xor" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "xor" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_xor_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

-- Unary builtin: not
private theorem backends_agree_not s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "not" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "not" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a] => exact (evalBuiltinCallWithBackendContext_evmYulLean_not_bridge s se mv ta bt bn ci bb sl cd a).symm
  | [] => rfl | _ :: _ :: _ => rfl

private theorem backends_agree_shl s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "shl" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "shl" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_shl_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_shr s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "shr" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "shr" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_shr_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

-- Ternary builtins: addmod, mulmod
private theorem backends_agree_addmod s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "addmod" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "addmod" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b, n] => exact (evalBuiltinCallWithBackendContext_evmYulLean_addmod_bridge s se mv ta bt bn ci bb sl cd a b n).symm
  | [] => rfl | [_] => rfl | [_, _] => rfl | _ :: _ :: _ :: _ :: _ => rfl

private theorem backends_agree_mulmod s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "mulmod" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "mulmod" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b, n] => exact (evalBuiltinCallWithBackendContext_evmYulLean_mulmod_bridge s se mv ta bt bn ci bb sl cd a b n).symm
  | [] => rfl | [_] => rfl | [_, _] => rfl | _ :: _ :: _ :: _ :: _ => rfl

private theorem backends_agree_byte s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "byte" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "byte" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_byte_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_slt s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "slt" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "slt" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_slt_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_sgt s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "sgt" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "sgt" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_sgt_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_exp s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "exp" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "exp" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_exp_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_sdiv s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "sdiv" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "sdiv" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_sdiv_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_smod s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "smod" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "smod" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_smod_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_sar s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "sar" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "sar" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_sar_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

private theorem backends_agree_signextend s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "signextend" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "signextend" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [a, b] => exact (evalBuiltinCallWithBackendContext_evmYulLean_signextend_bridge s se mv ta bt bn ci bb sl cd a b).symm
  | [] => rfl | [_] => rfl | _ :: _ :: _ :: _ => rfl

-- Nullary builtins: caller, address, callvalue, timestamp, number, chainid, blobbasefee, calldatasize
private theorem backends_agree_caller s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "caller" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "caller" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [] => exact (evalBuiltinCallWithBackendContext_evmYulLean_caller_bridge s se mv ta bt bn ci bb sl cd).symm
  | _ :: _ => rfl

private theorem backends_agree_address s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "address" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "address" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [] => exact (evalBuiltinCallWithBackendContext_evmYulLean_address_bridge s se mv ta bt bn ci bb sl cd).symm
  | _ :: _ => rfl

private theorem backends_agree_callvalue s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "callvalue" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "callvalue" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [] => exact (evalBuiltinCallWithBackendContext_evmYulLean_callvalue_bridge s se mv ta bt bn ci bb sl cd).symm
  | _ :: _ => rfl

private theorem backends_agree_timestamp s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "timestamp" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "timestamp" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [] => exact (evalBuiltinCallWithBackendContext_evmYulLean_timestamp_bridge s se mv ta bt bn ci bb sl cd).symm
  | _ :: _ => rfl

private theorem backends_agree_number s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "number" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "number" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [] => exact (evalBuiltinCallWithBackendContext_evmYulLean_number_bridge s se mv ta bt bn ci bb sl cd).symm
  | _ :: _ => rfl

private theorem backends_agree_chainid s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "chainid" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "chainid" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [] => exact (evalBuiltinCallWithBackendContext_evmYulLean_chainid_bridge s se mv ta bt bn ci bb sl cd).symm
  | _ :: _ => rfl

private theorem backends_agree_blobbasefee s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "blobbasefee" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "blobbasefee" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [] => exact (evalBuiltinCallWithBackendContext_evmYulLean_blobbasefee_bridge s se mv ta bt bn ci bb sl cd).symm
  | _ :: _ => rfl

-- Unary builtin: calldataload
private theorem backends_agree_calldataload s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "calldataload" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "calldataload" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [offset] => exact (evalBuiltinCallWithBackendContext_evmYulLean_calldataload_bridge s se mv ta bt bn ci bb sl cd offset).symm
  | [] => rfl | _ :: _ :: _ => rfl

-- Nullary builtin: calldatasize
private theorem backends_agree_calldatasize s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "calldatasize" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "calldatasize" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [] => exact (evalBuiltinCallWithBackendContext_evmYulLean_calldatasize_bridge s se mv ta bt bn ci bb sl cd).symm
  | _ :: _ => rfl

-- Unary builtin: sload (state-dependent, routed through the same
-- `storage : IRStorageSlot → IRStorageWord` lookup used by Verity's `legacyEvalBuiltinCallWithContext`)
private theorem backends_agree_sload s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "sload" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "sload" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [slot] => exact (evalBuiltinCallWithBackendContext_evmYulLean_sload_bridge s se mv ta bt bn ci bb sl cd slot).symm
  | [] => rfl
  | _ :: _ :: _ => rfl

-- Binary builtin: mappingSlot (Verity-specific helper, routed through the
-- shared keccak-faithful `abstractMappingSlot` derivation)
private theorem backends_agree_mappingSlot s se mv ta bt bn ci bb sl cd av :
    evalBuiltinCallWithBackendContext .verity s se mv ta bt bn ci bb sl cd "mappingSlot" av =
    evalBuiltinCallWithBackendContext .evmYulLean s se mv ta bt bn ci bb sl cd "mappingSlot" av := by
  simp only [evalBuiltinCallWithBackendContext]
  match av with
  | [base, key] => exact (evalBuiltinCallWithBackendContext_evmYulLean_mappingSlot_bridge s se mv ta bt bn ci bb sl cd base key).symm
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ :: _ => rfl

/-! ## Backend Equivalence for Bridged Builtins

The `.evmYulLean` and `.verity` backends agree on all 36 bridged builtins.
This is the pointwise equivalence theorem that Phase 4 retargeting relies on.
All bridged builtin dependencies are fully proven in `EvmYulLeanBridgeLemmas.lean`.
-/

/-- For any builtin in `bridgedBuiltins`, the `.verity` and `.evmYulLean` backends
    produce identical results under `evalBuiltinCallWithBackendContext`.

    This is the master backend equivalence theorem for Phase 4 retargeting.
    It composes the 36 per-builtin bridge theorems into a single dispatch proof.
    Every builtin handled by `legacyEvalBuiltinCallWithContext` is now bridged, so
    `unbridgedBuiltins` is empty.

    This theorem is sorry-free, composing the fully proven per-builtin bridge
    lemmas in `EvmYulLeanBridgeLemmas.lean`. -/
private theorem backends_agree_on_bridged_builtins
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat)
    (func : String) (argVals : List Nat)
    (hBridged : func ∈ bridgedBuiltins) :
    evalBuiltinCallWithBackendContext .verity storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata func argVals =
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata func argVals := by
  simp only [bridgedBuiltins, List.mem_cons, List.mem_nil_iff, or_false] at hBridged
  rcases hBridged with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  -- 36 goals, one per bridged builtin. Dispatch to per-builtin helpers.
  · exact backends_agree_add storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_sub storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_mul storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_div storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_mod storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_lt storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_gt storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_eq storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_iszero storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_and storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_or storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_xor storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_not storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_shl storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_shr storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_addmod storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_mulmod storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_byte storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_slt storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_sgt storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_exp storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_sdiv storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_smod storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_sar storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_signextend storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_caller storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_address storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_callvalue storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_timestamp storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_number storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_chainid storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_blobbasefee storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_calldataload storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_calldatasize storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_sload storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals
  · exact backends_agree_mappingSlot storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata argVals

/-! ## Expression-level backend equivalence

The pointwise builtin theorem lifts through Yul expressions whose call nodes use
only bridged builtin names, plus the backend-independent `tload`/`mload`
special cases handled directly by the Verity Yul expression evaluator.
-/

set_option maxHeartbeats 1000000 in
/-- `keccak256` is not handled by Verity's `legacyEvalBuiltinCallWithContext` (it
    falls through the 35-case if-else chain to the final `else none`) and is
    not handled by the EVMYulLean adapter (`evalBuiltinCallViaEvmYulLean` and
    `evalPureBuiltinViaEvmYulLean` both default to `none` for unknown funcs).
    Both backends therefore agree trivially by returning `none`. This makes
    `keccak256` a safe "bridged by absence" expression name: the Yul
    interpreter cannot compute a hash under either backend, and any Yul
    program that evaluates `keccak256(...)` through this interpreter halts
    identically on both sides.  -/
private theorem backends_agree_on_keccak256
    (storage : IRStorageSlot → IRStorageWord)
    (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (argVals : List Nat) :
    evalBuiltinCallWithBackendContext .verity storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "keccak256" argVals =
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "keccak256" argVals := by
  -- Both sides reduce definitionally to `none` via their respective long
  -- if-else chains on `func`. Using `rfl` with bumped heartbeats is the
  -- simplest path; targeted simp at every level would be longer and no faster.
  rfl

mutual

def evalYulExprsWithBackend (backend : BuiltinBackend) (state : YulState) :
    List Compiler.Yul.YulExpr → Option (List Nat)
  | [] => some []
  | e :: es => do
    let v ← evalYulExprWithBackend backend state e
    let vs ← evalYulExprsWithBackend backend state es
    pure (v :: vs)
termination_by es => exprsSize es
decreasing_by
  all_goals
    simp [exprsSize]
    omega

def evalYulCallWithBackend (backend : BuiltinBackend) (state : YulState)
    (func : String) : List Compiler.Yul.YulExpr → Option Nat
  | args => do
    let argVals ← evalYulExprsWithBackend backend state args
    if func = "tload" then
      match argVals with
      | [slot] => some (state.transientStorage (slot % Compiler.Constants.evmModulus))
      | _ => none
    else if func = "mload" then
      match argVals with
      | [offset] => some (state.memory offset)
      | _ => none
    else if func = "keccak256" then
      match argVals with
      | [offset, size] => some (abstractKeccakMemorySlice state.memory offset size)
      | _ => none
    else
      evalBuiltinCallWithBackendContext backend
        state.storage state.sender state.msgValue state.thisAddress state.blockTimestamp
        state.blockNumber state.chainId state.blobBaseFee state.selector state.calldata func argVals
termination_by args => exprsSize args + 1
decreasing_by
  omega

def evalYulExprWithBackend (backend : BuiltinBackend) (state : YulState) :
    Compiler.Yul.YulExpr → Option Nat
  | .lit n => some n
  | .hex n => some n
  | .str _ => none
  | .ident name => state.getVar name
  | .call func args => evalYulCallWithBackend backend state func args
termination_by e => exprSize e
decreasing_by
  simp [exprSize]

end

mutual

private theorem evalYulExprWithBackend_evmYulLean_eq
    (state : YulState) (expr : Compiler.Yul.YulExpr) :
    evalYulExprWithBackend .evmYulLean state expr = evalYulExpr state expr := by
  cases expr with
  | lit _ => simp [evalYulExprWithBackend, evalYulExpr]
  | hex _ => simp [evalYulExprWithBackend, evalYulExpr]
  | str _ => simp [evalYulExprWithBackend, evalYulExpr]
  | ident _ => simp [evalYulExprWithBackend, evalYulExpr]
  | call func args =>
      simp only [evalYulExprWithBackend, evalYulExpr, evalYulCallWithBackend, evalYulCall]
      rw [evalYulExprsWithBackend_evmYulLean_eq state args]
      rfl

private theorem evalYulExprsWithBackend_evmYulLean_eq
    (state : YulState) (args : List Compiler.Yul.YulExpr) :
    evalYulExprsWithBackend .evmYulLean state args = evalYulExprs state args := by
  cases args with
  | nil => simp [evalYulExprsWithBackend, evalYulExprs]
  | cons arg rest =>
      simp only [evalYulExprsWithBackend, evalYulExprs]
      rw [evalYulExprWithBackend_evmYulLean_eq state arg,
        evalYulExprsWithBackend_evmYulLean_eq state rest]

end

mutual

private theorem evalYulExprWithBackend_eq_on_bridged
    (state : YulState) (expr : Compiler.Yul.YulExpr) (hExpr : BridgedExpr expr) :
    evalYulExprWithBackend .verity state expr =
    evalYulExprWithBackend .evmYulLean state expr := by
  cases hExpr with
  | lit _ => simp [evalYulExprWithBackend]
  | hex _ => simp [evalYulExprWithBackend]
  | str _ => simp [evalYulExprWithBackend]
  | ident _ => simp [evalYulExprWithBackend]
  | call func args hName hArgs =>
      simp only [evalYulExprWithBackend, evalYulCallWithBackend]
      rw [evalYulExprsWithBackend_eq_on_bridged state args hArgs]
      cases hEval : evalYulExprsWithBackend .evmYulLean state args with
      | none => rfl
      | some argVals =>
          rcases hName with hBridged | rfl | rfl | rfl
          · have hEq := backends_agree_on_bridged_builtins
              state.storage state.sender state.msgValue state.thisAddress
              state.blockTimestamp state.blockNumber state.chainId state.blobBaseFee
              state.selector state.calldata func argVals hBridged
            simp [hEq]
          · simp
          · simp
          · -- func = "keccak256": both backends now have a direct keccak256
            -- branch that computes `abstractKeccakMemorySlice` identically.
            rfl

private theorem evalYulExprsWithBackend_eq_on_bridged
    (state : YulState) (args : List Compiler.Yul.YulExpr)
    (hArgs : ∀ arg ∈ args, BridgedExpr arg) :
    evalYulExprsWithBackend .verity state args =
    evalYulExprsWithBackend .evmYulLean state args := by
  cases args with
  | nil =>
      simp [evalYulExprsWithBackend]
  | cons arg rest =>
      have hArg : BridgedExpr arg := hArgs arg (by simp)
      have hRest : ∀ e ∈ rest, BridgedExpr e := by
        intro e he
        exact hArgs e (by simp [he])
      simp only [evalYulExprsWithBackend]
      rw [evalYulExprWithBackend_eq_on_bridged state arg hArg,
        evalYulExprsWithBackend_eq_on_bridged state rest hRest]

end

private theorem evalYulExpr_evmYulLean_eq_on_bridged
    (state : YulState) (expr : Compiler.Yul.YulExpr) (_hExpr : BridgedExpr expr) :
    evalYulExpr state expr =
    evalYulExprWithBackend .evmYulLean state expr := by
  exact (evalYulExprWithBackend_evmYulLean_eq state expr).symm

/-! ## Statement-level backend-parameterized executor

`execYulFuelWithBackend` mirrors `legacyExecYulFuel` from `Semantics.lean` but routes
each expression evaluation through `evalYulExprWithBackend backend`. The
statement and runtime-code theorems below bridge `.verity` and `.evmYulLean`
on targets satisfying the `Bridged*` predicates. Source-body closure and the
public safe-body EndToEnd wrapper live in `EvmYulLeanBodyClosure.lean` and
`Compiler.Proofs.EndToEnd`.
-/

private def execYulFuelWithBackend (backend : BuiltinBackend) :
    Nat → YulState → YulExecTarget → YulExecResult
  | _, state, .stmts [] => .continue state
  | _, state, .stmt (Compiler.Yul.YulStmt.funcDef _ _ _ _) => .continue state
  | 0, state, _ => .revert state
  | Nat.succ fuel, state, target =>
      match target with
      | .stmt stmt =>
          match stmt with
          | .comment _ => .continue state
          | .let_ name value =>
              match evalYulExprWithBackend backend state value with
              | some v => .continue (state.setVar name v)
              | none => .revert state
          | .letMany _ _ => .revert state
          | .assign name value =>
              match evalYulExprWithBackend backend state value with
              | some v => .continue (state.setVar name v)
              | none => .revert state
          | .leave => .continue state
          | .expr e =>
              match e with
              | .call "sstore" [slotExpr, valExpr] =>
                  match slotExpr with
                  | .call "mappingSlot" [baseExpr, keyExpr] =>
                      match evalYulExprWithBackend backend state baseExpr,
                            evalYulExprWithBackend backend state keyExpr,
                            evalYulExprWithBackend backend state valExpr with
                      | some baseSlot, some key, some val =>
                          let updated := Compiler.Proofs.abstractStoreMappingEntry
                            state.storage baseSlot key val
                          .continue { state with storage := updated }
                      | _, _, _ => .revert state
                  | _ =>
                      match evalYulExprWithBackend backend state slotExpr,
                            evalYulExprWithBackend backend state valExpr with
                      | some slot, some val =>
                          let updated := Compiler.Proofs.abstractStoreStorageOrMapping
                            state.storage slot val
                          .continue { state with storage := updated }
                      | _, _ => .revert state
              | .call "mstore" [offsetExpr, valExpr] =>
                  match evalYulExprWithBackend backend state offsetExpr,
                        evalYulExprWithBackend backend state valExpr with
                  | some offset, some val =>
                      .continue { state with
                        memory := fun o => if o = offset then val else state.memory o }
                  | _, _ => .revert state
              | .call "tstore" [offsetExpr, valExpr] =>
                  match evalYulExprWithBackend backend state offsetExpr,
                        evalYulExprWithBackend backend state valExpr with
                  | some offset, some val =>
                      .continue { state with
                        transientStorage := fun o =>
                          if o = offset then val else state.transientStorage o }
                  | _, _ => .revert state
              | .call "stop" [] => .stop state
              | .call "return" [offsetExpr, sizeExpr] =>
                  match evalYulExprWithBackend backend state offsetExpr,
                        evalYulExprWithBackend backend state sizeExpr with
                  | some offset, some size =>
                      if size = 32 then
                        .return (state.memory offset) state
                      else
                        .return 0 state
                  | _, _ => .revert state
              | .call "revert" [_, _] => .revert state
              | .call func args =>
                  if isYulLogName func then
                    match evalYulExprsWithBackend backend state args with
                    | some argVals =>
                        match applyYulLogCall? state func argVals with
                        | some next => .continue next
                        | none => .revert state
                    | none => .revert state
                  else
                    match evalYulExprWithBackend backend state e with
                    | some _ => .continue state
                    | none => .revert state
              | _ =>
                  match evalYulExprWithBackend backend state e with
                  | some _ => .continue state
                  | none => .revert state
          | .if_ cond body =>
              match evalYulExprWithBackend backend state cond with
              | some v =>
                  if v = 0 then
                    .continue state
                  else
                    execYulFuelWithBackend backend fuel state (.stmts body)
              | none => .revert state
          | .switch expr cases defaultCase =>
              match evalYulExprWithBackend backend state expr with
              | some v =>
                  match cases.find? (fun x => decide (x.fst = v)) with
                  | some (_, body) =>
                      execYulFuelWithBackend backend fuel state (.stmts body)
                  | none =>
                      match defaultCase with
                      | some body =>
                          execYulFuelWithBackend backend fuel state (.stmts body)
                      | none => .continue state
              | none => .revert state
          | .for_ init cond post body =>
              match execYulFuelWithBackend backend fuel state (.stmts init) with
              | .continue s' =>
                  match evalYulExprWithBackend backend s' cond with
                  | some v =>
                      if v = 0 then .continue s'
                      else
                        match execYulFuelWithBackend backend fuel s' (.stmts body) with
                        | .continue s'' =>
                            match execYulFuelWithBackend backend fuel s'' (.stmts post) with
                            | .continue s''' =>
                                execYulFuelWithBackend backend fuel s'''
                                  (.stmt (.for_ [] cond post body))
                            | other => other
                        | other => other
                  | none => .revert s'
              | other => other
          | .block stmts =>
              execYulFuelWithBackend backend fuel state (.stmts stmts)
          | .funcDef _ _ _ _ => .continue state
      | .stmts [] => .continue state
      | .stmts (stmt :: rest) =>
          match execYulFuelWithBackend backend fuel state (.stmt stmt) with
          | .continue s' => execYulFuelWithBackend backend fuel s' (.stmts rest)
          | .return v s => .return v s
          | .stop s => .stop s
          | .revert s => .revert s

/-- The backend-parameterized executor recovers `legacyExecYulFuel` at the `.verity`
    backend. Statement-level analogue of `evalYulExprWithBackend_verity_eq` —
    this is the correctness obligation that justifies replacing every
    `legacyExecYulFuel` call in upstream theorems with
    `execYulFuelWithBackend .verity`. -/
private theorem execYulFuelWithBackend_evmYulLean_eq
    (fuel : Nat) (state : YulState) (target : YulExecTarget) :
    execYulFuelWithBackend .evmYulLean fuel state target =
    legacyExecYulFuel fuel state target := by
  induction fuel generalizing state target with
  | zero =>
      cases target with
      | stmt s => cases s <;> rfl
      | stmts ss => cases ss <;> rfl
  | succ fuel ih =>
      cases target with
      | stmt s =>
          cases s <;> (
            try rfl
            all_goals (
              simp only [execYulFuelWithBackend, legacyExecYulFuel,
                evalYulExprWithBackend_evmYulLean_eq,
                evalYulExprsWithBackend_evmYulLean_eq, ih]
              try rfl))
      | stmts ss =>
          cases ss <;> (
            try rfl
            all_goals (
              simp only [execYulFuelWithBackend, legacyExecYulFuel, ih]
              try rfl))

/-! ## Statement-level backend equivalence: value-binding helpers

The following pair of theorems establish the first statement-level bridges
between `.verity` and `.evmYulLean` backends. They cover the `.let_` and
`.assign` Yul statement forms when their right-hand-side expression is a
`BridgedExpr`. Both proofs reduce by unfolding the executor one step then
rewriting through `evalYulExprWithBackend_eq_on_bridged`.

These are intentionally narrow helpers. A future statement-level predicate
(covering `.block`, sstore/mstore/tstore, and control flow) can dispatch to
them rather than re-deriving the expression rewrite each time.
-/

private theorem execYulFuelWithBackend_let_eq_on_bridged
    (fuel : Nat) (state : YulState) (name : String)
    (value : Compiler.Yul.YulExpr) (hValue : BridgedExpr value) :
    execYulFuelWithBackend .verity fuel state (.stmt (.let_ name value)) =
    execYulFuelWithBackend .evmYulLean fuel state (.stmt (.let_ name value)) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [execYulFuelWithBackend]
      rw [evalYulExprWithBackend_eq_on_bridged state value hValue]

private theorem execYulFuelWithBackend_assign_eq_on_bridged
    (fuel : Nat) (state : YulState) (name : String)
    (value : Compiler.Yul.YulExpr) (hValue : BridgedExpr value) :
    execYulFuelWithBackend .verity fuel state (.stmt (.assign name value)) =
    execYulFuelWithBackend .evmYulLean fuel state (.stmt (.assign name value)) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [execYulFuelWithBackend]
      rw [evalYulExprWithBackend_eq_on_bridged state value hValue]

/-! ## Straight-line statement backend equivalence

This predicate captures the non-branching statement fragment whose backend
dependence is solely through expression evaluation. It is the first
statement-level lift of `evalYulExprWithBackend_eq_on_bridged`; structured
control flow (`switch`, `for`, recursive `block`) still needs a separate
fuel/AST induction.
-/

private theorem execYulFuelWithBackend_eq_on_bridged_straight_stmt
    (fuel : Nat) (state : YulState) (stmt : Compiler.Yul.YulStmt)
    (hStmt : BridgedStraightStmt stmt) :
    execYulFuelWithBackend .verity fuel state (.stmt stmt) =
    execYulFuelWithBackend .evmYulLean fuel state (.stmt stmt) := by
  cases hStmt with
  | comment _ => cases fuel <;> rfl
  | let_ name value hValue =>
      exact execYulFuelWithBackend_let_eq_on_bridged fuel state name value hValue
  | letMany _ _ => cases fuel <;> rfl
  | assign name value hValue =>
      exact execYulFuelWithBackend_assign_eq_on_bridged fuel state name value hValue
  | «leave» => cases fuel <;> rfl
  | expr_sstore_mapping baseExpr keyExpr valExpr hBase hKey hVal =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [execYulFuelWithBackend]
          rw [evalYulExprWithBackend_eq_on_bridged state baseExpr hBase,
            evalYulExprWithBackend_eq_on_bridged state keyExpr hKey,
            evalYulExprWithBackend_eq_on_bridged state valExpr hVal]
  | expr_sstore_lit slot valExpr hVal =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [execYulFuelWithBackend]
          rw [evalYulExprWithBackend_eq_on_bridged state (.lit slot) (BridgedExpr.lit slot),
            evalYulExprWithBackend_eq_on_bridged state valExpr hVal]
  | expr_sstore_ident slotName valExpr hVal =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [execYulFuelWithBackend]
          rw [evalYulExprWithBackend_eq_on_bridged state (.ident slotName)
              (BridgedExpr.ident slotName),
            evalYulExprWithBackend_eq_on_bridged state valExpr hVal]
  | expr_sstore_add leftExpr rightExpr valExpr hLeft hRight hVal =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          have hAdd : BridgedExpr
              (Compiler.Yul.YulExpr.call "add" [leftExpr, rightExpr]) := by
            refine BridgedExpr.call "add" [leftExpr, rightExpr]
              (Or.inl ?_) ?_
            · simp [bridgedBuiltins]
            · intro arg hMem
              rcases List.mem_cons.mp hMem with rfl | hMem
              · exact hLeft
              · rcases List.mem_cons.mp hMem with rfl | hMem
                · exact hRight
                · cases hMem
          have hAddEval := evalYulExprWithBackend_eq_on_bridged state
            (Compiler.Yul.YulExpr.call "add" [leftExpr, rightExpr]) hAdd
          have hValEval := evalYulExprWithBackend_eq_on_bridged state valExpr hVal
          -- The slot `.call "add" [...]` is not a `.call "mappingSlot" [...]`
          -- so the inner slot match takes the generic `_` branch. `simp`
          -- reduces the string-literal pattern mismatch via iota; the two
          -- backend evals are unified via `hAddEval` / `hValEval`.
          simp [execYulFuelWithBackend, hAddEval, hValEval]
  | expr_mstore offsetExpr valExpr hOffset hVal =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [execYulFuelWithBackend]
          rw [evalYulExprWithBackend_eq_on_bridged state offsetExpr hOffset,
            evalYulExprWithBackend_eq_on_bridged state valExpr hVal]
  | expr_tstore offsetExpr valExpr hOffset hVal =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [execYulFuelWithBackend]
          rw [evalYulExprWithBackend_eq_on_bridged state offsetExpr hOffset,
            evalYulExprWithBackend_eq_on_bridged state valExpr hVal]
  | expr_stop => cases fuel <;> rfl
  | expr_return offsetExpr sizeExpr hOffset hSize =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [execYulFuelWithBackend]
          rw [evalYulExprWithBackend_eq_on_bridged state offsetExpr hOffset,
            evalYulExprWithBackend_eq_on_bridged state sizeExpr hSize]
  | expr_revert _ _ => cases fuel <;> rfl
  | expr_log func args hLog hArgs =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          -- Enumerate the five log names so the specific-string cases
          -- (`sstore`, `mstore`, `tstore`, `stop`, `return`, `revert`) drop
          -- out and the match reduces into the generic `.call func args`
          -- branch where both backends share `applyYulLogCall?`. Each backend
          -- differs only in `evalYulExprWithBackend` / `evalYulExprsWithBackend`
          -- on the bridged argument list, so rewriting the verity side to the
          -- evmYulLean side makes both sides syntactically identical.
          have hFunc : func = "log0" ∨ func = "log1" ∨ func = "log2" ∨
              func = "log3" ∨ func = "log4" := by
            simp [isYulLogName] at hLog
            tauto
          have hEval := evalYulExprsWithBackend_eq_on_bridged state args hArgs
          rcases hFunc with rfl | rfl | rfl | rfl | rfl <;>
            simp [execYulFuelWithBackend, isYulLogName, hEval]
  | funcDef _ _ _ _ => cases fuel <;> rfl

private theorem execYulFuelWithBackend_eq_on_bridged_straight_stmts
    (fuel : Nat) (state : YulState) (stmts : List Compiler.Yul.YulStmt)
    (hStmts : BridgedStraightStmts stmts) :
    execYulFuelWithBackend .verity fuel state (.stmts stmts) =
    execYulFuelWithBackend .evmYulLean fuel state (.stmts stmts) := by
  induction fuel generalizing state stmts with
  | zero =>
      cases stmts <;> rfl
  | succ fuel ih =>
      cases stmts with
      | nil => rfl
      | cons stmt rest =>
          have hStmt : BridgedStraightStmt stmt := hStmts stmt (by simp)
          have hRest : BridgedStraightStmts rest := by
            intro s hs
            exact hStmts s (by simp [hs])
          simp only [execYulFuelWithBackend]
          rw [execYulFuelWithBackend_eq_on_bridged_straight_stmt fuel state stmt hStmt]
          cases hExec : execYulFuelWithBackend .evmYulLean fuel state (.stmt stmt) with
          | «continue» s' =>
              simp only
              exact ih s' rest hRest
          | «return» v s => rfl
          | «stop» s => rfl
          | «revert» s => rfl

/-- A `.block` wrapper around a straight-line statement list preserves the
    backend equivalence established for `BridgedStraightStmts`. This discharges
    the block constructor when the block body is already in the straight-line
    fragment; recursive blocks and branching control flow still require the
    broader statement predicate/induction. -/
private theorem execYulFuelWithBackend_block_eq_on_bridged_straight_stmts
    (fuel : Nat) (state : YulState) (stmts : List Compiler.Yul.YulStmt)
    (hStmts : BridgedStraightStmts stmts) :
    execYulFuelWithBackend .verity fuel state (.stmt (.block stmts)) =
    execYulFuelWithBackend .evmYulLean fuel state (.stmt (.block stmts)) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [execYulFuelWithBackend]
      exact execYulFuelWithBackend_eq_on_bridged_straight_stmts fuel state stmts hStmts

/-- An `.if_` with a bridged condition and a straight-line body preserves
    backend equivalence. The condition is evaluated via `BridgedExpr`; when the
    condition evaluates to a nonzero value the body is executed at one less
    fuel, which we discharge via `execYulFuelWithBackend_eq_on_bridged_straight_stmts`.
    First narrow-helper lift into branching control flow; `.switch` and `.for_`
    still require their own helpers, and recursive control-flow bodies still
    require a broader predicate/induction. -/
private theorem execYulFuelWithBackend_if_eq_on_bridged_body
    (fuel : Nat) (state : YulState) (cond : Compiler.Yul.YulExpr)
    (body : List Compiler.Yul.YulStmt)
    (hCond : BridgedExpr cond) (hBody : BridgedStraightStmts body) :
    execYulFuelWithBackend .verity fuel state (.stmt (.if_ cond body)) =
    execYulFuelWithBackend .evmYulLean fuel state (.stmt (.if_ cond body)) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [execYulFuelWithBackend]
      rw [evalYulExprWithBackend_eq_on_bridged state cond hCond]
      cases evalYulExprWithBackend .evmYulLean state cond with
      | none => rfl
      | some v =>
          by_cases hv : v = 0
          · simp [hv]
          · simp [hv]
            exact execYulFuelWithBackend_eq_on_bridged_straight_stmts fuel state body hBody

/-- A `.switch` with a bridged scrutinee and straight-line selected bodies
    preserves backend equivalence. The predicate only needs to cover bodies that
    can actually be selected by `find?`; the default branch is handled
    separately. Recursive switch bodies and loops still need the broader
    statement predicate/induction. -/
private theorem execYulFuelWithBackend_switch_eq_on_bridged_cases
    (fuel : Nat) (state : YulState) (expr : Compiler.Yul.YulExpr)
    (cases : List (Nat × List Compiler.Yul.YulStmt))
    (defaultCase : Option (List Compiler.Yul.YulStmt))
    (hExpr : BridgedExpr expr) (hCases : BridgedSwitchCases cases)
    (hDefault : ∀ body, defaultCase = some body → BridgedStraightStmts body) :
    execYulFuelWithBackend .verity fuel state (.stmt (.switch expr cases defaultCase)) =
    execYulFuelWithBackend .evmYulLean fuel state (.stmt (.switch expr cases defaultCase)) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [execYulFuelWithBackend]
      rw [evalYulExprWithBackend_eq_on_bridged state expr hExpr]
      cases evalYulExprWithBackend .evmYulLean state expr with
      | none => rfl
      | some v =>
          cases hFind : cases.find? (fun x => decide (x.fst = v)) with
          | some hit =>
              cases hit with
              | mk value body =>
                  simp [hFind]
                  exact execYulFuelWithBackend_eq_on_bridged_straight_stmts
                    fuel state body (hCases v value body hFind)
          | none =>
              cases hDefaultCase : defaultCase with
              | none =>
                  simp [hFind]
              | some body =>
                  simp [hFind]
                  exact execYulFuelWithBackend_eq_on_bridged_straight_stmts
                    fuel state body (hDefault body hDefaultCase)

/-- A `.for_` with bridged straight-line init/body/post lists and a bridged
    condition preserves backend equivalence. The recursive loop call is made at
    the predecessor fuel with an empty initializer, so the proof follows the
    executor's fuel structure directly. Recursive control-flow inside the loop
    lists still needs the broader statement predicate/induction. -/
private theorem execYulFuelWithBackend_for_eq_on_bridged_parts
    (fuel : Nat) (state : YulState)
    (init : List Compiler.Yul.YulStmt) (cond : Compiler.Yul.YulExpr)
    (post body : List Compiler.Yul.YulStmt)
    (hInit : BridgedStraightStmts init) (hCond : BridgedExpr cond)
    (hPost : BridgedStraightStmts post) (hBody : BridgedStraightStmts body) :
    execYulFuelWithBackend .verity fuel state (.stmt (.for_ init cond post body)) =
    execYulFuelWithBackend .evmYulLean fuel state (.stmt (.for_ init cond post body)) := by
  induction fuel generalizing state init with
  | zero => rfl
  | succ fuel ih =>
      simp only [execYulFuelWithBackend]
      rw [execYulFuelWithBackend_eq_on_bridged_straight_stmts fuel state init hInit]
      cases execYulFuelWithBackend .evmYulLean fuel state (.stmts init) with
      | «continue» s' =>
          simp only
          rw [evalYulExprWithBackend_eq_on_bridged s' cond hCond]
          cases evalYulExprWithBackend .evmYulLean s' cond with
          | none => rfl
          | some v =>
              by_cases hv : v = 0
              · simp [hv]
              · simp [hv]
                rw [execYulFuelWithBackend_eq_on_bridged_straight_stmts fuel s' body hBody]
                cases execYulFuelWithBackend .evmYulLean fuel s' (.stmts body) with
                | «continue» s'' =>
                    simp only
                    rw [execYulFuelWithBackend_eq_on_bridged_straight_stmts fuel s'' post hPost]
                    cases execYulFuelWithBackend .evmYulLean fuel s'' (.stmts post) with
                    | «continue» s''' =>
                        simp only
                        exact ih s''' [] (by intro stmt hMem; cases hMem)
                    | «return» _ _ => rfl
                    | «stop» _ => rfl
                    | «revert» _ => rfl
                | «return» _ _ => rfl
                | «stop» _ => rfl
                | «revert» _ => rfl
      | «return» _ _ => rfl
      | «stop» _ => rfl
      | «revert» _ => rfl

/-! ## Recursive statement backend equivalence

`BridgedStmt` lifts the earlier straight-line/control-flow helpers to recursive
Yul statement structure. It is still an explicit fragment predicate: every
expression dependency must satisfy `BridgedExpr`, and every nested statement
list must recursively satisfy `BridgedStmt`.
-/

inductive BridgedTarget : YulExecTarget → Prop
  | stmt (stmt : Compiler.Yul.YulStmt) (hStmt : BridgedStmt stmt) :
      BridgedTarget (.stmt stmt)
  | stmts (stmts : List Compiler.Yul.YulStmt) (hStmts : BridgedStmts stmts) :
      BridgedTarget (.stmts stmts)

/-! ## Generated-code closure under the recursive statement predicate

The recursive executor theorem above is useful for Layer 3 only once generated
runtime wrappers are known to satisfy `BridgedStmt`. These lemmas prove that
the compiler-emitted dispatch shell (`callvalue`/`calldatasize` guards,
selector switch, fallback/receive wrapper, optional mapping helper) is bridged
whenever the IR function and entrypoint bodies it contains are bridged.
-/

private theorem bridgedExpr_callvalue :
    BridgedExpr (Compiler.Yul.YulExpr.call "callvalue" []) := by
  exact BridgedExpr.call "callvalue" [] (Or.inl (by simp [bridgedBuiltins]))
    (by intro arg hMem; cases hMem)

private theorem bridgedExpr_calldatasize :
    BridgedExpr (Compiler.Yul.YulExpr.call "calldatasize" []) := by
  exact BridgedExpr.call "calldatasize" [] (Or.inl (by simp [bridgedBuiltins]))
    (by intro arg hMem; cases hMem)

private theorem bridgedExpr_selector :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "shr"
        [Compiler.Yul.YulExpr.lit Compiler.Constants.selectorShift,
          Compiler.Yul.YulExpr.call "calldataload" [Compiler.Yul.YulExpr.lit 0]]) := by
  refine BridgedExpr.call "shr" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · exact BridgedExpr.lit Compiler.Constants.selectorShift
  · refine BridgedExpr.call "calldataload" _ (Or.inl (by simp [bridgedBuiltins])) ?_
    intro nested hNested
    simp only [List.mem_singleton] at hNested
    subst hNested
    exact BridgedExpr.lit 0

/-- The generated dispatcher selector expression is in the bridged expression
fragment, so the EVMYulLean fuel wrapper evaluates it exactly like
the historical Verity interpreter. -/
private theorem bridgedExpr_selectorExpr :
    BridgedExpr Compiler.Proofs.YulGeneration.selectorExpr := by
  simpa [Compiler.Proofs.YulGeneration.selectorExpr] using bridgedExpr_selector

/-- The EVMYulLean fuel wrapper selects the same 4-byte dispatcher
selector as the generated Verity selector expression.

This is the first generated-dispatcher semantic slice needed by the native
migration: every native/EVMYulLean dispatcher simulation branches on this
expression before it reaches storage, memory, or halt behavior. -/
@[simp] private theorem evalYulExprWithBackend_evmYulLean_selectorExpr_semantics
    (state : YulState) :
    evalYulExprWithBackend .evmYulLean state
        Compiler.Proofs.YulGeneration.selectorExpr =
      some (state.selector % selectorModulus) := by
  rw [← evalYulExpr_evmYulLean_eq_on_bridged state
    Compiler.Proofs.YulGeneration.selectorExpr bridgedExpr_selectorExpr]
  exact evalYulExpr_selectorExpr_semantics state

private theorem bridgedExpr_calldatasize_lt (n : Nat) :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "lt"
        [Compiler.Yul.YulExpr.call "calldatasize" [], Compiler.Yul.YulExpr.lit n]) := by
  refine BridgedExpr.call "lt" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · exact bridgedExpr_calldatasize
  · exact BridgedExpr.lit n

private theorem bridgedExpr_has_selector :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "iszero"
        [Compiler.Yul.YulExpr.call "lt"
          [Compiler.Yul.YulExpr.call "calldatasize" [], Compiler.Yul.YulExpr.lit 4]]) := by
  refine BridgedExpr.call "iszero" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst hMem
  exact bridgedExpr_calldatasize_lt 4

private theorem bridgedExpr_empty_calldata :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "eq"
        [Compiler.Yul.YulExpr.call "calldatasize" [], Compiler.Yul.YulExpr.lit 0]) := by
  refine BridgedExpr.call "eq" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · exact bridgedExpr_calldatasize
  · exact BridgedExpr.lit 0

private theorem bridgedExpr_iszero_ident (name : String) :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "iszero" [Compiler.Yul.YulExpr.ident name]) := by
  refine BridgedExpr.call "iszero" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst hMem
  exact BridgedExpr.ident name


theorem callvalueGuard_bridged : BridgedStmt Compiler.CodegenCommon.callvalueGuard := by
  unfold Compiler.CodegenCommon.callvalueGuard
  exact bridgedStmt_if_of_bridgedStmts bridgedExpr_callvalue
    BridgedStmts_singleton_revert_zero

theorem calldatasizeGuard_bridged (numParams : Nat) :
    BridgedStmt (Compiler.CodegenCommon.calldatasizeGuard numParams) := by
  unfold Compiler.CodegenCommon.calldatasizeGuard
  exact bridgedStmt_if_of_bridgedStmts (bridgedExpr_calldatasize_lt (4 + numParams * 32))
    BridgedStmts_singleton_revert_zero

theorem dispatchBody_bridged (payable : Bool) (label : String)
    (body : List Compiler.Yul.YulStmt) (hBody : BridgedStmts body) :
    BridgedStmts (Compiler.CodegenCommon.dispatchBody payable label body) := by
  unfold Compiler.CodegenCommon.dispatchBody
  cases payable <;>
    simp only [Bool.false_eq_true, ite_false, ite_true,
      List.singleton_append]
  · exact BridgedStmts_cons_comment label
      (BridgedStmts_cons callvalueGuard_bridged hBody)
  · exact BridgedStmts_cons_comment label hBody

theorem defaultDispatchCase_bridged
    (fallback receive : Option Compiler.IREntrypoint)
    (hFallback : ∀ fb, fallback = some fb → BridgedStmts fb.body)
    (hReceive : ∀ rc, receive = some rc → BridgedStmts rc.body) :
    BridgedStmts (Compiler.CodegenCommon.defaultDispatchCase fallback receive) := by
  cases receive with
  | none =>
      cases fallback with
      | none =>
          unfold Compiler.CodegenCommon.defaultDispatchCase
          exact BridgedStmts_singleton_revert_zero
      | some fb =>
          unfold Compiler.CodegenCommon.defaultDispatchCase
          exact dispatchBody_bridged fb.payable "fallback()" fb.body
            (hFallback fb rfl)
  | some rc =>
      cases fallback with
      | none =>
          unfold Compiler.CodegenCommon.defaultDispatchCase
          refine BridgedStmts_singleton_block ?_
          exact BridgedStmts_cons_let "__is_empty_calldata" _ bridgedExpr_empty_calldata
            (BridgedStmts_cons_if
              (BridgedExpr.ident "__is_empty_calldata")
              (dispatchBody_bridged rc.payable "receive()" rc.body
                (hReceive rc rfl))
              (BridgedStmts_cons_if (bridgedExpr_iszero_ident "__is_empty_calldata")
                BridgedStmts_singleton_revert_zero
                BridgedStmts_nil))
      | some fb =>
          unfold Compiler.CodegenCommon.defaultDispatchCase
          refine BridgedStmts_singleton_block ?_
          exact BridgedStmts_cons_let "__is_empty_calldata" _ bridgedExpr_empty_calldata
            (BridgedStmts_cons_if
              (BridgedExpr.ident "__is_empty_calldata")
              (dispatchBody_bridged rc.payable "receive()" rc.body
                (hReceive rc rfl))
              (BridgedStmts_cons_if (bridgedExpr_iszero_ident "__is_empty_calldata")
                (dispatchBody_bridged fb.payable "fallback()" fb.body
                  (hFallback fb rfl))
                BridgedStmts_nil))

private theorem switchCases_bridged
    (funcs : List Compiler.IRFunction)
    (hFunctions : ∀ fn, fn ∈ funcs → BridgedStmts fn.body) :
    ∀ scrutinee value body,
      (funcs.map (fun fn =>
        (fn.selector,
          Compiler.CodegenCommon.dispatchBody fn.payable s!"{fn.name}()"
            ([Compiler.CodegenCommon.calldatasizeGuard fn.params.length] ++ fn.body)))).find?
            (fun x => decide (x.fst = scrutinee)) = some (value, body) →
      BridgedStmts body := by
  intro scrutinee value body hFind
  have hMem :
      (value, body) ∈ funcs.map (fun fn =>
        (fn.selector,
          Compiler.CodegenCommon.dispatchBody fn.payable s!"{fn.name}()"
            ([Compiler.CodegenCommon.calldatasizeGuard fn.params.length] ++ fn.body))) :=
    List.mem_of_find?_eq_some hFind
  rcases List.mem_map.mp hMem with ⟨fn, hFn, hEq⟩
  cases hEq
  exact dispatchBody_bridged fn.payable s!"{fn.name}()"
    ([Compiler.CodegenCommon.calldatasizeGuard fn.params.length] ++ fn.body)
    (BridgedStmts_cons (calldatasizeGuard_bridged fn.params.length)
      (hFunctions fn hFn))

theorem buildSwitch_bridged
    (funcs : List Compiler.IRFunction)
    (fallback receive : Option Compiler.IREntrypoint)
    (hFunctions : ∀ fn, fn ∈ funcs → BridgedStmts fn.body)
    (hFallback : ∀ fb, fallback = some fb → BridgedStmts fb.body)
    (hReceive : ∀ rc, receive = some rc → BridgedStmts rc.body) :
    BridgedStmt (Compiler.CodegenCommon.buildSwitch funcs fallback receive false) := by
  unfold Compiler.CodegenCommon.buildSwitch
  exact bridgedStmt_block_of_bridgedStmts
    (BridgedStmts_cons_let "__has_selector" _ bridgedExpr_has_selector
      (BridgedStmts_cons_if (bridgedExpr_iszero_ident "__has_selector")
        (defaultDispatchCase_bridged fallback receive hFallback hReceive)
        (BridgedStmts_cons_if
          (BridgedExpr.ident "__has_selector")
          (BridgedStmts_singleton_switch
            bridgedExpr_selector
            (switchCases_bridged funcs hFunctions)
            (by
              intro body hBody
              cases hBody
              exact defaultDispatchCase_bridged fallback receive hFallback hReceive))
          BridgedStmts_nil)))

theorem mappingSlotFuncAt_bridged (scratchBase : Nat) :
    BridgedStmt (Compiler.CodegenCommon.mappingSlotFuncAt scratchBase) := by
  unfold Compiler.CodegenCommon.mappingSlotFuncAt
  exact bridgedStmt_funcDef "mappingSlot" ["baseSlot", "key"] ["slot"] _

theorem runtimeCode_bridged
    (contract : Compiler.IRContract)
    (hFunctions : ∀ fn, fn ∈ contract.functions → BridgedStmts fn.body)
    (hFallback : ∀ fb, contract.fallbackEntrypoint = some fb → BridgedStmts fb.body)
    (hReceive : ∀ rc, contract.receiveEntrypoint = some rc → BridgedStmts rc.body)
    (hInternals : BridgedStmts contract.internalFunctions) :
    BridgedStmts (Compiler.CodegenCommon.runtimeCode contract) := by
  unfold Compiler.CodegenCommon.runtimeCode
  cases contract.usesMapping
  · exact BridgedStmts_snoc hInternals
      (buildSwitch_bridged contract.functions contract.fallbackEntrypoint
        contract.receiveEntrypoint hFunctions hFallback hReceive)
  · simp only [ite_true]
    exact BridgedStmts_cons (mappingSlotFuncAt_bridged 0)
      (BridgedStmts_snoc hInternals
        (buildSwitch_bridged contract.functions contract.fallbackEntrypoint
          contract.receiveEntrypoint hFunctions hFallback hReceive))

theorem emitYul_runtimeCode_bridged
    (contract : Compiler.IRContract)
    (hFunctions : ∀ fn, fn ∈ contract.functions → BridgedStmts fn.body)
    (hFallback : ∀ fb, contract.fallbackEntrypoint = some fb → BridgedStmts fb.body)
    (hReceive : ∀ rc, contract.receiveEntrypoint = some rc → BridgedStmts rc.body)
    (hInternals : BridgedStmts contract.internalFunctions) :
    BridgedTarget (.stmts (Compiler.emitYul contract).runtimeCode) := by
  exact BridgedTarget.stmts _ (by
    simpa [Compiler.emitYul] using
      runtimeCode_bridged contract hFunctions hFallback hReceive hInternals)

private theorem execYulFuelWithBackend_eq_on_bridged_target
    (fuel : Nat) (state : YulState) (target : YulExecTarget)
    (hTarget : BridgedTarget target) :
    execYulFuelWithBackend .verity fuel state target =
    execYulFuelWithBackend .evmYulLean fuel state target := by
  induction fuel generalizing state target with
  | zero =>
      cases hTarget with
      | stmt stmt hStmt =>
          cases hStmt with
          | straight stmt hStraight =>
              exact execYulFuelWithBackend_eq_on_bridged_straight_stmt
                0 state stmt hStraight
          | block _ _ => rfl
          | if_ _ _ _ _ => rfl
          | «switch» _ _ _ _ _ _ => rfl
          | for_ _ _ _ _ _ _ _ _ => rfl
      | stmts stmts hStmts =>
          cases stmts <;> rfl
  | succ fuel ih =>
      cases hTarget with
      | stmt stmt hStmt =>
          cases hStmt with
          | straight stmt hStraight =>
              exact execYulFuelWithBackend_eq_on_bridged_straight_stmt
                (Nat.succ fuel) state stmt hStraight
          | block stmts hStmts =>
              simp only [execYulFuelWithBackend]
              exact ih state (.stmts stmts) (.stmts stmts hStmts)
          | if_ cond body hCond hBody =>
              simp only [execYulFuelWithBackend]
              rw [evalYulExprWithBackend_eq_on_bridged state cond hCond]
              cases evalYulExprWithBackend .evmYulLean state cond with
              | none => rfl
              | some v =>
                  by_cases hv : v = 0
                  · simp [hv]
                  · simp [hv]
                    exact ih state (.stmts body) (.stmts body hBody)
          | «switch» expr cases defaultCase hExpr hCases hDefault =>
              simp only [execYulFuelWithBackend]
              rw [evalYulExprWithBackend_eq_on_bridged state expr hExpr]
              cases evalYulExprWithBackend .evmYulLean state expr with
              | none => rfl
              | some v =>
                  cases hFind : cases.find? (fun x => decide (x.fst = v)) with
                  | some hit =>
                      cases hit with
                      | mk value body =>
                          simp [hFind]
                          exact ih state (.stmts body)
                            (.stmts body (hCases v value body hFind))
                  | none =>
                      cases hDefaultCase : defaultCase with
                      | none =>
                          simp [hFind]
                      | some body =>
                          simp [hFind]
                          exact ih state (.stmts body)
                            (.stmts body (hDefault body hDefaultCase))
          | for_ init cond post body hInit hCond hPost hBody =>
              simp only [execYulFuelWithBackend]
              rw [ih state (.stmts init) (.stmts init hInit)]
              cases execYulFuelWithBackend .evmYulLean fuel state (.stmts init) with
              | «continue» s' =>
                  simp only
                  rw [evalYulExprWithBackend_eq_on_bridged s' cond hCond]
                  cases evalYulExprWithBackend .evmYulLean s' cond with
                  | none => rfl
                  | some v =>
                      by_cases hv : v = 0
                      · simp [hv]
                      · simp [hv]
                        rw [ih s' (.stmts body) (.stmts body hBody)]
                        cases execYulFuelWithBackend .evmYulLean fuel s' (.stmts body) with
                        | «continue» s'' =>
                            simp only
                            rw [ih s'' (.stmts post) (.stmts post hPost)]
                            cases execYulFuelWithBackend .evmYulLean fuel s'' (.stmts post) with
                            | «continue» s''' =>
                                simp only
                                exact ih s''' (.stmt (.for_ [] cond post body))
                                  (.stmt (.for_ [] cond post body)
                                    (.for_ [] cond post body
                                      (by intro stmt hMem; cases hMem)
                                      hCond hPost hBody))
                            | «return» _ _ => rfl
                            | «stop» _ => rfl
                            | «revert» _ => rfl
                        | «return» _ _ => rfl
                        | «stop» _ => rfl
                        | «revert» _ => rfl
              | «return» _ _ => rfl
              | «stop» _ => rfl
              | «revert» _ => rfl
      | stmts stmts hStmts =>
          cases stmts with
          | nil => rfl
          | cons stmt rest =>
              have hStmt : BridgedStmt stmt := hStmts stmt (by simp)
              have hRest : BridgedStmts rest := by
                intro s hs
                exact hStmts s (by simp [hs])
              simp only [execYulFuelWithBackend]
              rw [ih state (.stmt stmt) (.stmt stmt hStmt)]
              cases execYulFuelWithBackend .evmYulLean fuel state (.stmt stmt) with
              | «continue» s' =>
                  simp only
                  exact ih s' (.stmts rest) (.stmts rest hRest)
              | «return» _ _ => rfl
              | «stop» _ => rfl
              | «revert» _ => rfl

private theorem execYulFuelWithBackend_eq_on_bridged_stmt
    (fuel : Nat) (state : YulState) (stmt : Compiler.Yul.YulStmt)
    (hStmt : BridgedStmt stmt) :
    execYulFuelWithBackend .verity fuel state (.stmt stmt) =
    execYulFuelWithBackend .evmYulLean fuel state (.stmt stmt) :=
  execYulFuelWithBackend_eq_on_bridged_target fuel state (.stmt stmt)
    (.stmt stmt hStmt)

private theorem execYulFuelWithBackend_eq_on_bridged_stmts
    (fuel : Nat) (state : YulState) (stmts : List Compiler.Yul.YulStmt)
    (hStmts : BridgedStmts stmts) :
    execYulFuelWithBackend .verity fuel state (.stmts stmts) =
    execYulFuelWithBackend .evmYulLean fuel state (.stmts stmts) :=
  execYulFuelWithBackend_eq_on_bridged_target fuel state (.stmts stmts)
    (.stmts stmts hStmts)

private theorem emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies
    (fuel : Nat) (state : YulState) (contract : Compiler.IRContract)
    (_hFunctions : ∀ fn, fn ∈ contract.functions → BridgedStmts fn.body)
    (_hFallback : ∀ fb, contract.fallbackEntrypoint = some fb → BridgedStmts fb.body)
    (_hReceive : ∀ rc, contract.receiveEntrypoint = some rc → BridgedStmts rc.body)
    (_hInternals : BridgedStmts contract.internalFunctions) :
    legacyExecYulFuel fuel state (.stmts (Compiler.emitYul contract).runtimeCode) =
    execYulFuelWithBackend .evmYulLean fuel state
      (.stmts (Compiler.emitYul contract).runtimeCode) := by
  exact (execYulFuelWithBackend_evmYulLean_eq fuel state
    (.stmts (Compiler.emitYul contract).runtimeCode)).symm

private noncomputable def execYulStmtsWithBackend
    (backend : BuiltinBackend) (state : YulState) (stmts : List Compiler.Yul.YulStmt) :
    YulExecResult :=
  execYulFuelWithBackend backend (sizeOf stmts + 1) state (.stmts stmts)

private noncomputable def interpretYulRuntimeWithBackend
    (backend : BuiltinBackend) (runtimeCode : List Compiler.Yul.YulStmt)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (events : List (List Nat) := []) :
    YulResult :=
  let initialState := YulState.initial tx storage events
  yulResultOfExecWithRollback initialState
    (execYulFuelWithBackend backend (sizeOf runtimeCode + 1) initialState
      (.stmts runtimeCode))

private theorem interpretYulRuntimeWithBackend_evmYulLean_eq
    (runtimeCode : List Compiler.Yul.YulStmt) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (events : List (List Nat) := []) :
    interpretYulRuntimeWithBackend .evmYulLean runtimeCode tx storage events =
    interpretYulRuntime runtimeCode tx storage events := by
  unfold interpretYulRuntimeWithBackend interpretYulRuntime
  unfold execYulStmts execYulStmtsFuel
  change
    yulResultOfExecWithRollback (YulState.initial tx storage events)
      (execYulFuelWithBackend .evmYulLean (sizeOf runtimeCode + 1)
        (YulState.initial tx storage events) (.stmts runtimeCode)) =
    match legacyExecYulFuel (sizeOf runtimeCode + 1)
        (YulState.initial tx storage events) (.stmts runtimeCode) with
    | .continue s =>
        { success := true, returnValue := s.returnValue, finalStorage := s.storage,
          finalMappings := Compiler.Proofs.storageAsMappings s.storage, events := s.events }
    | .return v s =>
        { success := true, returnValue := some v, finalStorage := s.storage,
          finalMappings := Compiler.Proofs.storageAsMappings s.storage, events := s.events }
    | .stop s =>
        { success := true, returnValue := none, finalStorage := s.storage,
          finalMappings := Compiler.Proofs.storageAsMappings s.storage, events := s.events }
    | .revert _ =>
        { success := false, returnValue := none, finalStorage := storage,
          finalMappings := Compiler.Proofs.storageAsMappings storage, events := events }
  rw [execYulFuelWithBackend_evmYulLean_eq]
  cases legacyExecYulFuel (sizeOf runtimeCode + 1) (YulState.initial tx storage events)
      (.stmts runtimeCode) <;> rfl

private theorem interpretYulFromIR_evmYulLean_eq_on_bridged_bodies
    (contract : Compiler.IRContract) (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (_hFunctions : ∀ fn, fn ∈ contract.functions → BridgedStmts fn.body)
    (_hFallback : ∀ fb, contract.fallbackEntrypoint = some fb → BridgedStmts fb.body)
    (_hReceive : ∀ rc, contract.receiveEntrypoint = some rc → BridgedStmts rc.body)
    (_hInternals : BridgedStmts contract.internalFunctions) :
  interpretYulFromIR contract tx state =
    interpretYulRuntimeWithBackend .evmYulLean
      (Compiler.emitYul contract).runtimeCode (YulTransaction.ofIR tx)
      state.storage state.events := by
  unfold interpretYulFromIR
  exact (interpretYulRuntimeWithBackend_evmYulLean_eq
    (Compiler.emitYul contract).runtimeCode (YulTransaction.ofIR tx)
    state.storage (events := state.events)).symm

/-! ## Phase 4 Completion Summary

### What this module establishes:
1. **`backends_agree_on_bridged_builtins`**: Pointwise backend equivalence for
   the full bridged-builtin set at the `evalBuiltinCallWithBackendContext`
   level. For every `func ∈ bridgedBuiltins`, `.verity` and `.evmYulLean`
   return the same result. The dispatch proof and all per-builtin bridge dependencies are sorry-free.
2. **`evalYulExpr_evmYulLean_eq_on_bridged`**: Expression-level backend
   equivalence for `BridgedExpr`, covering literals, identifiers, nested calls
   to bridged builtins, and backend-independent `tload`/`mload`.
3. **Backend-parameterized statement executor**: `execYulFuelWithBackend` is a
   backend-parameterized mirror of `legacyExecYulFuel`, providing the executor surface
   used by the statement-level equivalence proofs below.
4. **`execYulFuelWithBackend_{let,assign}_eq_on_bridged`**: First
   statement-level backend-equivalence theorems — `.let_ n v` and `.assign n v`
   produce identical results under `.verity` and `.evmYulLean` when `v` is a
   `BridgedExpr`. These are narrow helpers used by the broader statement-list
   and recursive-target predicates below.
5. **`execYulFuelWithBackend_eq_on_bridged_straight_stmts`**: Statement-level
   backend equivalence for straight-line statement lists whose expression
   dependencies satisfy `BridgedExpr`; the unsupported `.letMany` form is also
   covered because both backends revert identically.
6. **`execYulFuelWithBackend_block_eq_on_bridged_straight_stmts`**: The `.block`
   statement constructor preserves that straight-line list equivalence when its
   body is a `BridgedStraightStmts` list.
7. **`execYulFuelWithBackend_if_eq_on_bridged_body`**: The `.if_` statement
   constructor preserves backend equivalence when its condition is a
   `BridgedExpr` and its body is a `BridgedStraightStmts` list.
8. **`execYulFuelWithBackend_switch_eq_on_bridged_cases`**: The `.switch`
   statement constructor preserves backend equivalence when its scrutinee is a
   `BridgedExpr`, every selectable case body satisfies `BridgedStraightStmts`,
   and the optional default body is straight-line when present.
9. **`execYulFuelWithBackend_for_eq_on_bridged_parts`**: The `.for_`
   statement constructor preserves backend equivalence when its init/body/post
   lists are `BridgedStraightStmts` and its condition is a `BridgedExpr`.
10. **`execYulFuelWithBackend_eq_on_bridged_target`**: Recursive
    statement/statement-list backend equivalence for targets constrained by
    `BridgedTarget`, whose nested statements satisfy `BridgedStmt`.
11. **`emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies`**: Composes
    emitted runtime-wrapper closure with recursive target equivalence to state
    that Verity `legacyExecYulFuel` equals the EVMYulLean backend executor for
    `emitYul` runtime code when its embedded bodies are bridged.
12. The former contract-level EVMYulLean fuel-wrapper retarget theorem has
    been removed from this module. The remaining facts are transition/regression
    evidence for the bridged proof-interpreter fragment, while public
    compiler-correctness theorems are expected to target native dispatcher
    execution through `EvmYul.Yul.callDispatcher`.

### Trust boundary:
Expressions constrained by `BridgedExpr`, straight-line statement lists
constrained by `BridgedStraightStmts`, and recursive statement targets
constrained by `BridgedTarget` inherit EVMYulLean semantics. Contract-level
proof-interpreter preservation is not exported from this module as public
compiler-correctness authority. The remaining scope limit is the
external-call/function-table family carved out by `BridgedSafeStmts`.
-/

end Compiler.Proofs.YulGeneration.Backends
