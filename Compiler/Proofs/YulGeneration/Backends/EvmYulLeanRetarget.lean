/-
  Phase 4: Retarget the theorem stack to EVMYulLean.

  This module proves that the Verity Yul semantics — currently targeting the
  `.verity` builtin backend — are equivalent to execution under the `.evmYulLean`
  backend for programs that use only bridged builtins.

  **Key theorem**: `backends_agree_on_bridged_builtins` shows that
  `evalBuiltinCallWithBackendContext .verity ... func args =
   evalBuiltinCallWithBackendContext .evmYulLean ... func args`
  for every `func ∈ bridgedBuiltins`.

  This module also proves the expression-level lift for `BridgedExpr`:
  `evalYulExpr_evmYulLean_eq_on_bridged`, plus the recursive target lift
  `execYulFuelWithBackend_eq_on_bridged_target` for `BridgedTarget`
  executions. The remaining whole-program lift requires proving generated Yul
  targets satisfy `BridgedTarget`/`BridgedStmt` and composing that theorem into
  Layer 3; see the module summary at the bottom of this file.

  **Trust boundary shift (pointwise)**: For any builtin call using a bridged
  name, the trust boundary moves from "Verity's custom Yul builtin semantics
  are correct" to "EVMYulLean's builtin semantics match the EVM" (backed by
  upstream conformance tests). Whole-program guarantees still require the
  pending Layer-3 composition.

  Run: lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanRetarget
-/

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

This avoids unfolding the expensive `evalBuiltinCallWithContext` if-chain. -/

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
-- `storage : Nat → Nat` lookup used by Verity's `evalBuiltinCallWithContext`)
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
The 2 sorry-dependent builtins (smod, sar) contribute
to this through their sorry-backed bridge lemmas in `EvmYulLeanBridgeLemmas.lean`.
-/

/-- For any builtin in `bridgedBuiltins`, the `.verity` and `.evmYulLean` backends
    produce identical results under `evalBuiltinCallWithBackendContext`.

    This is the master backend equivalence theorem for Phase 4 retargeting.
    It composes the 36 per-builtin bridge theorems into a single dispatch proof.
    Every builtin handled by `evalBuiltinCallWithContext` is now bridged, so
    `unbridgedBuiltins` is empty.

    This theorem is sorry-free at the dispatch level; the 2 remaining sorry's
    (smod, sar) are isolated in the per-builtin bridge lemmas
    in `EvmYulLeanBridgeLemmas.lean`. -/
theorem backends_agree_on_bridged_builtins
    (storage : Nat → Nat) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
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

def allowedExprCallName (func : String) : Prop :=
  func ∈ bridgedBuiltins ∨ func = "tload" ∨ func = "mload" ∨ func = "keccak256"

set_option maxHeartbeats 1000000 in
/-- `keccak256` is not handled by Verity's `evalBuiltinCallWithContext` (it
    falls through the 35-case if-else chain to the final `else none`) and is
    not handled by the EVMYulLean adapter (`evalBuiltinCallViaEvmYulLean` and
    `evalPureBuiltinViaEvmYulLean` both default to `none` for unknown funcs).
    Both backends therefore agree trivially by returning `none`. This makes
    `keccak256` a safe "bridged by absence" expression name: the Yul
    interpreter cannot compute a hash under either backend, and any Yul
    program that evaluates `keccak256(...)` through this interpreter halts
    identically on both sides.  -/
private theorem backends_agree_on_keccak256
    (storage : Nat → Nat)
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

inductive BridgedExpr : Compiler.Yul.YulExpr → Prop
  | lit (n : Nat) : BridgedExpr (.lit n)
  | hex (n : Nat) : BridgedExpr (.hex n)
  | str (s : String) : BridgedExpr (.str s)
  | ident (name : String) : BridgedExpr (.ident name)
  | call (func : String) (args : List Compiler.Yul.YulExpr)
      (hName : allowedExprCallName func)
      (hArgs : ∀ arg ∈ args, BridgedExpr arg) :
      BridgedExpr (.call func args)

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

private theorem evalYulExprWithBackend_verity_eq
    (state : YulState) (expr : Compiler.Yul.YulExpr) :
    evalYulExprWithBackend .verity state expr = evalYulExpr state expr := by
  cases expr with
  | lit _ => simp [evalYulExprWithBackend, evalYulExpr]
  | hex _ => simp [evalYulExprWithBackend, evalYulExpr]
  | str _ => simp [evalYulExprWithBackend, evalYulExpr]
  | ident _ => simp [evalYulExprWithBackend, evalYulExpr]
  | call func args =>
      simp only [evalYulExprWithBackend, evalYulExpr, evalYulCallWithBackend, evalYulCall]
      rw [evalYulExprsWithBackend_verity_eq state args]
      rfl

private theorem evalYulExprsWithBackend_verity_eq
    (state : YulState) (args : List Compiler.Yul.YulExpr) :
    evalYulExprsWithBackend .verity state args = evalYulExprs state args := by
  cases args with
  | nil => simp [evalYulExprsWithBackend, evalYulExprs]
  | cons arg rest =>
      simp only [evalYulExprsWithBackend, evalYulExprs]
      rw [evalYulExprWithBackend_verity_eq state arg,
        evalYulExprsWithBackend_verity_eq state rest]

end

mutual

theorem evalYulExprWithBackend_eq_on_bridged
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

theorem evalYulExpr_evmYulLean_eq_on_bridged
    (state : YulState) (expr : Compiler.Yul.YulExpr) (hExpr : BridgedExpr expr) :
    evalYulExpr state expr =
    evalYulExprWithBackend .evmYulLean state expr := by
  have h := evalYulExprWithBackend_eq_on_bridged state expr hExpr
  rw [← evalYulExprWithBackend_verity_eq state expr]
  exact h

/-! ## Statement-level backend-parameterized executor (scaffolding)

`execYulFuelWithBackend` mirrors `execYulFuel` from `Semantics.lean` but routes
each expression evaluation through `evalYulExprWithBackend backend`. This is
infrastructure for the pending whole-program retargeting. Bridging `.verity`
and `.evmYulLean` on bridged statement targets is deferred to a follow-up.
-/

def execYulFuelWithBackend (backend : BuiltinBackend) :
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

/-- The backend-parameterized executor recovers `execYulFuel` at the `.verity`
    backend. Statement-level analogue of `evalYulExprWithBackend_verity_eq` —
    this is the correctness obligation that justifies replacing every
    `execYulFuel` call in upstream theorems with
    `execYulFuelWithBackend .verity`. -/
theorem execYulFuelWithBackend_verity_eq
    (fuel : Nat) (state : YulState) (target : YulExecTarget) :
    execYulFuelWithBackend .verity fuel state target =
    execYulFuel fuel state target := by
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
              simp only [execYulFuelWithBackend, execYulFuel,
                evalYulExprWithBackend_verity_eq,
                evalYulExprsWithBackend_verity_eq, ih]
              try rfl))
      | stmts ss =>
          cases ss <;> (
            try rfl
            all_goals (
              simp only [execYulFuelWithBackend, execYulFuel, ih]
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

theorem execYulFuelWithBackend_let_eq_on_bridged
    (fuel : Nat) (state : YulState) (name : String)
    (value : Compiler.Yul.YulExpr) (hValue : BridgedExpr value) :
    execYulFuelWithBackend .verity fuel state (.stmt (.let_ name value)) =
    execYulFuelWithBackend .evmYulLean fuel state (.stmt (.let_ name value)) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [execYulFuelWithBackend]
      rw [evalYulExprWithBackend_eq_on_bridged state value hValue]

theorem execYulFuelWithBackend_assign_eq_on_bridged
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

inductive BridgedStraightStmt : Compiler.Yul.YulStmt → Prop
  | comment (text : String) : BridgedStraightStmt (.comment text)
  | let_ (name : String) (value : Compiler.Yul.YulExpr)
      (hValue : BridgedExpr value) :
      BridgedStraightStmt (.let_ name value)
  | letMany (names : List String) (value : Compiler.Yul.YulExpr) :
      BridgedStraightStmt (.letMany names value)
  | assign (name : String) (value : Compiler.Yul.YulExpr)
      (hValue : BridgedExpr value) :
      BridgedStraightStmt (.assign name value)
  | leave : BridgedStraightStmt .leave
  | expr_sstore_mapping (baseExpr keyExpr valExpr : Compiler.Yul.YulExpr)
      (hBase : BridgedExpr baseExpr) (hKey : BridgedExpr keyExpr)
      (hVal : BridgedExpr valExpr) :
      BridgedStraightStmt
        (.expr (.call "sstore" [.call "mappingSlot" [baseExpr, keyExpr], valExpr]))
  /-- `sstore(lit slot, valExpr)` for a literal slot. Covers the common
  direct-storage-write shape emitted by `compileSetStorage` for unpacked
  single-slot fields at a known slot index. The executor's inner match on
  `.lit slot` falls through to the generic `sstore` branch (it is not a
  `mappingSlot` call), which only differs between backends via
  `evalYulExprWithBackend` on `.lit slot` / `valExpr` — both bridged. -/
  | expr_sstore_lit (slot : Nat) (valExpr : Compiler.Yul.YulExpr)
      (hVal : BridgedExpr valExpr) :
      BridgedStraightStmt (.expr (.call "sstore" [.lit slot, valExpr]))
  /-- `sstore(ident slotName, valExpr)` for compiler-emitted writes whose
  storage slot has already been bound to a local variable, e.g. struct-member
  and compatibility write helpers. -/
  | expr_sstore_ident (slotName : String) (valExpr : Compiler.Yul.YulExpr)
      (hVal : BridgedExpr valExpr) :
      BridgedStraightStmt (.expr (.call "sstore" [.ident slotName, valExpr]))
  | expr_mstore (offsetExpr valExpr : Compiler.Yul.YulExpr)
      (hOffset : BridgedExpr offsetExpr) (hVal : BridgedExpr valExpr) :
      BridgedStraightStmt (.expr (.call "mstore" [offsetExpr, valExpr]))
  | expr_tstore (offsetExpr valExpr : Compiler.Yul.YulExpr)
      (hOffset : BridgedExpr offsetExpr) (hVal : BridgedExpr valExpr) :
      BridgedStraightStmt (.expr (.call "tstore" [offsetExpr, valExpr]))
  | expr_stop : BridgedStraightStmt (.expr (.call "stop" []))
  | expr_return (offsetExpr sizeExpr : Compiler.Yul.YulExpr)
      (hOffset : BridgedExpr offsetExpr) (hSize : BridgedExpr sizeExpr) :
      BridgedStraightStmt (.expr (.call "return" [offsetExpr, sizeExpr]))
  | expr_revert (offsetExpr sizeExpr : Compiler.Yul.YulExpr) :
      BridgedStraightStmt (.expr (.call "revert" [offsetExpr, sizeExpr]))
  /-- `logN(args...)` for `N ∈ {0,1,2,3,4}`. The Yul semantics dispatches log
  calls via backend-agnostic `applyYulLogCall?` (takes only state + func +
  evaluated argument values), so both backends diverge only on the argument
  evaluation step which is closed by `BridgedExpr` on each argument. -/
  | expr_log (func : String) (args : List Compiler.Yul.YulExpr)
      (hLog : isYulLogName func = true)
      (hArgs : ∀ arg ∈ args, BridgedExpr arg) :
      BridgedStraightStmt (.expr (.call func args))
  | funcDef (name : String) (params rets : List String)
      (body : List Compiler.Yul.YulStmt) :
      BridgedStraightStmt (.funcDef name params rets body)

def BridgedStraightStmts (stmts : List Compiler.Yul.YulStmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedStraightStmt stmt

/-! ### List-level convenience helpers for `BridgedStraightStmts`

Analogues of `BridgedStmts_nil`/`_cons`/`_append` (defined further below for
the recursive `BridgedStmt` predicate) so that callers composing scalar-event
emission fragments or other compiler-emitted concatenated straight-line lists
can piece them together without unfolding the membership definition at each
call site. -/

theorem BridgedStraightStmts_nil : BridgedStraightStmts [] := by
  intro stmt hMem
  cases hMem

theorem BridgedStraightStmts_cons {stmt : Compiler.Yul.YulStmt}
    {stmts : List Compiler.Yul.YulStmt}
    (hStmt : BridgedStraightStmt stmt) (hStmts : BridgedStraightStmts stmts) :
    BridgedStraightStmts (stmt :: stmts) := by
  intro s hMem
  cases hMem with
  | head => exact hStmt
  | tail _ hTail => exact hStmts s hTail

theorem BridgedStraightStmts_append {xs ys : List Compiler.Yul.YulStmt}
    (hXs : BridgedStraightStmts xs) (hYs : BridgedStraightStmts ys) :
    BridgedStraightStmts (xs ++ ys) := by
  intro stmt hMem
  simp only [List.mem_append] at hMem
  cases hMem with
  | inl h => exact hXs stmt h
  | inr h => exact hYs stmt h

theorem BridgedStraightStmts_singleton {stmt : Compiler.Yul.YulStmt}
    (hStmt : BridgedStraightStmt stmt) : BridgedStraightStmts [stmt] :=
  BridgedStraightStmts_cons hStmt BridgedStraightStmts_nil

/-- A list of `(offset, value)` expression pairs where each component is a
    `BridgedExpr` maps to a `BridgedStraightStmts` list of `mstore(offset,
    value)` statements. Directly supports the scalar event-emission compiler
    pattern where `sigStores` and `unindexedStores` are both computed as
    `List YulStmt` via `.map` over pair-shaped data. -/
theorem BridgedStraightStmts_map_mstore
    (pairs : List (Compiler.Yul.YulExpr × Compiler.Yul.YulExpr))
    (hPairs : ∀ p ∈ pairs, BridgedExpr p.1 ∧ BridgedExpr p.2) :
    BridgedStraightStmts
      (pairs.map fun p =>
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "mstore" [p.1, p.2])) := by
  induction pairs with
  | nil => exact BridgedStraightStmts_nil
  | cons p rest ih =>
      have hHead : BridgedExpr p.1 ∧ BridgedExpr p.2 := hPairs p (by simp)
      have hRest : ∀ q ∈ rest, BridgedExpr q.1 ∧ BridgedExpr q.2 := by
        intro q hq
        exact hPairs q (by simp [hq])
      exact BridgedStraightStmts_cons
        (BridgedStraightStmt.expr_mstore p.1 p.2 hHead.1 hHead.2)
        (ih hRest)

/-- Analogue of `BridgedStraightStmts_map_mstore` for the transient-store
    variant. Compiler helpers that target transient storage (EIP-1153)
    occasionally emit concatenated `tstore` fragments, and having the
    `map`-shaped helper pre-proved avoids per-fragment list recursion. -/
theorem BridgedStraightStmts_map_tstore
    (pairs : List (Compiler.Yul.YulExpr × Compiler.Yul.YulExpr))
    (hPairs : ∀ p ∈ pairs, BridgedExpr p.1 ∧ BridgedExpr p.2) :
    BridgedStraightStmts
      (pairs.map fun p =>
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "tstore" [p.1, p.2])) := by
  induction pairs with
  | nil => exact BridgedStraightStmts_nil
  | cons p rest ih =>
      have hHead : BridgedExpr p.1 ∧ BridgedExpr p.2 := hPairs p (by simp)
      have hRest : ∀ q ∈ rest, BridgedExpr q.1 ∧ BridgedExpr q.2 := by
        intro q hq
        exact hPairs q (by simp [hq])
      exact BridgedStraightStmts_cons
        (BridgedStraightStmt.expr_tstore p.1 p.2 hHead.1 hHead.2)
        (ih hRest)

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

theorem execYulFuelWithBackend_eq_on_bridged_straight_stmts
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
theorem execYulFuelWithBackend_block_eq_on_bridged_straight_stmts
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
theorem execYulFuelWithBackend_if_eq_on_bridged_body
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

def BridgedSwitchCases (cases : List (Nat × List Compiler.Yul.YulStmt)) : Prop :=
  ∀ scrutinee value body,
    cases.find? (fun x => decide (x.fst = scrutinee)) = some (value, body) →
    BridgedStraightStmts body

/-- A `.switch` with a bridged scrutinee and straight-line selected bodies
    preserves backend equivalence. The predicate only needs to cover bodies that
    can actually be selected by `find?`; the default branch is handled
    separately. Recursive switch bodies and loops still need the broader
    statement predicate/induction. -/
theorem execYulFuelWithBackend_switch_eq_on_bridged_cases
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
theorem execYulFuelWithBackend_for_eq_on_bridged_parts
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

inductive BridgedStmt : Compiler.Yul.YulStmt → Prop
  | straight (stmt : Compiler.Yul.YulStmt)
      (hStmt : BridgedStraightStmt stmt) :
      BridgedStmt stmt
  | block (stmts : List Compiler.Yul.YulStmt)
      (hStmts : ∀ stmt ∈ stmts, BridgedStmt stmt) :
      BridgedStmt (.block stmts)
  | if_ (cond : Compiler.Yul.YulExpr) (body : List Compiler.Yul.YulStmt)
      (hCond : BridgedExpr cond)
      (hBody : ∀ stmt ∈ body, BridgedStmt stmt) :
      BridgedStmt (.if_ cond body)
  | «switch» (expr : Compiler.Yul.YulExpr)
      (cases : List (Nat × List Compiler.Yul.YulStmt))
      (defaultCase : Option (List Compiler.Yul.YulStmt))
      (hExpr : BridgedExpr expr)
      (hCases : ∀ scrutinee value body,
        cases.find? (fun x => decide (x.fst = scrutinee)) = some (value, body) →
        ∀ stmt ∈ body, BridgedStmt stmt)
      (hDefault : ∀ body, defaultCase = some body →
        ∀ stmt ∈ body, BridgedStmt stmt) :
      BridgedStmt (.switch expr cases defaultCase)
  | for_ (init : List Compiler.Yul.YulStmt) (cond : Compiler.Yul.YulExpr)
      (post body : List Compiler.Yul.YulStmt)
      (hInit : ∀ stmt ∈ init, BridgedStmt stmt)
      (hCond : BridgedExpr cond)
      (hPost : ∀ stmt ∈ post, BridgedStmt stmt)
      (hBody : ∀ stmt ∈ body, BridgedStmt stmt) :
      BridgedStmt (.for_ init cond post body)

def BridgedStmts (stmts : List Compiler.Yul.YulStmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedStmt stmt

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

theorem BridgedStmts_nil : BridgedStmts [] := by
  intro stmt hMem
  cases hMem

theorem BridgedStmts_cons {stmt : Compiler.Yul.YulStmt}
    {stmts : List Compiler.Yul.YulStmt}
    (hStmt : BridgedStmt stmt) (hStmts : BridgedStmts stmts) :
    BridgedStmts (stmt :: stmts) := by
  intro s hMem
  cases hMem with
  | head => exact hStmt
  | tail _ hTail => exact hStmts s hTail

theorem BridgedStmts_append {xs ys : List Compiler.Yul.YulStmt}
    (hXs : BridgedStmts xs) (hYs : BridgedStmts ys) :
    BridgedStmts (xs ++ ys) := by
  intro stmt hMem
  simp only [List.mem_append] at hMem
  cases hMem with
  | inl h => exact hXs stmt h
  | inr h => exact hYs stmt h

/-- Public singleton helper: if `hStmt : BridgedStmt stmt` then the one-element
    list `[stmt]` satisfies `BridgedStmts`. Matches `BridgedStraightStmts_singleton`
    for list composition of recursive-statement lists. -/
theorem BridgedStmts_singleton {stmt : Compiler.Yul.YulStmt}
    (hStmt : BridgedStmt stmt) : BridgedStmts [stmt] :=
  BridgedStmts_cons hStmt BridgedStmts_nil

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

/-- `keccak256(offsetExpr, sizeExpr)` with bridged argument expressions is a
    `BridgedExpr`. Both backends compute `abstractKeccakMemorySlice` directly
    in `evalYulCallWithBackend` / `evalYulCall` after the PR #1732 proven-fragment
    expansion, so this is a genuine convenience helper rather than an axiom
    wrapper. Useful for closing event-emission bodies (scalar `emit` compiles
    a `let __evt_topic0 := keccak256(__evt_ptr, sigBytes.length)` binding). -/
theorem bridgedExpr_keccak256 (offsetExpr sizeExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hSize : BridgedExpr sizeExpr) :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "keccak256" [offsetExpr, sizeExpr]) := by
  refine BridgedExpr.call "keccak256" _ (Or.inr (Or.inr (Or.inr rfl))) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · exact hOffset
  · exact hSize

/-- `mload(offsetExpr)` with a bridged `offsetExpr` is a `BridgedExpr`. Both
    backends already include `mload` directly in `evalYulCallWithBackend` /
    `evalYulCall` (single-slot memory read by Verity's free-memory model).
    Useful for closing compiler-emitted `let __evt_ptr := mload(0x40)` shapes
    at the head of scalar `emit` bodies, and for any prologue helper that
    consults the free-memory pointer. -/
theorem bridgedExpr_mload (offsetExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "mload" [offsetExpr]) := by
  refine BridgedExpr.call "mload" _ (Or.inr (Or.inr (Or.inl rfl))) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst hMem
  exact hOffset

/-- `tload(slotExpr)` analogue of `bridgedExpr_mload`. EIP-1153 transient
    storage reads are in `allowedExprCallName` and share the same two-backend
    `tload` branch in `evalYulCallWithBackend`. Having the helper available
    keeps tload-consuming Yul prologues composable under `BridgedExpr`. -/
theorem bridgedExpr_tload (slotExpr : Compiler.Yul.YulExpr)
    (hSlot : BridgedExpr slotExpr) :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "tload" [slotExpr]) := by
  refine BridgedExpr.call "tload" _ (Or.inr (Or.inl rfl)) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst hMem
  exact hSlot

/-- `let name := mload(offsetExpr)` with a bridged `offsetExpr` is a
    `BridgedStraightStmt`. Composes `BridgedStraightStmt.let_` with
    `bridgedExpr_mload`. Directly matches the `let __evt_ptr := mload(0x40)`
    prologue emitted at the head of compiled scalar `emit` bodies. -/
theorem bridgedStraightStmt_let_mload (name : String)
    (offsetExpr : Compiler.Yul.YulExpr) (hOffset : BridgedExpr offsetExpr) :
    BridgedStraightStmt
      (.let_ name (Compiler.Yul.YulExpr.call "mload" [offsetExpr])) :=
  BridgedStraightStmt.let_ name _ (bridgedExpr_mload offsetExpr hOffset)

/-- `let name := tload(slotExpr)` analogue of `bridgedStraightStmt_let_mload`
    for EIP-1153 transient storage reads. -/
theorem bridgedStraightStmt_let_tload (name : String)
    (slotExpr : Compiler.Yul.YulExpr) (hSlot : BridgedExpr slotExpr) :
    BridgedStraightStmt
      (.let_ name (Compiler.Yul.YulExpr.call "tload" [slotExpr])) :=
  BridgedStraightStmt.let_ name _ (bridgedExpr_tload slotExpr hSlot)

/-- `let name := keccak256(offsetExpr, sizeExpr)` with bridged operands is a
    `BridgedStraightStmt`. Composes `BridgedStraightStmt.let_` with
    `bridgedExpr_keccak256`. Matches the `let __evt_topic0 := keccak256(...)`
    binding inside compiled scalar `emit` bodies. -/
theorem bridgedStraightStmt_let_keccak256 (name : String)
    (offsetExpr sizeExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hSize : BridgedExpr sizeExpr) :
    BridgedStraightStmt
      (.let_ name
        (Compiler.Yul.YulExpr.call "keccak256" [offsetExpr, sizeExpr])) :=
  BridgedStraightStmt.let_ name _
    (bridgedExpr_keccak256 offsetExpr sizeExpr hOffset hSize)

/-- `name := mload(offsetExpr)` analogue of `bridgedStraightStmt_let_mload` for
    reassignment to an already-declared local (e.g. `retVal := mload(ptr)`
    in a return-epilogue). -/
theorem bridgedStraightStmt_assign_mload (name : String)
    (offsetExpr : Compiler.Yul.YulExpr) (hOffset : BridgedExpr offsetExpr) :
    BridgedStraightStmt
      (.assign name (Compiler.Yul.YulExpr.call "mload" [offsetExpr])) :=
  BridgedStraightStmt.assign name _ (bridgedExpr_mload offsetExpr hOffset)

/-- `name := tload(slotExpr)` analogue of `bridgedStraightStmt_let_tload`. -/
theorem bridgedStraightStmt_assign_tload (name : String)
    (slotExpr : Compiler.Yul.YulExpr) (hSlot : BridgedExpr slotExpr) :
    BridgedStraightStmt
      (.assign name (Compiler.Yul.YulExpr.call "tload" [slotExpr])) :=
  BridgedStraightStmt.assign name _ (bridgedExpr_tload slotExpr hSlot)

/-- `name := keccak256(offsetExpr, sizeExpr)` analogue of
    `bridgedStraightStmt_let_keccak256` for reassignment contexts. -/
theorem bridgedStraightStmt_assign_keccak256 (name : String)
    (offsetExpr sizeExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hSize : BridgedExpr sizeExpr) :
    BridgedStraightStmt
      (.assign name
        (Compiler.Yul.YulExpr.call "keccak256" [offsetExpr, sizeExpr])) :=
  BridgedStraightStmt.assign name _
    (bridgedExpr_keccak256 offsetExpr sizeExpr hOffset hSize)

/-- Convenience constructor that lifts `expr_log` through the `isYulLogName`
    hypothesis for any of the five Yul log mnemonics. Callers outside this file
    can produce `BridgedStraightStmt` log emissions without restating the
    `isYulLogName` boolean obligation. Each emitted `logN` from the PR #1732
    proven-fragment dispatch table now has a closed bridged counterpart. -/
theorem bridgedStraightStmt_log_of_bridged_args
    (func : String) (args : List Compiler.Yul.YulExpr)
    (hLog : isYulLogName func = true)
    (hArgs : ∀ arg ∈ args, BridgedExpr arg) :
    BridgedStraightStmt (.expr (.call func args)) :=
  BridgedStraightStmt.expr_log func args hLog hArgs

/-- `BridgedStraightStmt` lifts to `BridgedStmt` via the `straight` ctor; this
    is a thin convenience wrapper so that callers can chain a `logN` emission
    (or any other straight-line statement) directly into a recursive body
    context without retyping `BridgedStmt.straight _`. -/
theorem bridgedStmt_of_bridgedStraightStmt {stmt : Compiler.Yul.YulStmt}
    (hStmt : BridgedStraightStmt stmt) : BridgedStmt stmt :=
  BridgedStmt.straight stmt hStmt

/-- List-level lift: any list satisfying `BridgedStraightStmts` also satisfies
    the recursive `BridgedStmts` predicate, since `BridgedStraightStmt` lifts
    pointwise via `bridgedStmt_of_bridgedStraightStmt`. Useful when a compiler
    fragment emits a pure-straight segment (e.g. the `sigStores` /
    `unindexedStores` lists inside scalar `emit` bodies) that needs to slot
    into a recursive-statement body context. -/
theorem BridgedStmts_of_BridgedStraightStmts
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStraightStmts stmts) :
    BridgedStmts stmts := by
  intro stmt hMem
  exact bridgedStmt_of_bridgedStraightStmt (hStmts stmt hMem)

private theorem bridgedStmt_revert_zero :
    BridgedStmt
      (Compiler.Yul.YulStmt.expr
        (Compiler.Yul.YulExpr.call "revert"
          [Compiler.Yul.YulExpr.lit 0, Compiler.Yul.YulExpr.lit 0])) :=
  BridgedStmt.straight _
    (BridgedStraightStmt.expr_revert
      (Compiler.Yul.YulExpr.lit 0) (Compiler.Yul.YulExpr.lit 0))

theorem callvalueGuard_bridged : BridgedStmt Compiler.CodegenCommon.callvalueGuard := by
  unfold Compiler.CodegenCommon.callvalueGuard
  exact BridgedStmt.if_ _ _ bridgedExpr_callvalue
    (BridgedStmts_cons bridgedStmt_revert_zero BridgedStmts_nil)

theorem calldatasizeGuard_bridged (numParams : Nat) :
    BridgedStmt (Compiler.CodegenCommon.calldatasizeGuard numParams) := by
  unfold Compiler.CodegenCommon.calldatasizeGuard
  exact BridgedStmt.if_ _ _ (bridgedExpr_calldatasize_lt (4 + numParams * 32))
    (BridgedStmts_cons bridgedStmt_revert_zero BridgedStmts_nil)

theorem dispatchBody_bridged (payable : Bool) (label : String)
    (body : List Compiler.Yul.YulStmt) (hBody : BridgedStmts body) :
    BridgedStmts (Compiler.CodegenCommon.dispatchBody payable label body) := by
  unfold Compiler.CodegenCommon.dispatchBody
  cases payable <;>
    simp only [Bool.false_eq_true, ite_false, ite_true,
      List.singleton_append]
  · exact BridgedStmts_cons (BridgedStmt.straight _
      (BridgedStraightStmt.comment label))
      (BridgedStmts_cons callvalueGuard_bridged hBody)
  · exact BridgedStmts_cons (BridgedStmt.straight _
      (BridgedStraightStmt.comment label)) hBody

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
          exact BridgedStmts_cons bridgedStmt_revert_zero BridgedStmts_nil
      | some fb =>
          unfold Compiler.CodegenCommon.defaultDispatchCase
          exact dispatchBody_bridged fb.payable "fallback()" fb.body
            (hFallback fb rfl)
  | some rc =>
      cases fallback with
      | none =>
          unfold Compiler.CodegenCommon.defaultDispatchCase
          refine BridgedStmts_cons ?_ BridgedStmts_nil
          refine BridgedStmt.block _ ?_
          exact BridgedStmts_cons
            (BridgedStmt.straight _
              (BridgedStraightStmt.let_ "__is_empty_calldata" _ bridgedExpr_empty_calldata))
            (BridgedStmts_cons
              (BridgedStmt.if_ _ _
                (BridgedExpr.ident "__is_empty_calldata")
                (dispatchBody_bridged rc.payable "receive()" rc.body
                  (hReceive rc rfl)))
              (BridgedStmts_cons
                (BridgedStmt.if_ _ _ (bridgedExpr_iszero_ident "__is_empty_calldata")
                  (BridgedStmts_cons bridgedStmt_revert_zero BridgedStmts_nil))
                BridgedStmts_nil))
      | some fb =>
          unfold Compiler.CodegenCommon.defaultDispatchCase
          refine BridgedStmts_cons ?_ BridgedStmts_nil
          refine BridgedStmt.block _ ?_
          exact BridgedStmts_cons
            (BridgedStmt.straight _
              (BridgedStraightStmt.let_ "__is_empty_calldata" _ bridgedExpr_empty_calldata))
            (BridgedStmts_cons
              (BridgedStmt.if_ _ _
                (BridgedExpr.ident "__is_empty_calldata")
                (dispatchBody_bridged rc.payable "receive()" rc.body
                  (hReceive rc rfl)))
              (BridgedStmts_cons
                (BridgedStmt.if_ _ _ (bridgedExpr_iszero_ident "__is_empty_calldata")
                  (dispatchBody_bridged fb.payable "fallback()" fb.body
                    (hFallback fb rfl)))
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
  exact BridgedStmt.block _
    (BridgedStmts_cons
      (BridgedStmt.straight _
        (BridgedStraightStmt.let_ "__has_selector" _ bridgedExpr_has_selector))
      (BridgedStmts_cons
        (BridgedStmt.if_ _ _ (bridgedExpr_iszero_ident "__has_selector")
          (defaultDispatchCase_bridged fallback receive hFallback hReceive))
        (BridgedStmts_cons
          (BridgedStmt.if_ _ _
            (BridgedExpr.ident "__has_selector")
            (BridgedStmts_cons
              (BridgedStmt.«switch» _ _ _
                bridgedExpr_selector
                (switchCases_bridged funcs hFunctions)
                (by
                  intro body hBody
                  cases hBody
                  exact defaultDispatchCase_bridged fallback receive hFallback hReceive))
              BridgedStmts_nil))
          BridgedStmts_nil)))

theorem mappingSlotFuncAt_bridged (scratchBase : Nat) :
    BridgedStmt (Compiler.CodegenCommon.mappingSlotFuncAt scratchBase) := by
  unfold Compiler.CodegenCommon.mappingSlotFuncAt
  exact BridgedStmt.straight _
    (BridgedStraightStmt.funcDef "mappingSlot" ["baseSlot", "key"] ["slot"] _)

theorem runtimeCode_bridged
    (contract : Compiler.IRContract)
    (hFunctions : ∀ fn, fn ∈ contract.functions → BridgedStmts fn.body)
    (hFallback : ∀ fb, contract.fallbackEntrypoint = some fb → BridgedStmts fb.body)
    (hReceive : ∀ rc, contract.receiveEntrypoint = some rc → BridgedStmts rc.body)
    (hInternals : BridgedStmts contract.internalFunctions) :
    BridgedStmts (Compiler.CodegenCommon.runtimeCode contract) := by
  unfold Compiler.CodegenCommon.runtimeCode
  cases contract.usesMapping
  · exact BridgedStmts_append hInternals
      (BridgedStmts_cons
        (buildSwitch_bridged contract.functions contract.fallbackEntrypoint
          contract.receiveEntrypoint hFunctions hFallback hReceive)
        BridgedStmts_nil)
  · simp only [ite_true]
    exact BridgedStmts_cons (mappingSlotFuncAt_bridged 0)
      (BridgedStmts_append hInternals
        (BridgedStmts_cons
          (buildSwitch_bridged contract.functions contract.fallbackEntrypoint
            contract.receiveEntrypoint hFunctions hFallback hReceive)
          BridgedStmts_nil))

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

theorem execYulFuelWithBackend_eq_on_bridged_target
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

theorem execYulFuelWithBackend_eq_on_bridged_stmt
    (fuel : Nat) (state : YulState) (stmt : Compiler.Yul.YulStmt)
    (hStmt : BridgedStmt stmt) :
    execYulFuelWithBackend .verity fuel state (.stmt stmt) =
    execYulFuelWithBackend .evmYulLean fuel state (.stmt stmt) :=
  execYulFuelWithBackend_eq_on_bridged_target fuel state (.stmt stmt)
    (.stmt stmt hStmt)

theorem execYulFuelWithBackend_eq_on_bridged_stmts
    (fuel : Nat) (state : YulState) (stmts : List Compiler.Yul.YulStmt)
    (hStmts : BridgedStmts stmts) :
    execYulFuelWithBackend .verity fuel state (.stmts stmts) =
    execYulFuelWithBackend .evmYulLean fuel state (.stmts stmts) :=
  execYulFuelWithBackend_eq_on_bridged_target fuel state (.stmts stmts)
    (.stmts stmts hStmts)

theorem emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies
    (fuel : Nat) (state : YulState) (contract : Compiler.IRContract)
    (hFunctions : ∀ fn, fn ∈ contract.functions → BridgedStmts fn.body)
    (hFallback : ∀ fb, contract.fallbackEntrypoint = some fb → BridgedStmts fb.body)
    (hReceive : ∀ rc, contract.receiveEntrypoint = some rc → BridgedStmts rc.body)
    (hInternals : BridgedStmts contract.internalFunctions) :
    execYulFuel fuel state (.stmts (Compiler.emitYul contract).runtimeCode) =
    execYulFuelWithBackend .evmYulLean fuel state
      (.stmts (Compiler.emitYul contract).runtimeCode) := by
  rw [← execYulFuelWithBackend_verity_eq fuel state
    (.stmts (Compiler.emitYul contract).runtimeCode)]
  exact execYulFuelWithBackend_eq_on_bridged_target fuel state
    (.stmts (Compiler.emitYul contract).runtimeCode)
    (emitYul_runtimeCode_bridged contract hFunctions hFallback hReceive hInternals)

noncomputable def execYulStmtsWithBackend
    (backend : BuiltinBackend) (state : YulState) (stmts : List Compiler.Yul.YulStmt) :
    YulExecResult :=
  execYulFuelWithBackend backend (sizeOf stmts + 1) state (.stmts stmts)

noncomputable def interpretYulRuntimeWithBackend
    (backend : BuiltinBackend) (runtimeCode : List Compiler.Yul.YulStmt)
    (tx : YulTransaction) (storage : Nat → Nat) (events : List (List Nat) := []) :
    YulResult :=
  let initialState := YulState.initial tx storage events
  yulResultOfExecWithRollback initialState
    (execYulStmtsWithBackend backend initialState runtimeCode)

theorem interpretYulRuntimeWithBackend_verity_eq
    (runtimeCode : List Compiler.Yul.YulStmt) (tx : YulTransaction)
    (storage : Nat → Nat) (events : List (List Nat) := []) :
    interpretYulRuntimeWithBackend .verity runtimeCode tx storage events =
    interpretYulRuntime runtimeCode tx storage events := by
  unfold interpretYulRuntimeWithBackend execYulStmtsWithBackend interpretYulRuntime
  unfold execYulStmts execYulStmtsFuel
  change
    yulResultOfExecWithRollback (YulState.initial tx storage events)
      (execYulFuelWithBackend .verity (sizeOf runtimeCode + 1)
        (YulState.initial tx storage events) (.stmts runtimeCode)) =
    match execYulFuel (sizeOf runtimeCode + 1)
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
  rw [execYulFuelWithBackend_verity_eq]
  cases execYulFuel (sizeOf runtimeCode + 1) (YulState.initial tx storage events)
      (.stmts runtimeCode) <;> rfl

theorem interpretYulFromIR_evmYulLean_eq_on_bridged_bodies
    (contract : Compiler.IRContract) (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (hFunctions : ∀ fn, fn ∈ contract.functions → BridgedStmts fn.body)
    (hFallback : ∀ fb, contract.fallbackEntrypoint = some fb → BridgedStmts fb.body)
    (hReceive : ∀ rc, contract.receiveEntrypoint = some rc → BridgedStmts rc.body)
    (hInternals : BridgedStmts contract.internalFunctions) :
    interpretYulFromIR contract tx state =
    interpretYulRuntimeWithBackend .evmYulLean
      (Compiler.emitYul contract).runtimeCode (YulTransaction.ofIR tx)
      state.storage state.events := by
  unfold interpretYulFromIR
  calc
    interpretYulRuntime (Compiler.emitYul contract).runtimeCode
        (YulTransaction.ofIR tx) state.storage state.events =
      interpretYulRuntimeWithBackend .verity
        (Compiler.emitYul contract).runtimeCode (YulTransaction.ofIR tx)
        state.storage state.events := by
          exact (interpretYulRuntimeWithBackend_verity_eq
            (Compiler.emitYul contract).runtimeCode (YulTransaction.ofIR tx)
            state.storage (events := state.events)).symm
    _ = interpretYulRuntimeWithBackend .evmYulLean
        (Compiler.emitYul contract).runtimeCode (YulTransaction.ofIR tx)
        state.storage state.events := by
          unfold interpretYulRuntimeWithBackend execYulStmtsWithBackend
          change
            yulResultOfExecWithRollback
              (YulState.initial (YulTransaction.ofIR tx) state.storage state.events)
              (execYulFuelWithBackend .verity
                (sizeOf (Compiler.emitYul contract).runtimeCode + 1)
                (YulState.initial (YulTransaction.ofIR tx) state.storage state.events)
                (.stmts (Compiler.emitYul contract).runtimeCode)) =
            yulResultOfExecWithRollback
              (YulState.initial (YulTransaction.ofIR tx) state.storage state.events)
              (execYulFuelWithBackend .evmYulLean
                (sizeOf (Compiler.emitYul contract).runtimeCode + 1)
                (YulState.initial (YulTransaction.ofIR tx) state.storage state.events)
                (.stmts (Compiler.emitYul contract).runtimeCode))
          rw [execYulFuelWithBackend_verity_eq]
          rw [emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies
            (sizeOf (Compiler.emitYul contract).runtimeCode + 1)
            (YulState.initial (YulTransaction.ofIR tx) state.storage state.events)
            contract hFunctions hFallback hReceive hInternals]

theorem yulCodegen_preserves_semantics_evmYulLean
    (contract : Compiler.IRContract)
    (tx : IRTransaction)
    (initialState : IRState)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hWF : ContractWF contract)
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none)
    (hdispatchGuardSafe : ∀ fn, fn ∈ contract.functions →
      DispatchGuardsSafe fn tx)
    (hNoHasSelector : ∀ fn, fn ∈ contract.functions →
      yulStmtsNoRef "__has_selector" fn.body)
    (hHasSelectorDead : ∀ fn, fn ∈ contract.functions →
      HasSelectorDeadBridge fn.body)
    (hLoopFree : ∀ fn, fn ∈ contract.functions →
      yulStmtsLoopFree fn.body = true)
    (hbody : ∀ fn, fn ∈ contract.functions →
      resultsMatch
        (execIRFunction fn tx.args (initialState.withTx tx))
        (interpretYulBody fn tx (initialState.withTx tx)))
    (hFunctions : ∀ fn, fn ∈ contract.functions → BridgedStmts fn.body)
    (hFallback : ∀ fb, contract.fallbackEntrypoint = some fb → BridgedStmts fb.body)
    (hReceive : ∀ rc, contract.receiveEntrypoint = some rc → BridgedStmts rc.body)
    (hInternals : BridgedStmts contract.internalFunctions) :
    resultsMatch
      (interpretIR contract tx initialState)
      (interpretYulRuntimeWithBackend .evmYulLean
        (Compiler.emitYul contract).runtimeCode (YulTransaction.ofIR tx)
        initialState.storage initialState.events) := by
  have hLayer3 :=
    yulCodegen_preserves_semantics contract tx initialState
      hselector hNoWrap hWF hNoFallback hNoReceive hdispatchGuardSafe
      hNoHasSelector hHasSelectorDead hLoopFree hbody
  rw [← interpretYulFromIR_evmYulLean_eq_on_bridged_bodies
    contract tx initialState hFunctions hFallback hReceive hInternals]
  exact hLayer3

/-! ## Phase 4 Completion Summary

### What this module establishes:
1. **`backends_agree_on_bridged_builtins`**: Pointwise backend equivalence for
   the full bridged-builtin set at the `evalBuiltinCallWithBackendContext`
   level. For every `func ∈ bridgedBuiltins`, `.verity` and `.evmYulLean`
   return the same result. The dispatch proof is sorry-free; the 2 sorry-backed
   core equivalences (smod, sar) are isolated in `EvmYulLeanBridgeLemmas.lean`.
2. **`evalYulExpr_evmYulLean_eq_on_bridged`**: Expression-level backend
   equivalence for `BridgedExpr`, covering literals, identifiers, nested calls
   to bridged builtins, and backend-independent `tload`/`mload`.
3. **Statement-executor scaffolding**: `execYulFuelWithBackend` is a
   backend-parameterized mirror of `execYulFuel`, providing the executor surface
   needed for statement-level induction.
4. **`execYulFuelWithBackend_{let,assign}_eq_on_bridged`**: First
   statement-level backend-equivalence theorems — `.let_ n v` and `.assign n v`
   produce identical results under `.verity` and `.evmYulLean` when `v` is a
   `BridgedExpr`. These are narrow helpers a future full statement predicate
   can dispatch to.
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
    that Verity `execYulFuel` equals the EVMYulLean backend executor for
    `emitYul` runtime code, conditional on bridged embedded bodies.
12. **`yulCodegen_preserves_semantics_evmYulLean`**: Composes the existing
    Layer-3 IR-to-Yul preservation theorem with the bridged-runtime equality
    above, yielding a contract-level result whose Yul side is evaluated by the
    EVMYulLean builtin backend. This remains conditional on generated embedded
    bodies satisfying `BridgedStmts`.

This is still not an end-to-end theorem, because the full EndToEnd composition
still targets `interpretYulFromIR`; using the EVMYulLean-targeted Layer-3
theorem requires discharging the embedded-body `BridgedStmts` hypotheses for
the compiled contract.

### What remains:
- **EndToEnd composition**: Replace the public end-to-end theorem's Yul target
  with `interpretYulRuntimeWithBackend .evmYulLean` once body-closure
  hypotheses are available for the compiled contract.
- **2 core sorry's**: smod/sar (complex Int↔UInt256 sign/bit semantics)

### Trust boundary (current state):
Expressions constrained by `BridgedExpr`, straight-line statement lists
constrained by `BridgedStraightStmts`, and recursive statement targets
constrained by `BridgedTarget` inherit EVMYulLean semantics. Contract-level
Layer-3 preservation also targets the EVMYulLean backend when embedded bodies
satisfy `BridgedStmts`. Whole-program guarantees still depend on EndToEnd
composition and on the two sorry-dependent core equivalences above.
-/

end Compiler.Proofs.YulGeneration.Backends
