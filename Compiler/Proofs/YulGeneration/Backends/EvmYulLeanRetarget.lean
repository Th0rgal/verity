/-
  Phase 4: Retarget the theorem stack to EVMYulLean.

  This module proves that the Verity Yul semantics — currently targeting the
  `.verity` builtin backend — are equivalent to execution under the `.evmYulLean`
  backend for programs that use only bridged builtins.

  **Key theorem**: `backends_agree_on_bridged_builtins` shows that
  `evalBuiltinCallWithBackendContext .verity ... func args =
   evalBuiltinCallWithBackendContext .evmYulLean ... func args`
  for every `func ∈ bridgedBuiltins`.

  This is a **pointwise** statement over single builtin calls. The whole-program
  lift (expression-level and Layer-3-composed IR → Yul `.evmYulLean`) requires
  structural induction over the Yul AST and is **not yet proven**; see the
  module summary at the bottom of this file.

  **Trust boundary shift (pointwise)**: For any builtin call using a bridged
  name, the trust boundary moves from "Verity's custom Yul builtin semantics
  are correct" to "EVMYulLean's builtin semantics match the EVM" (backed by
  upstream conformance tests). Whole-program guarantees still require the
  pending structural induction.

  Run: lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanRetarget
-/

import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas
import Compiler.Proofs.YulGeneration.Preservation

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Proofs.YulGeneration

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

/-! ## Backend Equivalence for Bridged Builtins

The `.evmYulLean` and `.verity` backends agree on all 34 bridged builtins.
This is the pointwise equivalence theorem that Phase 4 retargeting relies on.
The 2 sorry-dependent builtins (smod, sar) contribute
to this through their sorry-backed bridge lemmas in `EvmYulLeanBridgeLemmas.lean`.
-/

/-- For any builtin in `bridgedBuiltins`, the `.verity` and `.evmYulLean` backends
    produce identical results under `evalBuiltinCallWithBackendContext`.

    This is the master backend equivalence theorem for Phase 4 retargeting.
    It composes the 34 per-builtin bridge theorems into a single dispatch proof.
    The 2 unbridged builtins (`sload`, `mappingSlot`) are excluded by the
    `hBridged` hypothesis.

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
    rfl | rfl | rfl | rfl
  -- 34 goals, one per bridged builtin. Dispatch to per-builtin helpers.
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

/-! ## Phase 4 Completion Summary

### What this module establishes:
1. **`backends_agree_on_bridged_builtins`**: Pointwise backend equivalence for
   the full bridged-builtin set at the `evalBuiltinCallWithBackendContext`
   level. For every `func ∈ bridgedBuiltins`, `.verity` and `.evmYulLean`
   return the same result. The dispatch proof is sorry-free; the 2 sorry-backed
   core equivalences (smod, sar) are isolated in `EvmYulLeanBridgeLemmas.lean`.

This is the *pointwise* statement. It is deliberately the only end-to-end
theorem in this module, because:
- A stronger expression-level statement (`evalYulExpr` over both backends)
  requires the whole-program structural induction described under "What
  remains" below and is **not yet proven**.
- A Layer-3-composed statement (IR → Yul under `.evmYulLean`) requires that
  same induction plus Phase 3 state bridging and is **not yet proven**.

### What remains:
- **Phase 3 state bridge**: Prove `sload` and `mappingSlot` equivalence
- **Whole-program induction**: Lift pointwise builtin equivalence to full
  Yul-program execution equivalence (structural induction over the AST)
- **2 core sorry's**: smod/sar (complex Int↔UInt256 sign/bit semantics)

### Trust boundary (current state):
Anything provable via only bridged builtins inherits EVMYulLean semantics
pointwise. Whole-program guarantees still depend on the two items above.
-/

end Compiler.Proofs.YulGeneration.Backends
