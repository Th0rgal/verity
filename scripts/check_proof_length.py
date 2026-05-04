#!/usr/bin/env python3
"""Check proof lengths and enforce size limits.

Enforces the proof hygiene guideline from CONTRIBUTING.md:
- Proofs should be under 30 lines.
- Proofs over 50 lines require an entry in the allowlist below.
- New proofs exceeding the hard limit without an allowlist entry fail CI.

Usage:
    python3 scripts/check_proof_length.py
    python3 scripts/check_proof_length.py --format=markdown   # summary table
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from property_utils import ROOT, THEOREM_RE, strip_lean_comments

# Any new declaration keyword that ends the current proof span.
_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:(?:partial)\s+)?"
    r"(?:theorem|lemma|def|example|instance|inductive|structure|class|abbrev|opaque)\s+"
)
_END_RE = re.compile(r"^\s*end\b")
_SECTION_RE = re.compile(r"^\s*(?:section|namespace)\b")

SOFT_LIMIT = 30
HARD_LIMIT = 50

# Existing proofs that exceed HARD_LIMIT. Each entry was reviewed and accepted
# before the check was introduced. New proofs must not be added here without a
# justification comment in the PR explaining why decomposition is not feasible.
ALLOWLIST: set[str] = {
    # --- Expression compilation correctness proofs ---
    "eval_compileExpr_ceilDiv_of_compiled",
    "eval_compileExpr_wDivUp_of_compiled",
    "eval_compileExpr_mulDivDown_of_compiled",
    "eval_compileExpr_mulDivUp_of_compiled",
    "eval_compileExpr_logicalAnd_of_compiled",
    "eval_compileExpr_logicalOr_of_compiled",
    # --- Core expression/statement compilation ---
    "compileExpr_core_ok",
    "compileRequireFailCond_core_ok",
    "compileStmt_core_ok_any_scope",  # mstore/tstore widening — mechanical per-constructor cases
    "compileStmtList_core_ok",
    "compileStmtList_terminal_core_ok",
    "compileStmtList_terminal_core_ok_nonempty",
    "execStmtList_terminal_core_not_continue",  # mstore/tstore widening — 9 per-constructor cases
    "compileStmtList_terminal_ite_ok_inv",
    "compileStmt_terminal_ite_ok_inv",
    "compileStmt_ok_any_scope_aux",
    "eval_compileExpr_core_onExpr",
    "evalExpr_lt_evmModulus_core_onExpr",
    "eval_compileRequireFailCond_core_onExpr",
    # Constructor mode equivalence is a structural expression-constructor split;
    # each case is direct, but splitting further would duplicate the same
    # surface-closure plumbing across dozens of one-line cases.
    "compileExpr_constructor_mode_eq",
    # --- Statement-level compiled step proofs ---
    "compiledStmtStep_letVar",
    "compiledStmtStep_assignVar",
    "compiledStmtStep_require",
    "compiledStmtStep_return",
    "compiledStmtStep_ite",
    # --- Storage write compiled step proofs ---
    "compiledStmtStep_setStorage_singleSlot",
    "compiledStmtStep_setStorage_aliasSlots",
    "compiledStmtStep_setStorage_of_validateIdentifierShapes",
    "compiledStmtStep_setStorage_of_validateIdentifierShapes_of_scopeDiscipline",
    "compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences",
    "compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences_of_compileStmtList_of_bodySurface",
    "compiledStmtStep_setStorageAddr_singleSlot_preserves",
    # --- Mapping write singleton bridges ---
    "compiledStmtStep_setMappingUint_singleSlot_of_slotSafety_preserves",
    "compiledStmtStep_setMapping_singleSlot_of_slotSafety_preserves",
    "compiledStmtStep_setMappingWord_singleSlot_of_slotSafety_preserves",
    "compiledStmtStep_setStructMember_singleSlot_of_slotSafety_preserves",
    "compiledStmtStep_setMapping2_singleSlot_of_slotSafety_preserves",
    "compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety_preserves",
    "compiledStmtStep_setMappingChain_singleSlot_of_slotSafety_preserves",
    "compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety_preserves",
    "compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety",
    # --- Helper-aware result packaging bridge ---
    "interpretFunctionWithHelpers_eq_execResultToIRResultWithInternals_of_body",
    "compiledStmtStep_setStructMember2_singleSlot_of_slotSafety_preserves",
    "stmtListGenericCore_singleton_setStructMember2Single_of_slotSafety",
    # --- Transient/memory write singleton bridges ---
    "compiledStmtStep_tstore_single_preserves",
    "compiledStmtStep_mstore_single_preserves",
    # --- IR execution proofs (terminal ite, core append/tail) ---
    "execIRStmt_compiled_terminal_ite_then_branch_entry",
    "execIRStmt_compiled_terminal_ite_else_branch_entry",
    "execIRStmt_compiled_terminal_ite_else_branch_entry_tailFuel",
    "execIRStmts_compiled_terminal_ite_then_of_irExec",
    "execIRStmts_compiled_terminal_ite_else_of_irExec",
    "stmtResultMatchesIRExec_compiled_terminal_ite_then",
    "stmtResultMatchesIRExec_compiled_terminal_ite_else",
    "execIRStmts_compiled_return_core_append_wholeFuel_of_scope",
    "execIRStmts_compiled_let_core_append_wholeFuel_of_scope",
    "execIRStmts_compiled_let_core_tailExtraFuel_of_scope",
    "execIRStmts_compiled_assign_core_append_wholeFuel_of_scope",
    "execIRStmts_compiled_assign_core_tailExtraFuel_of_scope",
    "execIRStmts_compiled_require_core_pass_append_wholeFuel_of_scope",
    "execIRStmts_compiled_require_core_pass_tailExtraFuel_of_scope",
    "execIRStmts_compiled_require_core_fail_append_wholeFuel_of_scope",
    "stmtResultMatchesIRExec_compiled_let_core_tailExtraFuel_of_scope",
    "stmtResultMatchesIRExec_compiled_assign_core_tailExtraFuel_of_scope",
    "stmtResultMatchesIRExec_compiled_require_core_pass_tailExtraFuel_of_scope",
    "stmtResultMatchesIRExec_compiled_return_core_append_wholeFuel_of_scope",
    "exec_compileStmtList_core",
    "exec_compileStmtList_core_extraFuel",
    "exec_compileStmtList_terminal_core_sizeOf_extraFuel",
    "exec_compileStmtList_generic_sizeOf_extraFuel_step",
    # --- Generic induction and scope proofs ---
    "stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded",
    "stmtListGenericCore_of_stmtListTerminalCore_of_scopeNamesIncluded",
    "stmtListGenericCore_of_supportedStmtList_of_surface",
    "stmtListGenericCore_of_supportedStmtList_of_surface_exceptMappingWrites",
    "stmtListGenericCore_of_supportedStmtList_of_surface_exceptMappingWrites_stmtSafety",
    "stmtListGenericCore_singleton_requireLiteralGuardFamilyClause",
    "stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface",
    "stmtListScopeCore_of_unsupportedContractSurface_eq_false",
    "exprBoundNamesInScope_of_validateScopedExprIdentifiers_core",
    "stmtListScopeDiscipline_of_validateScopedStmtListIdentifiers",
    "scopeNamesPresent_foldl_stmtNextScope_of_validateScopedStmtListIdentifiers",
    "stmtListScopeDiscipline_scope_names",
    # --- Surface predicate bridge proofs ---
    "exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false",
    "exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed",
    "exprTouchesUnsupportedCallSurface_eq_featureOr",
    "exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed",
    "exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed",
    "stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed",
    "stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames",
    "stmtTouchesUnsupportedContractSurface_eq_false_of_featureClosed",
    "stmtListTerminalCore_helperSurfaceClosed",  # mstore/tstore widening — mechanical per-constructor cases
    "SupportedStmtList.helperSurfaceClosed",
    "SupportedStmtList.internalHelperCallNames_nil",
    "supportedStmtList_usesStorageArrayElement_false",
    "supportedStmtList_usesDynamicBytesEq_false",
    "supportedStmtList_usesArrayElement_false",
    # --- Mapping slot and field resolution proofs ---
    "findResolvedFieldAtSlotCopyFrom_of_member",
    "firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_member",
    # IRStorageSlot migration: these storage write/state-match proofs grew
    # because each case now carries both the old source Nat slot reasoning and
    # the bounded IRStorageSlot normalization bridge. Splitting them further
    # would duplicate the same `wordNormalize`/`IRStorageSlot.ofNat` plumbing
    # across one-off local helpers.
    "runtimeStateMatchesIR_writeUintSlots",
    "runtimeStateMatchesIR_writeAddressSlot",
    "runtimeStateMatchesIR_writeAddressKeyedMappingChainSlot",
    "runtimeStateMatchesIR_writeAddressKeyedMappingSlot",
    "runtimeStateMatchesIR_writeAddressKeyedMappingWordSlot",
    "runtimeStateMatchesIR_writeAddressKeyedMappingPackedWordSlot",
    "runtimeStateMatchesIR_writeAddressKeyedMapping2Slot",
    "runtimeStateMatchesIR_writeAddressKeyedMapping2WordSlot",
    "encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_eq_written",
    "encodeStorageAt_writeAddressKeyedMapping2Slots_singleton_eq_written",
    "encodeStorageAt_writeAddressKeyedMapping2WordSlots_singleton_eq_written",
    # Source storage-read steps need to bridge `sload(lit slot)` through
    # `wordNormalize slot` and then repackage the updated binding/state
    # invariants. These are four parallel cases for uint/address let/assign.
    "compiledStmtStep_letStorageField",
    "compiledStmtStep_letStorageAddrField",
    "compiledStmtStep_assignStorageField",
    "compiledStmtStep_assignStorageAddrField",
    # --- Compat scratch lemmas ---
    "compatScratch_not_internalImmutable",
    "compatScratch_startsWith_reserved",
    "scopeAvoidsReservedCompilerPrefix_of_validateIdentifierShapes",
    # --- Function-level compilation proofs ---
    "compileFunctionSpec_correct_of_body",
    "compileFunctionSpec_correct_of_body_normalized_extraFuel",
    "compileFunctionSpec_correct_generic",
    "exec_compiledFunctionIR_of_body",
    "exec_compiledFunctionIR_of_body_extraFuel",
    "exec_genParamLoadBodyFrom_supported_then",
    "exec_genParamLoads_supported_then_extraFuel",
    "bindSupportedParams_lookupBinding",
    "supported_function_body_correct_from_exact_state_core",
    "supported_function_body_correct_from_exact_state_core_extraFuel",
    "supported_function_body_correct_from_exact_state_terminal_core_extraFuel",
    "supported_function_body_correct_from_exact_state_generic",
    "supported_function_correct",
    "supported_function_correct_except_mapping_writes",
    "supported_function_correct_except_mapping_writes_stmtSafety",
    "supported_function_correct_with_body_interface_except_mapping_writes",
    "supported_function_correct_with_body_interface_except_mapping_writes_stmtSafety",
    # --- Legacy compatibility and dispatch ---
    "legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface",
    "legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields_resolved",
    "legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface_exceptMappingWrites",
    "legacyCompatibleExternalStmtList_of_compileSetStructMember2_ok",
    "interpretContract_correct_of_compiled_functions",
    "interpretContract_correct_of_compiled_functions_except_mapping_writes_and_helper_ir_closed",
    # Constructor-bearing compile output adds one extra compileConstructor split
    # to these component extractors; the surrounding Forall₂ proof shape remains
    # unchanged and does not factor cleanly without duplicating mapM plumbing.
    "compileValidatedCore_ok_yields_compiled_functions",
    "compileValidatedCore_ok_yields_compiled_functions_except_mapping_writes",
    "compile_ok_yields_internalFunctions_nil_except_mapping_writes",
    "compile_preserves_semantics",
    "compile_preserves_semantics_except_mapping_writes",
    "compile_preserves_semantics_except_mapping_writes_stmtSafety",
    "initialIRStateForTx_matches_runtime",
    "resultsMatch_of_execResultsAligned",
    # --- SimpleStorage native EVMYulLean dispatcher closed forms ---
    # These are concrete generated-code reductions for the store(uint256)
    # selected path. The long proofs are linear fuel/body-shape plumbing over
    # generated Yul and are kept local to the Phase 3 bridge discharge.
    "exec_block_simpleStorageLoweredStoreCaseBodyTail3_halt",
    "exec_block_simpleStorageLoweredStoreCaseBody_halt",
    "interpretIR_simpleStorage_storeHit_arg",
    "simpleStorageNativeContract_dispatcherExec_storeHit_halt_atFuel",
    # Phase 3 short-calldata store-hit endpoint: same generated dispatcher
    # plumbing as the halt endpoint, but the selected body takes the ABI
    # argument-length revert branch before reaching the store payload.
    "simpleStorageNativeContract_dispatcherExec_storeHit_short_revert_atFuel",
    # Phase 3 store-hit storage projection: zero sstore erases the EVM RBMap
    # key, while the IR stores a bounded zero word. The proof must split zero
    # and nonzero writes plus same-key/other-key projected lookups.
    "projectStorageFromState_storeHit_initialState_materialized",
    # RBMap erase-self deletion follows the Batteries red-black tree delete
    # algorithm through the three ordered-tree branches. The cases are
    # mechanical and shared by the native zero-sstore projection helpers.
    "del_all_cut_ne",
    # Native zero-sstore projection composes calldata, sstore, stop, and the
    # RBMap erase-self lookup fact in one generated store-body endpoint.
    "primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_projectResult_slot0_zero_of_erase",
    # --- Helper-aware theorem stack (Issue #1630 / PR #1633 / PR #1639) ---
    "supported_function_body_correct_from_exact_state_generic_with_helpers",
    "supported_function_body_correct_from_exact_state_generic_with_helpers_goal",
    "supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir",
    "supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir_callsDisjoint",
    "supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir_except_mapping_writes",
    "supported_function_body_correct_from_exact_state_generic_helper_steps_raw",
    "supported_function_body_correct_from_exact_state_generic_helper_surface_steps_and_helper_ir",
    "supported_function_body_correct_from_exact_state_generic_internal_helper_surface_steps_and_helper_ir",
    "supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir",
    "supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir_callsDisjoint",
    "supported_function_body_correct_from_exact_state_generic_split_internal_helper_surface_steps_and_helper_ir",
    "supported_function_body_with_helpers_ir_goal_of_helper_ir_goal_callsDisjoint",
    "supported_function_correct_with_helper_proofs",
    "supported_function_correct_with_helper_proofs_goal",
    "supported_function_correct_with_helper_proofs_body_goal",
    "supported_function_correct_with_helper_proofs_body_goal_and_helper_ir",
    "supported_function_correct_with_helper_proofs_body_goal_and_helper_ir_of_bodyCallsDisjoint",
    "compileFunctionSpec_correct_generic_with_helper_proofs",
    "compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir",
    "compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir_of_bodyCallsDisjoint",
    "interpretContract_correct_of_compiled_functions_with_helper_proofs",
    "interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir_goal",
    "compile_preserves_semantics_with_helper_proofs",
    "exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel_step",
    "exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel_step",
    "stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible",
    "stmtListGenericWithHelpersAndHelperIR_of_withHelpers_and_compiledLegacyCompatible",
    # --- IR interpreter dispatch (mload pre-dispatch adds extra branches) ---
    "evalIRExprWithInternals_eq_evalIRExpr_of_callsDisjoint",
    "evalIRExprWithInternals_eq_evalIRExpr_of_no_internal",
    # --- Return statement compilation (memory sync adds steps) ---
    "exec_compileStmt_return_core_extraFuel",
    # --- Helper-aware IR compatibility proofs ---
    "execIRStmtWithInternals_eq_execIRStmt_sstore_of_no_internal",
    # Event-log interpreter compatibility has to mirror the builtin-call
    # case split for both disjoint and helper-free conservative-extension
    # theorems.
    "evalIRCallWithInternals_stmt_eq_of_callsDisjoint",
    "evalIRCallWithInternals_stmt_eq_of_no_internal",
    "execIRStmtWithInternals_eq_execIRStmt_expr_of_no_internal",
    "execIRStmtWithInternals_eq_execIRStmt_expr_of_callsDisjoint",
    "execIRStmtsWithInternals_eq_execIRStmts_of_exprCompatibility",
    "execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint",
    "execIRStmtsWithInternals_eq_execIRStmts_of_stmtCompatibility",
    "execIRStmtsWithInternals_of_internalCallAssign_compiledHelperWitness",
    "execIRStmtsWithInternals_of_internalCall_compiledHelperWitness",
    "execIRStmtsWithInternals_of_internalCall_compile",
    "compiledStmtStepWithHelpersAndHelperIR_internalCallAssign",
    "compiledStmtStepWithHelpersAndHelperIR_internalCall",
    "evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed",
    "execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_aux",
    # Spec-aware compile-scope transport is one mutual induction over
    # statements and statement lists; splitting it would duplicate the scope
    # bookkeeping that the theorem is meant to centralize.
    "compileStmt_ok_any_scope_with_surface_aux",
    # --- Contract feature fixtures ---
    "literalMappingWrite_calldataFits",
    # Constructor-body bridge and its focused fixture for issue #1723.
    "supported_constructor_body_correct_with_body_interface",
    "constructorOnly_noConflict",
    # Call-surface decomposition kept as one structural recursion proof.
    "stmtOrListTouchesUnsupportedCallSurface_eq_featureOr",
    # --- Yul generation / Layer 3 proofs ---
    "yulCodegen_preserves_semantics_via_reference_oracle",
    "stmt_and_stmts_equiv",
    "execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv",
    "legacyExecYulFuel_succ_eq",
    "exec_switchCaseBody_revert_of_short",
    "exec_switchCaseBody_continue_of_long",
    "SwitchCaseBodyBridge_short",
    "SwitchCaseBodyBridge",
    "layer3_contract_preserves_semantics",
    # Thin EVMYulLean EndToEnd wrapper; signature carries explicit body-closure
    # witnesses and the proof mostly forwards existing Layer-3 hypotheses.
    "layer3_contract_preserves_semantics_evmYulLean",
    # Native generated-fragment wrappers mirror the public native boundary
    # surface; the long spans are explicit shape/lowering/agreement hypotheses,
    # while the bodies delegate to smaller generated-fragment lemmas.
    "layer3_contract_preserves_semantics_native_of_generated_lowered_callDispatcher_bridge",
    "layer3_contract_preserves_semantics_native_of_generated_dispatcherExec_bridge",
    "layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_callDispatcher_bridge",
    # --- End-to-end proofs ---
    "simpleStorage_endToEnd",
    # Thin public wrapper; the scanner counts the trailing Phase 4 summary
    # comment in its theorem span.
    "simpleStorage_endToEnd_evmYulLean",
    # Native SimpleStorage wrapper keeps the dispatcher-agreement seam explicit
    # while delegating to the lowered native theorem; the long span is the public
    # hypothesis surface, not a large proof script.
    "simpleStorage_endToEnd_native_evmYulLean",
    # Phase 2 retrieve-hit prerequisites: closed-form interpretIR reduction
    # over the retrieve body's two-statement form (`mstore(0, sload(0));
    # return(0, 32)`); the proof must walk the EDSL execIRStmts/execIRStmt
    # state machine through the call/expr/builtin layers and discharge a
    # fuel-bound side condition. Cannot be split without exposing internal
    # IR-evaluation helpers.
    "interpretIR_simpleStorage_retrieveHit",
    # Phase 2 retrieve-hit prerequisites: dispatcher-exec halt-form chain.
    # Composes the body-level closed form with the existing tail3 reduction
    # endpoint after opening the source-lowered existential and pinning the
    # switch case shape. The 155-line span is the union of fuel-reshape,
    # existential-opening, body-state plumbing, and `_via_reduction`'s
    # decomposition obligation; each piece is mechanical but inseparable.
    "simpleStorageNativeContract_dispatcherExec_retrieveHit_halt_atFuel",
    # Phase 2 retrieve-hit prerequisites: closed-form `projectResult`
    # evaluation on the YulHalt halt produced by the lowered retrieve body.
    # The proof must thread `mstore0_then_return32_*` harness lemmas across
    # the chained `setMachineState` overrides to extract the 32-byte
    # `H_return` window before computing `projectHaltReturn`.
    "projectResult_retrieveHit_eq",
    # Direct native-vs-IR retrieve-hit closure: intentionally mirrors the
    # concrete native dispatcher halt and projected-storage plumbing above, but
    # targets `nativeDispatcherExecMatchesIRPositive` directly.
    "simpleStorageNativeRetrieveHitMatchBridge_proved",
    # Direct native-vs-IR store-hit closure: it intentionally keeps the
    # short-calldata revert and argument-present storage-update branches in one
    # proof so the direct native case split stays explicit.
    "simpleStorageNativeStoreHitMatchBridge_proved",
    # Safe-body public EVMYulLean wrapper derives the raw BridgedStmts function
    # hypotheses from compile output, static parameter closure, and
    # BridgedSafeStmts witnesses before delegating to the function-bridge
    # variant. Splitting it would only move the hypothesis threading into a
    # single-use helper.
    "layers2_3_ir_matches_yul_evmYulLean",
    # Native generic-route bridge closure has to expose the function, fallback,
    # receive, and internal-body BridgedStmts witnesses explicitly before
    # applying the Yul backend equivalence. The proof is linear hypothesis
    # plumbing around one public transition theorem.
    "interpretYulFromIR_evmYulLean_eq_on_bridged_bodies",
    # --- Contract proofs (Contracts/) ---
    "constructor_increment_getCount",
    "add_one_preserves_order_iff_no_overflow",
    "sub_add_cancel_of_lt",
    "sub_add_cancel_left",
    "safeDiv_result_le_numerator",
    # --- EVMYulLean bridge proofs (multi-layer UInt256→Fin→Nat reduction) ---
    "bridge_eval_byte_normalized",
    "sdiv_int256_eq_uint256Sdiv",
    "smod_int256_eq_uint256Smod",
    # Verity-side half of A2 (smod); 5-case sign decomposition mirroring sdiv.
    "int256_mod_toUint256_val_eq_smodSpec",
    # EVMYulLean-side half of A2 (smod); mirrors the UInt256.smod definition
    # across divisor-zero, sign, and zero-remainder cases before composing
    # through the shared Nat-level smodSpec.
    "uint256_smod_toNat_eq_smodSpec",
    # EVMYulLean-side half of A3 (sar); it must split on sign and saturated
    # shift, then normalize complement-shift-complement through Fin and Nat.
    "uint256_sar_toNat_eq_sarSpec",
    # Verity-side half of A3 (sar); it must split on sign and saturated
    # shift, then connect Int.fdiv on negative two's-complement words to the
    # shared Nat-level sarSpec used by the EVMYulLean-side proof.
    "int256_sar_toUint256_val_eq_sarSpec",
    # signextend proof requires 4-case byte-index analysis + bit-level shift
    # semantics matching; structural complexity is inherent to the operation.
    "signextend_uint256_eq",
    # backends_agree dispatch proof case-splits all 36 bridged builtins;
    # each branch is one line but 36 builtins + headers exceed 50 lines.
    "backends_agree_on_bridged_builtins",
    # Pure-context dispatch is the same 25-builtin case split specialized to
    # context-free builtins; each branch delegates to an individual bridge.
    "evalBuiltinCallWithBackendContext_evmYulLean_pure_bridge",
    # Backend-parameterized mirror of legacyExecYulFuel; long by construction because
    # it preserves all statement cases while swapping only expression backend.
    "execYulFuelWithBackend",
    # Recovery proof mirrors the executor's statement case split; each branch is
    # direct simplification back to legacyExecYulFuel.
    "execYulFuelWithBackend_verity_eq",
    # Native harness block-append lemmas are structural inductions over a Yul
    # block prefix with fuel normalization at each cons. The success, suffix
    # error, and prefix-error variants are intentionally parallel because they
    # encode distinct executor outcomes used by the native lowering harness.
    "exec_block_append_error",
    "exec_block_append_prefix_error",
    # Native switch-case prefix-hit error mirrors the successful prefix-hit
    # proof but threads an error result from the selected body through the
    # generated case-chain fuel accounting.
    "exec_nativeSwitchCaseIfs_prefix_hit_error_fuel",
    # Per-constructor straight-line statement backend equivalence: one short
    # case per `BridgedStraightStmt` constructor; the breadth of shapes
    # (comment/let/letMany/assign/leave/sstore_mapping/sstore_lit/
    # sstore_ident/mstore/tstore/stop/return/revert/funcDef) pushes the total
    # past 50 lines even with each case under a handful of tactics.
    "execYulFuelWithBackend_eq_on_bridged_straight_stmt",
    # Straight-line statement-list backend equivalence: fuel induction plus a
    # head/tail dispatch over the four YulExecResult constructors forces the
    # proof past the 50-line budget even with all stmt cases delegated to the
    # per-constructor helper lemma.
    "execYulFuelWithBackend_eq_on_bridged_straight_stmts",
    # Block-wrapper theorem has a short proof, but the scanner counts the
    # following Phase 4 summary comment / next theorem's doc block in its
    # theorem span because section comments are attributed to the preceding
    # theorem.
    "execYulFuelWithBackend_block_eq_on_bridged_straight_stmts",
    # If-body theorem has a short proof, but the scanner counts the trailing
    # switch theorem's doc block in its theorem span.
    "execYulFuelWithBackend_if_eq_on_bridged_body",
    # Switch helper has a short proof, but the scanner counts the trailing
    # for theorem's doc block in its theorem span.
    "execYulFuelWithBackend_switch_eq_on_bridged_cases",
    # For helper follows the executor's nested loop structure and exceeds the
    # default 50-line budget even though it delegates all list execution to
    # existing straight-line lemmas.
    "execYulFuelWithBackend_for_eq_on_bridged_parts",
    # Default dispatch closure covers all four fallback/receive combinations;
    # each branch is a direct constructor proof for the generated wrapper.
    "defaultDispatchCase_bridged",
    # Recursive target theorem is the statement-level fuel induction over all
    # BridgedStmt constructors. Each branch mirrors one executor case and
    # delegates nested execution through the predecessor-fuel IH.
    "execYulFuelWithBackend_eq_on_bridged_target",
    # Thin public wrapper, but the scanner counts the trailing Phase 4 summary
    # comment in its theorem span.
    "execYulFuelWithBackend_eq_on_bridged_stmts",
    # Conditional emitted-runtime backend equality composes wrapper closure,
    # recursive target equality, and `.verity` executor recovery; the statement
    # is long because it carries all embedded-body closure hypotheses.
    "emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies",
    # Conditional Layer-3 EVMYulLean theorem composes existing codegen
    # preservation with emitted-runtime backend equality; the scanner also
    # counts the trailing Phase 4 summary block in its theorem span.
    "yulCodegen_preserves_semantics_evmYulLean_via_reference_oracle",
    # Scalar parameter body closure is a structural induction over the six
    # scalar ABI cases emitted by `genParamLoadBodyFrom`.
    "genParamLoadBodyFrom_calldataload_bridged",
    # Static scalar composite body closure mirrors `IsStaticScalarParamType`
    # with three inductive branches (scalar / fixedArray / tuple) and a nested
    # list induction over the tuple's `let rec go` body.
    "genStaticTypeLoads_calldataload_bridged",
    # Static scalar parameter body closure is a structural induction over the
    # actual `genParamLoadBodyFrom` prologue generator; the fixed-array branch
    # has to cover both inline static loads and the generated first-element alias.
    "genParamLoadBodyFrom_calldataload_static_scalar_bridged",
    # Source-expression closure main theorem: structural induction over the
    # 21 `BridgedSourceExpr` constructors (4 leaves + 17 binops); each binop
    # case is 4-5 lines and cannot be merged without losing readability.
    "compileExpr_bridgedSource",
    # Pure binding list closure mirrors `compileStmtList`'s head/tail recursion;
    # most proof lines are boilerplate decomposition of the two Except binds.
    "compileStmtList_pure_binding_bridged",
    # Storage-fragment list closure has the same compileStmtList head/tail
    # recursion plus per-head dispatch between pure bindings and single-slot
    # setStorage; decomposition would only duplicate the existing list skeleton.
    "compileStmtList_storage_fragment_bridged",
    # External-terminator list closure mirrors compileStmtList's head/tail
    # recursion; its reported span grew past 50 lines when the require-closure
    # section was appended after it. The theorem body itself remains short
    # boilerplate over Except binds.
    "compileStmtList_terminator_external_bridged",
    # Require list closure follows the same compileStmtList head/tail skeleton
    # with a `cases hHeadSource` step to extract the bridged failure-condition
    # hypothesis before delegating to the per-statement require closure.
    "compileStmtList_require_bridged",
    # Mapping-write list closure mirrors the same compileStmtList head/tail
    # recursion skeleton; delegates per-head to the mapping-write dispatch
    # theorem. The excess lines are boilerplate decomposition of the two
    # Except binds over head and tail.
    "compileStmtList_mappingWrite_bridged",
    # Double-mapping single-slot setMapping2 closure nests one compileExpr
    # cases layer deeper than the single-mapping variant (three exprs
    # compileExpr calls + inner mappingSlot BridgedExpr.call construction),
    # pushing the proof three lines over the limit.
    "compileStmt_setMapping2_singleSlot_bridged",
    # Double-mapping list closure is the same compileStmtList head/tail
    # skeleton as the single-mapping variant; the excess lines are
    # boilerplate decomposition of the two Except binds.
    "compileStmtList_mappingWrite2_bridged",
    # setStorageAddr list closure is the same compileStmtList head/tail
    # skeleton as the other single-slot closures; the excess lines are
    # boilerplate decomposition of the two Except binds plus the doc
    # comment for the next section (which the proof-length measurer
    # attributes to this proof's span).
    "compileStmtList_storageAddr_bridged",
    # setStructMember list closure same as other single-slot closures;
    # the extra lines come from the doc-comment preamble for the next
    # section being attributed to this proof's span by the measurer.
    "compileStmtList_structMember_bridged",
    # Double-mapping struct-member single-slot closure mirrors the
    # setMapping2 single-slot proof (three compileExpr cases + inner
    # BridgedExpr.call construction) but adds four additional struct
    # hypotheses (members/findMember/unpacked/wordOffset) that are
    # unfolded up front, pushing the proof over the limit.
    "compileStmt_setStructMember2_singleSlot_bridged",
    # setStructMember2 list closure same as other single-slot list
    # closures; the extra lines come from the doc-comment preamble for
    # the next section (setMappingWord) being attributed to this proof's
    # span by the measurer.
    "compileStmtList_structMember2_bridged",
    # setMappingWord list closure same as other single-slot list
    # closures; the extra lines come from the doc-comment preamble for
    # the next section (setMapping2Word) being attributed to this
    # proof's span by the measurer.
    "compileStmtList_mappingWord_bridged",
    # Double-mapping-word single-slot closure mirrors the setMapping2
    # single-slot proof (three compileExpr cases + inner BridgedExpr.call
    # construction) but adds a leading `subst hWordOffset` plus an
    # `unfold compileSetMapping2Word`, pushing the proof over the limit.
    "compileStmt_setMapping2Word_singleSlot_bridged",
    # setMapping2Word list closure same as other single-slot list
    # closures; the extra lines come from the doc-comment preamble for
    # the next section (returnValuesEmpty external) being attributed to
    # this proof's span by the measurer.
    "compileStmtList_mapping2Word_bridged",
    # Internal empty-returnValues list closure is the same compileStmtList
    # head/tail skeleton as other body-closure list proofs; the excess lines
    # come from the doc-comment preamble for the next section (internal
    # non-empty returnValues) being attributed to this proof's span.
    "compileStmtList_returnValuesEmpty_internal_bridged",
    # Internal non-empty returnValues list closure is the same compileStmtList
    # head/tail skeleton; the excess lines come from the doc-comment preamble
    # for the next section (external general returnValues) being attributed to
    # this proof's span by the measurer.
    "compileStmtList_returnValuesInternal_bridged",
    # External returnValues list closure is the same compileStmtList head/tail
    # skeleton; the excess lines come from the doc-comment preamble for the
    # next section (mstore/tstore body closure) being attributed to this
    # proof's span by the measurer.
    "compileStmtList_returnValuesExternal_bridged",
    # Internal-return list closure is the same compileStmtList head/tail
    # skeleton as the external terminator and require closure proofs; the
    # excess lines are boilerplate decomposition of the two Except binds.
    "compileStmtList_internal_return_bridged",
    # Internal mixed-body list closure is the same compileStmtList head/tail
    # skeleton as the external mixed-body list proof; its span crosses the
    # limit because the following one-layer ite section now follows it.
    "compileStmtList_internal_body_fragment_bridged",
    # One-layer source ite closure mirrors the compiler's two emitted shapes:
    # empty else emits one Yul if, nonempty else emits a three-statement block
    # with a cached condition and two Yul ifs. The proof is mostly mechanical
    # Except-bind decomposition plus those two generated-shape branches.
    "compileStmt_ite_external_body_fragment_bridged",
    # Same generated-shape proof as the external ite closure, but with internal
    # branch body closure so internal returns compile to assignment plus leave.
    "compileStmt_ite_internal_body_fragment_bridged",
    # One-layer source ite closure for with-errors body fragments: same two
    # compiler-emitted shapes as the plain-body variant (empty else -> one Yul
    # if, nonempty else -> cached-condition block with two Yul ifs), but the
    # branches are closed via the with-errors list closure so they may include
    # zero-arg custom errors, direct mstore/tstore, and single-slot mapping
    # writes alongside storage/require/terminator. Mechanical Except-bind
    # decomposition.
    "compileStmt_ite_external_body_with_errors_bridged",
    # Same generated-shape proof as the external with-errors ite closure, but
    # with internal branch body closure for internal returns alongside
    # with-errors extensions.
    "compileStmt_ite_internal_body_with_errors_bridged",
    # External structured with-errors list closure: same compileStmtList
    # head/tail skeleton as the plain-body structured list closure, delegating
    # per-statement closure to the structured with-errors dispatcher.
    "compileStmtList_external_structured_body_with_errors_bridged",
    # Internal structured with-errors list closure: span now includes the
    # trailing nested-with-errors section header because the measured range
    # reaches the next non-indented section. Proof body unchanged.
    "compileStmtList_internal_structured_body_with_errors_bridged",
    # Two-level with-errors ite closure mirrors the same two compiler-emitted
    # shapes (single Yul `if` vs cached-condition `block` with two inner
    # `if`s) as the one-layer with-errors proof, but delegates branch bodies
    # to structured with-errors list closure. The proof is mechanical
    # Except-bind decomposition.
    "compileStmt_ite_external_nested_body_with_errors_bridged",
    # Same generated-shape proof as the external two-level with-errors ite
    # closure, but with internal branch body closure for internal returns
    # alongside with-errors extensions.
    "compileStmt_ite_internal_nested_body_with_errors_bridged",
    # External nested with-errors list closure: same compileStmtList
    # head/tail skeleton as earlier list closures; the measured span includes
    # the following internal-section boundary.
    "compileStmtList_external_nested_body_with_errors_bridged",
    # Internal nested with-errors list closure: span now reaches into the
    # following forEach-with-errors section header because the measured
    # range extends to the next non-indented section. Proof body unchanged.
    "compileStmtList_internal_nested_body_with_errors_bridged",
    # External forEach-wrapped with-errors list closure: same compileStmtList
    # head/tail skeleton as earlier list closures; the measured span reaches
    # into the internal forEach-with-errors section header.
    "compileStmtList_external_forEach_body_with_errors_bridged",
    # Internal forEach-wrapped with-errors list closure: span now reaches into
    # the following recursive-with-errors section header because the measured
    # range extends to the next non-indented section. Proof body unchanged.
    "compileStmtList_internal_forEach_body_with_errors_bridged",
    # Recursive with-errors body closure mirrors the same two compiler-emitted
    # ite shapes as the one-layer proof, but uses mutual recursion (matching
    # the plain-body recursive closure) to delegate arbitrarily nested branch
    # lists through the paired list closure. Proof is mechanical Except-bind
    # decomposition.
    "compileStmt_external_recursive_body_with_errors_bridged",
    # Same mutual-recursive proof shape as the external version, using the
    # internal-body dispatcher and internal-list closure for branches.
    "compileStmt_internal_recursive_body_with_errors_bridged",
    # Raw-log-lifted recursive external variant: identical proof shape to
    # `compileStmt_external_recursive_body_with_errors_bridged` with the
    # base case dispatching through `compileStmt_external_body_with_raw_log_bridged`
    # (which dispatches further to the with-errors base or the rawLog leaf).
    "compileStmt_external_recursive_body_with_raw_log_bridged",
    # Symmetric raw-log-lifted recursive internal variant.
    "compileStmt_internal_recursive_body_with_raw_log_bridged",
    # Internal structured-body list closure is the same compileStmtList
    # head/tail skeleton as the external structured-body proof; the measured
    # span now includes the following nested-ite section header.
    "compileStmtList_internal_structured_body_fragment_bridged",
    # Two-level source ite closure mirrors the same two compiler-emitted shapes
    # as the one-layer proof, but delegates branch bodies to structured-body
    # list closure. The proof is mechanical Except-bind decomposition.
    "compileStmt_ite_external_nested_body_fragment_bridged",
    # Same generated-shape proof as the external two-level ite closure, but
    # with internal branch body closure for internal returns.
    "compileStmt_ite_internal_nested_body_fragment_bridged",
    # Internal nested-body list closure is the same compileStmtList head/tail
    # skeleton as earlier list closure proofs; the following recursive-ite
    # section increases the measured declaration span.
    "compileStmtList_internal_nested_body_fragment_bridged",
    # Recursive source ite closure mirrors the same two emitted shapes as the
    # fixed-depth ite proofs, but recursive calls replace bounded branch
    # delegation. The proof remains mechanical Except-bind decomposition.
    "compileStmt_external_recursive_body_fragment_bridged",
    # Same recursive generated-shape proof as the external version, using the
    # internal body fragment so internal returns compile to assignment + leave.
    "compileStmt_internal_recursive_body_fragment_bridged",
    # Require failure-condition source closure case-splits on the 23
    # `BridgedSourceExpr` constructors: `.ge`/`.le` are handled specially
    # because `compileRequireFailCond` uses the direct `lt`/`gt` optimization,
    # and the remaining 21 constructors each invoke the shared
    # `compileRequireFailCond_default_bridgedSource` helper for the `iszero`
    # fall-through. Each constructor case is two mechanical lines; merging
    # them would require either introducing a generic reconstruction tactic
    # or passing a weaker hypothesis to the helper.
    "compileRequireFailCond_bridgedSource",
    # Memory-write source closure handles both `.mstore` and `.tstore`
    # constructors; each case is a mechanical Except-bind decomposition of the
    # two-argument `compileExpr`/`compileExpr` pair before a single
    # `BridgedStraightStmt.expr_mstore`/`expr_tstore` application. Merging the
    # two cases would require a shared helper that abstracts over the Yul
    # primitive name.
    "compileStmt_memoryWrite_bridged",
    # Memory-write list closure mirrors the same compileStmtList head/tail
    # skeleton as the other list closure proofs; the excess lines are
    # boilerplate decomposition of the two Except binds.
    "compileStmtList_memoryWrite_bridged",
    # `Stmt.forEach` closure has a fixed-shape wrapper: init `[let v := 0]`,
    # cond `lt(v, count)`, post `[v := add(v, 1)]`, plus the caller's body
    # closure hypothesis. The excess lines are boilerplate decomposition of
    # the two Except binds, the fixed init/cond/post shape proofs, and the
    # body delegation. Each init/post/cond witness is a mechanical
    # `BridgedStmt.straight` / `BridgedExpr.call` application.
    "compileStmt_forEach_with_bridged_body",
    # Zero-argument custom-error revert closure enumerates the seven distinct
    # bridged-statement kinds inside `revertWithCustomError`'s emitted
    # `YulStmt.block`: `mload`-let for the free-memory pointer, the four
    # `mstore` signature-byte stores produced by `chunkBytes32`, the
    # `keccak256`-let, the `shl`/`shr` selector arithmetic, the selector
    # `mstore`, the tail-init `mload`-let, and the final `revert` expr.
    # Each branch needs its own `BridgedExpr` construction because the
    # constructor families (`BridgedStraightStmt` vs `BridgedExpr.call`) and
    # arity differ; decomposing into per-statement-kind helpers would yield
    # seven trivial single-use lemmas whose combined boilerplate exceeds the
    # main proof's line count.
    "revertWithCustomError_zero_bridged",
    # Zero-arg custom-error list closure is standard compileStmtList
    # cons/nil induction (nil: empty-list lemma; cons: destructure head
    # Except.ok, destructure tail Except.ok, apply per-statement lemma,
    # recurse via IH, split membership by `List.mem_append`). The excess
    # lines are the four Except-bind cases mechanically matching
    # `compileStmtList`'s bind structure.
    "compileStmtList_customError_zero_bridged",
    # External body + zero-arg custom error list closure mirrors the
    # existing `compileStmtList_external_body_fragment_bridged` skeleton
    # verbatim; the head case just dispatches through the extended
    # per-statement theorem instead of the mixed-body one.
    "compileStmtList_external_body_with_errors_bridged",
    # Internal body + zero-arg custom error list closure: same cons/nil
    # boilerplate as the external variant with `isInternal := true`.
    "compileStmtList_internal_body_with_errors_bridged",
    # Direct `rawLog` source-closure proof unfolds `compileStmt`'s rawLog
    # branch: the `topics.length > 4` guard case (impossible via
    # `Except.noConfusion`), three sequential `Except.ok` destructurings
    # (`compileExprList topics`, `compileExpr dataOffset`, `compileExpr
    # dataSize`), per-arg `BridgedExpr` extraction through
    # `compileExprList_bridgedSource`/`compileExpr_bridgedSource`,
    # `isYulLogName s!"log{topics.length}"` discharge by 5-case `omega`
    # decomposition, and membership-split through `List.mem_append` for
    # the `[offset, size] ++ topics` argument list before applying
    # `BridgedStraightStmt.expr_log`. Decomposing would yield
    # single-use Except-bind helpers whose boilerplate exceeds the proof.
    "compileStmt_rawLog_bridged",
    # Direct `rawLog` list closure mirrors the shared cons/nil boilerplate
    # used by every `compileStmtList_*_bridged` sibling: the `error`/`ok`
    # destructurings of `compileStmt` and the recursive `compileStmtList`
    # call, plus `BridgedStmts_append` on the head/tail witnesses.
    "compileStmtList_rawLog_bridged",
    # Raw-log-lifted external body list closure dispatches head statements
    # through `compileStmt_external_body_with_raw_log_bridged` (base/rawLog)
    # and reuses the same cons/nil boilerplate as sibling with-errors list
    # closures; decomposing would duplicate that Except-bind skeleton.
    "compileStmtList_external_body_with_raw_log_bridged",
    # Raw-log-lifted internal body list closure: identical boilerplate to
    # the external variant with `isInternal := true`.
    "compileStmtList_internal_body_with_raw_log_bridged",
    # tstore list closure mirrors the same compileStmtList head/tail
    # skeleton as sibling list closures; the excess lines come from the
    # doc-comment preamble for the next section (storageArrayPush body
    # closure) being attributed to this proof's span by the measurer.
    "compileStmtList_tstore_bridged",
    # storageArrayPush single-slot closure enumerates the five emitted
    # straight-line statements in the `.block` body: let __array_len =
    # sload(lit slot), mstore(lit 0, lit slot), let __array_base =
    # keccak256(lit 0, lit 32), sstore(add(__array_base, __array_len),
    # valueExpr), and sstore(lit slot, add(__array_len, lit 1)). Each
    # branch builds its own BridgedExpr witness for the composite
    # sload/add expressions; decomposing would yield five trivial
    # single-use helpers whose combined boilerplate exceeds the main
    # proof's line count.
    "compileStmt_storageArrayPush_singleSlot_bridged",
    # storageArrayPush list closure: same compileStmtList head/tail
    # skeleton as sibling list closures; the excess lines come from the
    # doc-comment preamble for the next section (storageArrayPop body
    # closure) being attributed to this proof's span by the measurer.
    "compileStmtList_storageArrayPush_bridged",
    # storageArrayPop single-slot closure enumerates seven emitted
    # statements in the `.block` body including an `if iszero(__array_len)
    # { revert(0, 0) }` guard: let __array_len = sload(lit slot), if_
    # guard, let __array_new_len = sub, mstore(lit 0, lit slot), let
    # __array_base = keccak256, sstore(add(..), lit 0), sstore(lit slot,
    # ident __array_new_len). Each branch builds its own BridgedExpr
    # witness; decomposing would yield seven trivial single-use helpers
    # whose combined boilerplate exceeds the main proof's line count.
    "compileStmt_storageArrayPop_singleSlot_bridged",
    # storageArrayPop list closure: same compileStmtList head/tail
    # skeleton as sibling list closures; the excess lines come from the
    # doc-comment preamble for the next section (setStorageArrayElement
    # body closure) being attributed to this proof's span by the measurer.
    "compileStmtList_storageArrayPop_bridged",
    # setStorageArrayElement single-slot closure enumerates six emitted
    # statements in the `.block` body including an `if
    # iszero(lt(__array_index, __array_len)) { revert(0, 0) }` bounds-check
    # guard: let __array_len = sload, let __array_index = indexExpr, if_
    # guard, mstore(lit 0, lit slot), let __array_base = keccak256,
    # sstore(add(__array_base, __array_index), valueExpr). Each branch
    # builds its own BridgedExpr witness for sload/lt/iszero; decomposing
    # would yield six trivial single-use helpers whose combined
    # boilerplate exceeds the main proof's line count.
    "compileStmt_setStorageArrayElement_singleSlot_bridged",
    # setStorageArrayElement list closure: same compileStmtList head/tail
    # skeleton as sibling list closures; the excess lines come from the
    # doc-comment preamble for the next section (setMappingWord
    # wordOffset ≠ 0 body closure) being attributed to this proof's span
    # by the measurer.
    "compileStmtList_setStorageArrayElement_bridged",
    # setMapping2Word single-slot nonzero-offset closure builds three
    # BridgedExpr witnesses (key1, key2, value), then a nested
    # mappingSlot(mappingSlot(lit slot, key1), key2) outer-slot witness via
    # two `refine BridgedExpr.call "mappingSlot" …` applications, then
    # applies `expr_sstore_add` for the final `sstore(add(outerSlot, lit
    # wordOffset), value)`. Decomposing the nested-mappingSlot witness
    # would yield a trivial single-use helper whose boilerplate exceeds
    # the size saved.
    "compileStmt_setMapping2Word_singleSlot_nonzero_bridged",
    # setMappingWord wordOffset ≠ 0 list closure: same compileStmtList
    # head/tail skeleton as sibling list closures; the excess lines come
    # from the doc-comment preamble for the next section (setMapping2Word
    # wordOffset ≠ 0 body closure) being attributed to this proof's span
    # by the measurer.
    "compileStmtList_mappingWordNonzero_bridged",
    # setMappingChain single-slot closure requires a two-way case split on
    # keyExprs (empty → expr_sstore_lit; non-empty prefix ++ [last] →
    # expr_sstore_mapping) plus the bridgedExpr_foldl_mappingSlot helper
    # application for the prefix chain. The surrounding bind/case-unfold
    # boilerplate across the compileExprList + compileExpr monadic chain
    # inflates the total. Decomposing the two `rcases` branches would each
    # yield a trivial single-use helper whose boilerplate exceeds the save.
    "compileStmt_setMappingChain_singleSlot_bridged",
    # setMapping2Word wordOffset ≠ 0 list closure: prior section's
    # compileStmtList head/tail skeleton pushed over by this section's
    # (setMappingChain) doc-comment preamble being attributed to this
    # proof's span, same pattern as
    # `compileStmtList_setStorageArrayElement_bridged` (`eccc1df9`) and
    # `compileStmtList_mappingWordNonzero_bridged` (`5ef7f4b7`).
    "compileStmtList_mapping2WordNonzero_bridged",
    # Multi-slot setMapping compatibility branch emits an outer
    # `YulStmt.block` wrapping two let-bindings plus N sstore writes
    # (one per slot). The proof must enumerate four concrete membership
    # cases (let __compat_key, let __compat_value, sstore slot0,
    # sstore slot1) before falling through to the generic slotsRest
    # map case via the `bridgedStraightStmts_multiSlot_sstore_mapping`
    # helper. Each ctor call carries six explicit witness arguments
    # (baseExpr, keyExpr, valExpr + their BridgedExpr proofs), which
    # pads the proof without substantive logic. Decomposing the four
    # rcases branches would produce trivial single-use helpers whose
    # boilerplate exceeds the save.
    "compileMappingSlotWrite_multiSlot_bridged",
    # setMappingChain list closure: prior section's compileStmtList
    # head/tail skeleton pushed over by this section's (multi-slot
    # setMapping) doc-comment preamble being attributed to this
    # proof's span, same pattern as
    # `compileStmtList_mapping2WordNonzero_bridged` (`69d3abde`).
    "compileStmtList_mappingChain_bridged",
    # Multi-slot setMapping2 compatibility branch emits an outer
    # `YulStmt.block` wrapping three let-bindings (__compat_key1,
    # __compat_key2, __compat_value) plus N nested-mappingSlot sstore
    # writes (one per slot). The proof must enumerate five concrete
    # membership cases (three let-bindings + sstore slot0 +
    # sstore slot1) before falling through to the generic slotsRest
    # map case via the `bridgedStraightStmts_multiSlot_sstore_mapping2`
    # helper. Each concrete sstore case must also construct a nested
    # `BridgedExpr.call "mappingSlot"` witness inline for the inner
    # mappingSlot subexpression. Decomposing would yield trivial
    # single-use helpers whose boilerplate exceeds the save.
    "compileStmt_setMapping2_multiSlot_bridged",
    # Multi-slot setMapping list closure: prior section's
    # compileStmtList head/tail skeleton pushed over by this
    # section's (multi-slot setMapping2) doc-comment preamble being
    # attributed to this proof's span, same pattern as
    # `compileStmtList_mappingChain_bridged` (`cd135ff7`).
    "compileStmtList_mappingWriteMultiSlot_bridged",
    # Multi-slot setMapping2 list closure: prior section's list
    # skeleton pushed over to 57 lines by the newly appended
    # multi-slot setStructMember section's doc-comment preamble
    # being attributed to this proof's span, same pattern as
    # `compileStmtList_mappingChain_bridged` (`cd135ff7`) and
    # `compileStmtList_mappingWriteMultiSlot_bridged`.
    "compileStmtList_mappingWrite2MultiSlot_bridged",
    # Multi-slot setStructMember2 wordOffset=0 closure: inherent
    # 5-way concrete membership enumeration (3 let-bindings + 2
    # concrete sstore cases with inline nested BridgedExpr.call
    # "mappingSlot" witnesses) before the slotsRest tail helper,
    # same pattern as `compileStmt_setMapping2_multiSlot_bridged`
    # (`defa6150`).
    "compileStmt_setStructMember2_multiSlot_bridged",
    # Multi-slot setStructMember list closure: prior section's list
    # skeleton pushed over to 58 lines by the newly appended
    # multi-slot setStructMember2 section's doc-comment preamble,
    # same displacement pattern as
    # `compileStmtList_mappingWriteMultiSlot_bridged` (`cd135ff7`)
    # and `compileStmtList_mappingWrite2MultiSlot_bridged` (`29634900`).
    "compileStmtList_structMemberMultiSlot_bridged",
    # Multi-slot setStructMember2 list closure: prior section's list
    # skeleton pushed over to 61 lines by the newly appended
    # multi-slot setMappingWord wordOffset=0 section's doc-comment
    # preamble, same displacement pattern as
    # `compileStmtList_mappingWriteMultiSlot_bridged` (`cd135ff7`),
    # `compileStmtList_mappingWrite2MultiSlot_bridged` (`29634900`),
    # and `compileStmtList_structMemberMultiSlot_bridged` (`3b331fc7`).
    "compileStmtList_structMember2MultiSlot_bridged",
    # Multi-slot setMapping2Word wordOffset=0 closure: inherent
    # 5-way concrete membership enumeration (3 let-bindings + 2
    # concrete sstore cases with inline nested BridgedExpr.call
    # "mappingSlot" witnesses) before the slotsRest tail helper,
    # same pattern as `compileStmt_setMapping2_multiSlot_bridged`
    # (`defa6150`) and `compileStmt_setStructMember2_multiSlot_bridged`
    # (`3b331fc7`).
    "compileStmt_setMapping2Word_multiSlot_bridged",
    # Multi-slot setMappingWord wordOffset=0 list closure: prior
    # section's list skeleton pushed over to 60 lines by the newly
    # appended multi-slot setMapping2Word wordOffset=0 section's
    # doc-comment preamble, same displacement pattern as
    # `compileStmtList_mappingWriteMultiSlot_bridged` (`cd135ff7`),
    # `compileStmtList_mappingWrite2MultiSlot_bridged` (`29634900`),
    # `compileStmtList_structMemberMultiSlot_bridged` (`3b331fc7`),
    # and `compileStmtList_structMember2MultiSlot_bridged` (`112e2995`).
    "compileStmtList_mappingWordMultiSlot_bridged",
    # Multi-slot setMapping2Word wordOffset=0 list closure: prior
    # section's list skeleton pushed over to 66 lines by the newly
    # appended multi-slot setMappingWord wordOffset≠0 section's
    # doc-comment preamble, same displacement pattern as prior
    # multi-slot list closures.
    "compileStmtList_mapping2WordMultiSlot_bridged",
    # Multi-slot setMapping2Word wordOffset≠0 closure: 126 lines
    # inherent — 5-way concrete membership enumeration over outer
    # block (let __compat_key1, let __compat_key2, let __compat_value,
    # sstore_add(slot0), sstore_add(slot1), slotsRest tail), each
    # sstore_add head carrying a nested mappingSlot(mappingSlot(...))
    # bridged witness. Mirrors `compileStmt_setMapping2Word_multiSlot_bridged`
    # (wordOffset=0, 97 lines allowlisted above) plus the extra `add`
    # layer boilerplate.
    "compileStmt_setMapping2Word_multiSlot_nonzero_bridged",
    # Multi-slot setMappingWord wordOffset≠0 list closure: prior
    # section's list skeleton pushed over to 70 lines by the newly
    # appended multi-slot setMapping2Word wordOffset≠0 section's
    # doc-comment preamble + helper + predicate, same displacement
    # pattern as prior multi-slot list closures.
    "compileStmtList_mappingWordMultiSlotNonzero_bridged",
    # Multi-slot setMapping2Word wordOffset≠0 `slots.map` helper:
    # 61 lines inherent — per-slot element is `expr_sstore_add` whose
    # inner mappingSlot arg is itself a nested mappingSlot, requiring
    # both an inner and outer BridgedExpr.call derivation before
    # invoking the `expr_sstore_add` ctor. No clean decomposition.
    "bridgedStraightStmts_multiSlot_sstore_mapping2_add",
    # Multi-slot setMapping2Word wordOffset≠0 list closure: prior
    # section's list skeleton pushed over to 59 lines by the newly
    # appended multi-slot setStructMember wordOffset≠0 section's
    # doc-comment preamble + predicate, same displacement pattern as
    # prior multi-slot list closures.
    "compileStmtList_mapping2WordMultiSlotNonzero_bridged",
    # Multi-slot setStructMember2 wordOffset≠0 closure: mirrors
    # setMapping2Word wordOffset≠0 multi-slot (97+ lines) via the
    # struct-member2 ctor. Five-way List.mem_cons enumeration over
    # compileSetStructMember2's emitted block (three lets + two
    # sstore_add heads over nested mappingSlot(mappingSlot(...)) +
    # slotsRest tail), with member.wordOffset threaded into each
    # sstore_add and the multi-slot sstore_mapping2_add helper.
    "compileStmt_setStructMember2_multiSlot_nonzero_bridged",
    # Multi-slot setStructMember wordOffset≠0 list closure: displaced
    # from 59 to 63 lines by the newly appended multi-slot
    # setStructMember2 wordOffset≠0 section's doc-comment preamble +
    # predicate, same displacement pattern as prior multi-slot list
    # closures.
    "compileStmtList_structMemberMultiSlotNonzero_bridged",
    # Single-slot setMappingPackedWord wordOffset=0 closure: 115-line
    # span enumerates the one-element list wrapping a block of four
    # `let_` bindings (value / packed / slot_word / slot_cleared, each
    # an `and`/`sload`/`not` call) plus a terminating
    # `expr_sstore_mapping` with a three-level `or(ident, shl(lit,
    # ident))` value. Every inner call goes through `bridgedBuiltins`,
    # so decomposition would only multiply identical `BridgedExpr.call`
    # boilerplate. First packed-bits body closure — no cleaner factoring
    # available until a shared `and`/`or`/`not`/`shl` BridgedExpr helper
    # lands.
    "compileStmt_setMappingPackedWord_singleSlot_bridged",
    # Single-slot setMappingPackedWord wordOffset≠0 source body closure:
    # 132-line span structurally mirrors the wordOffset=0 variant (5-way
    # rcases over the emitted block) with the added `add(mappingSlot,
    # lit wordOffset)` BridgedExpr witness used by both the `sload` arg
    # and the terminating `expr_sstore_add`. Same decomposition rationale
    # as the wordOffset=0 sibling.
    "compileStmt_setMappingPackedWord_singleSlot_nonzero_bridged",
    # Single-slot setMappingPackedWord wordOffset=0 list closure:
    # displaced from 45 to 59 lines by the newly appended wordOffset≠0
    # inductive declaration which terminates the proof span (same
    # displacement pattern as prior adjacent closures; proof body
    # unchanged).
    "compileStmtList_mappingPackedWord_bridged",
    # Multi-slot setMappingPackedWord wordOffset=0 inner-block helper:
    # 90-line span builds the `mappingSlot` BridgedExpr once and then
    # enumerates the three inner-block stmts (sload-let, and-not
    # cleared, or-shl sstore) for a single slot. Decomposing would
    # multiply identical `BridgedExpr.call` boilerplate across three
    # sibling helpers.
    "bridgedStmt_packedInnerBlock_wordOffsetZero",
    # Multi-slot setMappingPackedWord wordOffset=0 main closure:
    # 67-line span enumerates the outer block prefix
    # (let_key / let_value / let_packed) and the slots.map inner blocks
    # (slot0, slot1, slotsRest via the map helper). Each branch reuses
    # the inner-block helper; further decomposition yields no clear
    # gain.
    "compileStmt_setMappingPackedWord_multiSlot_bridged",
    # Single-slot setMappingPackedWord wordOffset≠0 list closure:
    # displaced by the newly appended multi-slot helpers and main
    # theorem which terminate the proof span (same displacement
    # pattern as prior adjacent closures; proof body unchanged).
    "compileStmtList_mappingPackedWordNonzero_bridged",
    # Multi-slot setMappingPackedWord wordOffset≠0 inner-block helper:
    # 108-line span builds `mappingSlot` and `add(mappingSlot, lit
    # wordOffset)` BridgedExpr witnesses once and then enumerates the
    # three inner-block stmts (sload-let over add, and-not cleared,
    # expr_sstore_add terminator) for a single slot. Decomposing would
    # multiply identical `BridgedExpr.call` boilerplate across three
    # sibling helpers.
    "bridgedStmt_packedInnerBlock_wordOffsetNonzero",
    # Multi-slot setMappingPackedWord wordOffset≠0 main closure: 70-
    # line span enumerates outer block prefix (let_key / let_value /
    # let_packed) and the slots.map inner blocks (slot0, slot1,
    # slotsRest via the map helper). Each branch reuses the inner-
    # block helper; further decomposition yields no clear gain.
    "compileStmt_setMappingPackedWord_multiSlot_nonzero_bridged",
    # Multi-slot setMappingPackedWord wordOffset=0 list closure:
    # displaced from 45 to 63 lines by the newly appended multi-slot
    # wordOffset≠0 helpers + predicate + main theorem (proof body
    # unchanged; same displacement pattern as prior adjacent
    # closures).
    "compileStmtList_mappingPackedWordMultiSlot_bridged",
    # Multi-slot setMappingPackedWord wordOffset≠0 list closure: same
    # compileStmtList head/tail skeleton as its wordOffset=0 sibling; the
    # extra span is the adjacent safe-body aggregation preamble, not unique
    # proof logic.
    "compileStmtList_mappingPackedWordMultiSlotNonzero_bridged",
    # Multi-slot setStructMember2 wordOffset≠0 list closure: displaced
    # from 45 to 63 lines by the newly appended single-slot
    # setMappingPackedWord section's doc-comment preamble + predicate,
    # same displacement pattern as prior multi-slot list closures
    # (proof body unchanged).
    "compileStmtList_structMember2MultiSlotNonzero_bridged",
    # Universal safe-body aggregation is one constructor dispatch over
    # BridgedSafeStmts. Each branch delegates to an existing fragment-specific
    # closure theorem; splitting would create a parallel dispatch helper with
    # the same 24-case shape.
    "compileStmtList_always_bridged",
    # Universal no-function-definition aggregation mirrors
    # compileStmtList_always_bridged: one constructor dispatch over
    # BridgedSafeStmts, with each branch delegating to a fragment-specific
    # noFuncDefs theorem.
    "compileStmtList_always_noFuncDefs",
    # --- Misc ---
    "findUniqueInternalFunction",
    # Native generated-switch block append/error lemmas mirror the existing
    # ok-append proof and keep the fuel arithmetic visible in one place for
    # the halt-before-default dispatcher cases.
    "exec_block_append_error",
    "exec_block_append_prefix_error",
    # Native generated-switch selected-hit error chain is the error analogue of
    # the preserved selected-hit chain; the long span is the prefix induction
    # needed to prove later cases/default are unreachable after a halt.
    "exec_nativeSwitchCaseIfs_prefix_hit_error_fuel",
}

# Directories containing proof files to scan.
PROOF_DIRS = [
    ROOT / "Compiler" / "Proofs",
    ROOT / "Verity" / "Proofs",
    ROOT / "Verity" / "Core",
    ROOT / "Contracts",
]


def _is_proof_terminator(line: str) -> bool:
    """Return True if *line* starts a new declaration or ends a scope."""
    return bool(_DECL_RE.match(line) or _END_RE.match(line) or _SECTION_RE.match(line))


def measure_proofs(lean_file: Path) -> list[tuple[str, int, int]]:
    """Return (name, start_line_1indexed, length) for every theorem/lemma."""
    text = lean_file.read_text(encoding="utf-8")
    stripped = strip_lean_comments(text)
    lines = stripped.splitlines()

    results: list[tuple[str, int, int]] = []
    current_name: str | None = None
    current_start: int | None = None

    for i, line in enumerate(lines):
        m = THEOREM_RE.match(line)
        if m:
            # Close previous proof span.
            if current_name is not None and current_start is not None:
                results.append((current_name, current_start + 1, i - current_start))
            current_name = m.group("name")
            current_start = i
        elif current_name is not None and _is_proof_terminator(line):
            results.append((current_name, current_start + 1, i - current_start))  # type: ignore[arg-type]
            # The terminator might itself be a new theorem via the THEOREM_RE branch
            # above, but since THEOREM_RE didn't match, this is a def/end/etc.
            current_name = None
            current_start = None

    # Handle proof at end of file.
    if current_name is not None and current_start is not None:
        results.append((current_name, current_start + 1, len(lines) - current_start))

    return results


def main() -> None:
    parser = argparse.ArgumentParser(description="Check proof lengths.")
    parser.add_argument(
        "--format",
        choices=["text", "markdown"],
        default="text",
        help="Output format (default: text)",
    )
    args = parser.parse_args()

    all_proofs: list[tuple[Path, str, int, int]] = []  # (file, name, line, length)
    for proof_dir in PROOF_DIRS:
        if not proof_dir.exists():
            continue
        for lean_file in sorted(proof_dir.rglob("*.lean")):
            for name, line, length in measure_proofs(lean_file):
                all_proofs.append((lean_file, name, line, length))

    # Partition into buckets.
    violations: list[tuple[Path, str, int, int]] = []
    warnings: list[tuple[Path, str, int, int]] = []
    allowlisted: list[tuple[Path, str, int, int]] = []

    for file, name, line, length in all_proofs:
        if length > HARD_LIMIT:
            if name in ALLOWLIST:
                allowlisted.append((file, name, line, length))
            else:
                violations.append((file, name, line, length))
        elif length > SOFT_LIMIT:
            warnings.append((file, name, line, length))

    total = len(all_proofs)
    under_soft = total - len(warnings) - len(allowlisted) - len(violations)

    if args.format == "markdown":
        _print_markdown(total, under_soft, warnings, allowlisted, violations)
    else:
        _print_text(total, under_soft, warnings, allowlisted, violations)

    if violations:
        sys.exit(1)


def _print_text(
    total: int,
    under_soft: int,
    warnings: list[tuple[Path, str, int, int]],
    allowlisted: list[tuple[Path, str, int, int]],
    violations: list[tuple[Path, str, int, int]],
) -> None:
    print(f"Proof length check: {total} proofs scanned.")
    print(f"  {under_soft} under {SOFT_LIMIT} lines (good)")
    print(f"  {len(warnings)} between {SOFT_LIMIT}-{HARD_LIMIT} lines (acceptable)")
    print(f"  {len(allowlisted)} over {HARD_LIMIT} lines (allowlisted)")

    if violations:
        print(
            f"\nERROR: {len(violations)} proof(s) exceed {HARD_LIMIT} lines "
            f"without an allowlist entry:",
            file=sys.stderr,
        )
        for file, name, line, length in sorted(violations, key=lambda x: -x[3]):
            rel = file.relative_to(ROOT)
            print(
                f"  {rel}:{line}: {name} ({length} lines, limit {HARD_LIMIT})",
                file=sys.stderr,
            )
        print(
            f"\nTo fix: decompose the proof into smaller lemmas, or add the "
            f"theorem name to ALLOWLIST in scripts/check_proof_length.py with "
            f"a justification comment in the PR.",
            file=sys.stderr,
        )
    else:
        print(
            f"\nProof length check passed. "
            f"No new proofs exceed the {HARD_LIMIT}-line hard limit."
        )


def _print_markdown(
    total: int,
    under_soft: int,
    warnings: list[tuple[Path, str, int, int]],
    allowlisted: list[tuple[Path, str, int, int]],
    violations: list[tuple[Path, str, int, int]],
) -> None:
    print("### Proof Length Distribution\n")
    print(f"| Range | Count | Percentage |")
    print(f"| :-- | --: | --: |")
    pct = lambda n: f"{100 * n / total:.0f}%" if total else "0%"
    print(f"| Under {SOFT_LIMIT} lines | {under_soft} | {pct(under_soft)} |")
    print(f"| {SOFT_LIMIT}-{HARD_LIMIT} lines | {len(warnings)} | {pct(len(warnings))} |")
    print(f"| Over {HARD_LIMIT} lines (allowlisted) | {len(allowlisted)} | {pct(len(allowlisted))} |")
    if violations:
        print(f"| **Over {HARD_LIMIT} lines (NEW, failing)** | **{len(violations)}** | **{pct(len(violations))}** |")
    print(f"| **Total** | **{total}** | 100% |")


if __name__ == "__main__":
    main()
