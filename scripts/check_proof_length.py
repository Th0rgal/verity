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
    "compileStmtList_core_ok",
    "compileStmtList_terminal_core_ok",
    "compileStmtList_terminal_core_ok_nonempty",
    "compileStmtList_terminal_ite_ok_inv",
    "compileStmt_terminal_ite_ok_inv",
    "compileStmt_ok_any_scope_aux",
    "eval_compileExpr_core_onExpr",
    "evalExpr_lt_evmModulus_core_onExpr",
    "eval_compileRequireFailCond_core_onExpr",
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
    "stmtTouchesUnsupportedContractSurface_eq_false_of_featureClosed",
    "SupportedStmtList.helperSurfaceClosed",
    "SupportedStmtList.internalHelperCallNames_nil",
    "supportedStmtList_usesStorageArrayElement_false",
    "supportedStmtList_usesDynamicBytesEq_false",
    "supportedStmtList_usesArrayElement_false",
    # --- Mapping slot and field resolution proofs ---
    "findResolvedFieldAtSlotCopyFrom_of_member",
    "firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_member",
    "encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_eq_written",
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
    "compile_preserves_semantics",
    "compile_preserves_semantics_except_mapping_writes",
    "compile_preserves_semantics_except_mapping_writes_stmtSafety",
    "initialIRStateForTx_matches_runtime",
    "resultsMatch_of_execResultsAligned",
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
    # --- Contract feature fixtures ---
    "literalMappingWrite_calldataFits",
    # --- Yul generation / Layer 3 proofs ---
    "yulCodegen_preserves_semantics",
    "stmt_and_stmts_equiv",
    "execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv",
    "execYulFuel_succ_eq",
    "exec_switchCaseBody_revert_of_short",
    "exec_switchCaseBody_continue_of_long",
    "SwitchCaseBodyBridge_short",
    "SwitchCaseBodyBridge",
    "layer3_contract_preserves_semantics",
    # Thin EVMYulLean EndToEnd wrapper; signature carries explicit body-closure
    # witnesses and the proof mostly forwards existing Layer-3 hypotheses.
    "layer3_contract_preserves_semantics_evmYulLean",
    # --- End-to-end proofs ---
    "simpleStorage_endToEnd",
    # Thin public wrapper; the scanner counts the trailing Phase 4 summary
    # comment in its theorem span.
    "simpleStorage_endToEnd_evmYulLean",
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
    # signextend proof requires 4-case byte-index analysis + bit-level shift
    # semantics matching; structural complexity is inherent to the operation.
    "signextend_uint256_eq",
    # backends_agree dispatch proof case-splits all 36 bridged builtins;
    # each branch is one line but 36 builtins + headers exceed 50 lines.
    "backends_agree_on_bridged_builtins",
    # Backend-parameterized mirror of execYulFuel; long by construction because
    # it preserves all statement cases while swapping only expression backend.
    "execYulFuelWithBackend",
    # Recovery proof mirrors the executor's statement case split; each branch is
    # direct simplification back to execYulFuel.
    "execYulFuelWithBackend_verity_eq",
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
    "yulCodegen_preserves_semantics_evmYulLean",
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
    # --- Misc ---
    "findUniqueInternalFunction",
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
