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
    "stmtListGenericCore_singleton_requireLiteralGuardFamilyClause",
    "stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface",
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
    "supported_function_correct_with_body_interface_except_mapping_writes",
    # --- Legacy compatibility and dispatch ---
    "legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields_resolved",
    "legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface_exceptMappingWrites",
    "legacyCompatibleExternalStmtList_of_compileSetStructMember2_ok",
    "interpretContract_correct_of_compiled_functions",
    "compile_preserves_semantics",
    "compile_preserves_semantics_except_mapping_writes",
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
    # --- Contract proofs (Contracts/) ---
    "constructor_increment_getCount",
    "add_one_preserves_order_iff_no_overflow",
    "sub_add_cancel_of_lt",
    "sub_add_cancel_left",
    "safeDiv_result_le_numerator",
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
