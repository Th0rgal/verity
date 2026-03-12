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
    "ledger_transfer_correct_sufficient",
    "token_transfer_correct_sufficient",
    "token_mint_correct_as_owner",
    "all_stmts_equiv",
    "sub_add_cancel_of_lt",
    "safeIncrement_correct",
    "execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv",
    "simpleToken_owner_correct",
    "yulCodegen_preserves_semantics",
    "token_transfer_preserves_total_balance",
    "safeDecrement_correct",
    "add_one_preserves_order_iff_no_overflow",
    "ledger_transfer_preserves_total",
    "ledger_withdraw_correct_sufficient",
    "resultsMatch_of_execResultsAligned",
    "constructor_increment_getCount",
    "sub_add_cancel_left",
    "ledger_deposit_correct",
    "safeDiv_result_le_numerator",
    # End-to-end composition proofs (Issue #998) — compose Layers 2+3:
    "simpleStorage_endToEnd",
    "simpleStorage_retrieve_edsl_to_yul",
    "yulBody_from_state_eq_yulBody",
    # Statement equivalence core recursion proof (Lean 4.22 transport-heavy);
    # decomposition planned after stabilization of helper lemmas.
    "stmt_and_stmts_equiv",
    # Issue #1060 stabilization: fragment-dispatch semantic theorem currently
    # centralizes many continuation cases; temporary allowlist to unblock CI
    # while decomposing into helper lemmas in follow-up 2.2 slices.
    "compile_require_family_clauses_then_tail_semantics",
    # Morpho Blue admin function compilation fragments — mechanical proofs
    # whose length comes from spelling out the full typed-IR output, not
    # from proof complexity (each closes with a single simp+rfl).
    "compileStmts_letCallerLetStorageAddrReqEqReqNeqSetStorageAddrParamStop_run",
    "compileStmts_letCallerLetStorageAddrReqEqLetMappingReqEqLitSetMappingStop_run",
    "compileStmts_letCallerLetStorageAddrReqEqLetMappingUintReqEqLitReqLtSetMappingUintStop_run",
    "compileStmts_letCallerLetMapping2IteParamReqSetMapping2Stop_run",
    # Guard no-op bridge for switch-case execution (Issue #1094 follow-up):
    # long due explicit Yul expression reduction over reducible exec semantics.
    "exec_calldatasizeGuard_noop",
    # Execution-context dispatch helpers in Preservation.lean; both are long due
    # transport-heavy local normalization over reducible Yul/IR state updates.
    "exec_callvalueGuard_noop",
    "evalSelectorExpr_setVar_has_selector",
    # Generic Layer 2 param-loading list theorem (Issue #1510 / PR #1554):
    # centralizes the scalar-head induction for `genParamLoadBodyFrom`; further
    # decomposition is possible later, but keeping the recursion in one place
    # is currently the least duplicated proof boundary for compileFunctionSpec.
    "exec_genParamLoadBodyFrom_supported_then",
    # Generic Layer 2 function assembly theorem (Issue #1510 / PR #1554):
    # packages raw-arg prebinding, param-load normalization, and IR result
    # construction into one reusable compiler-facing boundary ahead of the
    # remaining body-correctness proof.
    "exec_compiledFunctionIR_of_body",
    # Generic Layer 2 compileFunctionSpec assembly theorem (Issue #1510 / PR #1554):
    # centralizes the successful compiler-output shape plus source/IR function
    # packaging so the remaining work stays focused on one generic body theorem
    # instead of repeating function-level composition in later dispatch/contract proofs.
    "compileFunctionSpec_correct_of_body",
    # Generic Layer 2 supported-field normalization wrapper (Issue #1510 / PR #1554):
    # isolates the `CompilationModel.compile` field-normalization boundary so later
    # compile-facing theorems can reuse the existing function correctness theorem
    # without re-proving slot-alias normalization at each call site.
    # Generic Layer 2 dispatch assembly theorem (Issue #1510 / PR #1554):
    # intentionally keeps selector lookup, arity shortfall, and revert packaging
    # in one compiler-facing theorem so later whole-contract correctness can
    # consume a single dispatch boundary instead of reassembling these cases.
    "interpretContract_correct_of_compiled_functions",
    # Generic Layer 2 proof-spine carryover from PR #1554:
    # these theorems predate the hard-limit gate and currently centralize the
    # structural-fuel/whole-fuel transports, terminal-ite normalization, and
    # compiler-facing assembly steps needed to keep the partially generic Layer 2
    # boundary stable. Splitting them is follow-up work, but allowlisting keeps
    # CI green without mutating the proof architecture during merge resolution.
    "bindSupportedParams_lookupBinding",
    "compileExpr_core_ok",
    "eval_compileExpr_core_onExpr",
    "evalExpr_lt_evmModulus_core_onExpr",
    "eval_compileExpr_logicalAnd_of_compiled",
    "eval_compileExpr_logicalOr_of_compiled",
    "compileRequireFailCond_core_ok",
    "eval_compileRequireFailCond_core_onExpr",
    "exec_compileStmt_return_core",
    "exec_compileStmt_return_core_extraFuel",
    "compileStmtList_core_ok",
    "compileStmt_terminal_ite_ok_inv",
    "compileStmtList_terminal_ite_ok_inv",
    "compileStmtList_terminal_core_ok",
    "compileStmtList_terminal_core_ok_nonempty",
    "exec_compileStmtList_core",
    "exec_compileStmtList_core_extraFuel",
    "exec_compileStmtList_terminal_core_sizeOf_extraFuel",
    "initialIRStateForTx_matches_runtime",
    "exec_compiledFunctionIR_of_body_extraFuel",
    "supported_function_body_correct_from_exact_state_core",
    "supported_function_body_correct_from_exact_state_core_extraFuel",
    "supported_function_body_correct_from_exact_state_terminal_core_extraFuel",
    "compileFunctionSpec_correct_of_body_supported_extraFuel",
    "supported_function_correct",
    "compileFunctionSpec_correct_generic",
    "compile_preserves_semantics",
    # Issue #1564 / PR #1606:
    # these are the pre-existing long terminal-ite branch-entry transport
    # proofs, now exposed as public lemmas so later Layer 2 induction work can
    # reuse them directly. The proof bodies are unchanged; only the exported
    # names shifted, so the historical allowlist needs to track the new names.
    "execIRStmt_compiled_terminal_ite_then_branch_entry",
    "execIRStmt_compiled_terminal_ite_else_branch_entry",
    "execIRStmt_compiled_terminal_ite_else_branch_entry_tailFuel",
    "execStmtList_terminal_core_not_continue",
    "execIRStmts_compiled_terminal_ite_then_of_irExec",
    "execIRStmts_compiled_terminal_ite_else_of_irExec",
    "stmtResultMatchesIRExec_compiled_terminal_ite_then",
    "stmtResultMatchesIRExec_compiled_terminal_ite_else",
    "execIRStmts_compiled_return_core_append_wholeFuel",
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
    "exec_genParamLoads_supported_then_extraFuel",
    # Generic Layer 3 switch-case bridge shrink follow-up:
    # these proofs are transport-heavy reductions over reducible Yul semantics,
    # and are kept intact while the remaining dispatch axiom is narrowed further.
    "exec_switchCaseBody_revert_of_short",
    "SwitchCaseBodyBridge_short",
    # Layer 3 switch-case axiom decomposition (SwitchCaseBodyBridge narrowing):
    # success-path guard stepping mirrors the revert-path structure and is long
    # for the same reason (explicit case-split over payable + fuel arithmetic).
    "exec_switchCaseBody_continue_of_long",
    # Composition theorem bridging proved guard stepping + narrower body axiom;
    # long due to explicit fuel case-split and interpretYulRuntime unfolding.
    "SwitchCaseBodyBridge",
    # Issue #1563 — fuel adequacy proof (axiom elimination):
    # strong induction over sizeOf covering all YulStmt constructors; length
    # comes from exhaustive case-split, not proof complexity.
    "execYulFuel_succ_eq",
    # Issue #1563 — end-to-end composition now threads loop-free hypothesis;
    # marginally above limit (55 lines) due to added precondition plumbing.
    "layer3_contract_preserves_semantics",
    # Issue #1618 / PR #1620 — generic statement-induction library:
    # these proofs are the initial axiom-elimination spine for Layer 2. Most are
    # structural inductions or compiler-surface assembly lemmas that currently
    # centralize scope discipline, storage-write transport, and fuel arithmetic so
    # the new generic theorem has a single reusable proof boundary. They should be
    # decomposed further in follow-up cleanup, but allowlisting them keeps the
    # migration reviewable without forcing a second large refactor in the same PR.
    "exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false",
    "stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface",
    "exprBoundNamesInScope_of_validateScopedExprIdentifiers_core",
    "stmtListScopeDiscipline_of_validateScopedStmtListIdentifiers",
    "scopeNamesPresent_foldl_stmtNextScope_of_validateScopedStmtListIdentifiers",
    "stmtListScopeDiscipline_scope_names",
    "compiledStmtStep_require",
    "findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_member",
    "firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_member",
    "compiledStmtStep_setStorage_singleSlot",
    "compiledStmtStep_setStorage_aliasSlots",
    "compiledStmtStep_setStorage_of_validateIdentifierShapes",
    "compiledStmtStep_setStorage_of_validateIdentifierShapes_of_scopeDiscipline",
    "compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences_of_compileStmtList",
    "compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences_of_compileStmtList_of_bodySurface",
    "compiledStmtStep_ite",
    "stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded",
    "stmtListGenericCore_of_stmtListTerminalCore_of_scopeNamesIncluded",
    "exec_compileStmtList_generic_sizeOf_extraFuel_step",
    "supported_function_body_correct_from_exact_state_generic",
    # Issue #1630 / helper-semantics retarget follow-up:
    # this theorem is the helper-aware wrapper around the existing generic body
    # proof while helper-summary soundness/rank evidence is still threaded only
    # partway through the stack. Its length comes from preserving the generic
    # body theorem surface during the semantics retarget, not from novel proof
    # complexity in the wrapper itself.
    "supported_function_body_correct_from_exact_state_generic_with_helpers",
    # Issue #1630 / PR #1639 — helper-aware stmt retarget seam isolation:
    # this theorem performs the constructor-by-constructor stmt-list lift from
    # residual expr-statement compatibility to full legacy-compatible external
    # stmt-list compatibility. Its length comes from spelling out the remaining
    # compiled-side transport cases once, so the named stmt-subgoal interface
    # can shrink to the real semantic core instead of carrying separate if/block
    # obligations.
    "execIRStmtsWithInternals_eq_execIRStmts_of_exprCompatibility",
    # Issue #1630 / PR #1633 — helper-aware source-semantics compatibility:
    # this mutual-recursion theorem centralizes the constructor-by-constructor
    # collapse from helper-aware expression evaluation back to the legacy
    # helper-free semantics under the temporary fail-closed helper boundary.
    # Splitting it further is follow-up cleanup once helper-summary composition
    # replaces the compatibility path; for now keeping the recursion in one
    # theorem avoids duplicating the structural cases across the paired list/stmt
    # compatibility lemmas introduced by the new proof interface inventory.
    "evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed",
    # Issue #1630 / PR #1633 follow-up — helper-proof theorem-surface adapters:
    # these declarations are intentionally long because they mirror the existing
    # generic Layer 2 theorem signatures while adding the explicit helper-proof
    # slot. The proof bodies are thin wrappers around the existing theorems; the
    # line count comes from preserving the stable public API shape, not from
    # proof complexity.
    "supported_function_correct_with_helper_proofs",
    "interpretContract_correct_of_compiled_functions_with_helper_proofs",
    "compileFunctionSpec_correct_generic_with_helper_proofs",
    "compile_preserves_semantics_with_helper_proofs",
    # Issue #1638 / PR #1639 — helper-aware compiled-target retarget wrappers:
    # these theorems preserve the public Layer 2 theorem signatures while
    # swapping in the helper-aware compiled semantics target or goal surface.
    # They are mostly API-preserving composition lemmas; decomposition is
    # follow-up cleanup once the remaining stmt-level conservative-extension
    # theorem lands and the helper-aware path becomes the default theorem stack.
    "compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir",
    "interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir",
    "interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir_goal",
    "compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed",
    # Issue #1638 / PR #1639 — compiled-side helper retarget seam:
    # this theorem is the one list-composition proof that shows the open helper
    # blocker lives at single-statement compatibility rather than list plumbing.
    # Its length comes from the constructor-by-constructor composition over the
    # legacy-compatible Yul stmt-list fragment.
    "execIRStmtsWithInternals_eq_execIRStmts_of_stmtCompatibility",
    # Issue #1638 / PR #1639 follow-up — closing the helper-free conservative-
    # extension theorem on the legacy-compatible runtime subset currently
    # requires one explicit constructor-by-constructor `sstore` split and one
    # explicit expr-statement case split over dedicated builtin statement
    # forms. These are the final closed helper-free semantic proofs; splitting
    # them further would mostly duplicate the same reduced-form branches.
    "execIRStmtWithInternals_eq_execIRStmt_sstore_of_no_internal",
    "execIRStmtWithInternals_eq_execIRStmt_expr_of_no_internal",
    # Issue #1630 / PR #1633 — feature-interface compatibility bridge:
    # this private theorem is the one place that folds the split `core` / `state`
    # / `calls` booleans back into the legacy `exprTouchesUnsupportedContractSurface`
    # predicate while the generic body proof still consumes the old boundary.
    # Decomposing it now would only spread the temporary compatibility transport.
    "exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed",
    "firstFieldWriteSlotConflict_eq_none_of_validateCompileInputs",
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
