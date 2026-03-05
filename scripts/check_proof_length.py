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
    # Semantic bridge proofs (Issue #998) — hand-composed EDSL≡IR per function:
    "simpleStorage_store_semantic_bridge",
    "simpleStorage_retrieve_semantic_bridge",
    "counter_decrement_semantic_bridge",
    "owned_transferOwnership_semantic_bridge",
    "safeCounter_increment_semantic_bridge",
    "safeCounter_decrement_semantic_bridge",
    "ownedCounter_decrement_semantic_bridge",
    "ownedCounter_transferOwnership_semantic_bridge",
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
}

# Directories containing proof files to scan.
PROOF_DIRS = [
    ROOT / "Compiler" / "Proofs",
    ROOT / "Verity" / "Proofs",
    ROOT / "Verity" / "Core",
    ROOT / "Verity" / "Examples",
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
