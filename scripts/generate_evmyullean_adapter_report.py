#!/usr/bin/env python3
"""Generate/check deterministic EVMYulLean adapter coverage report artifact.

Usage:
    python3 scripts/generate_evmyullean_adapter_report.py
    python3 scripts/generate_evmyullean_adapter_report.py --check
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from property_utils import ROOT

BACKENDS_DIR = (
    ROOT / "Compiler" / "Proofs" / "YulGeneration" / "Backends"
)
ADAPTER_FILE = BACKENDS_DIR / "EvmYulLeanAdapter.lean"
BRIDGE_LEMMAS_FILE = BACKENDS_DIR / "EvmYulLeanBridgeLemmas.lean"
BRIDGE_TEST_FILE = BACKENDS_DIR / "EvmYulLeanBridgeTest.lean"
CORRECTNESS_FILE = BACKENDS_DIR / "EvmYulLeanAdapterCorrectness.lean"
DEFAULT_OUTPUT = ROOT / "artifacts" / "evmyullean_adapter_report.json"

EXPECTED_EXPR_CASES = ["lit", "hex", "str", "ident", "call"]
EXPECTED_STMT_CASES = ["comment", "let_", "letMany", "assign", "expr", "leave", "if_", "for_", "switch", "block", "funcDef"]

CASE_RE = re.compile(r"^\s*\|\s*\.([A-Za-z0-9_']+)")
GAP_RE = re.compile(r'\.error\s+"([^"]+)"')
EVAL_STUB_RE = re.compile(r"def\s+evalBuiltinCallViaEvmYulLean[\s\S]*?:\s*Option\s+Nat\s*:=\s*none")

# Regex for lookupPrimOp string-keyed match arms: | "name" => some .OP
PRIMOP_RE = re.compile(r'^\s*\|\s*"([a-z0-9_]+)"\s+=>\s*some\s+\.', re.MULTILINE)

# Regex for evalPureBuiltinViaEvmYulLean match arms: | "name", [args] => some (...)
PURE_BRIDGE_RE = re.compile(r'^\s*\|\s*"([a-z0-9_]+)",\s*\[', re.MULTILINE)

# Regex for universal bridge lemmas: theorem evalBuiltinCall_NAME_bridge
BRIDGE_LEMMA_RE = re.compile(r'theorem\s+evalBuiltinCall_(\w+)_bridge\b')

# Regex to extract individual examples (multi-line, split on `example`)
EXAMPLE_SPLIT_RE = re.compile(r'\bexample\b')

# Regex for builtins in bridge equivalence tests (both verityEval and bridgeEval present)
VERITY_EVAL_RE = re.compile(r'verityEval\w*\s+"([a-z0-9_]+)"')
BRIDGE_EVAL_RE = re.compile(r'bridgeEval\s+"([a-z0-9_]+)"')

# Count native_decide occurrences
NATIVE_DECIDE_RE = re.compile(r'by\s+native_decide')

# Regex for correctness theorems: theorem NAME (including names with apostrophes)
# Handles optional attributes (@[simp], @[ext], etc.) and modifiers before theorem.
CORRECTNESS_THEOREM_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected)\s+)*theorem\s+([\w']+)",
    re.MULTILINE,
)


def _strip_lean_comments(text: str) -> str:
    """Remove Lean line/block comments while preserving line structure."""
    result: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    while i < n:
        if block_depth > 0:
            if text.startswith("/-", i):
                block_depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                block_depth -= 1
                i += 2
                continue
            if text[i] == "\n":
                result.append("\n")
            i += 1
            continue

        if text.startswith("--", i):
            newline = text.find("\n", i)
            if newline == -1:
                break
            result.append("\n")
            i = newline + 1
            continue
        if text.startswith("/-", i):
            block_depth = 1
            i += 2
            continue

        result.append(text[i])
        i += 1
    return "".join(result)


def _extract_block(text: str, start_marker: str, end_marker: str) -> list[str]:
    start = text.find(start_marker)
    if start < 0:
        raise ValueError(f"Could not find block start marker: {start_marker}")
    end = text.find(end_marker, start)
    if end < 0:
        raise ValueError(f"Could not find block end marker: {end_marker}")
    return text[start:end].splitlines()


def _parse_cases(lines: list[str]) -> dict[str, str]:
    clauses: dict[str, list[str]] = {}
    current: str | None = None
    for line in lines:
        m = CASE_RE.match(line)
        if m:
            current = m.group(1)
            clauses.setdefault(current, [])
        if current is not None:
            clauses[current].append(line)

    result: dict[str, str] = {}
    for name, body_lines in clauses.items():
        body = "\n".join(body_lines)
        gaps = GAP_RE.findall(body)
        if not gaps:
            result[name] = "supported"
            continue
        if "pure (" in body and (".error" in body):
            result[name] = "partial"
            continue
        result[name] = "gap"
    return result


def _parse_gap_messages(lines: list[str]) -> dict[str, list[str]]:
    clauses: dict[str, list[str]] = {}
    current: str | None = None
    for line in lines:
        m = CASE_RE.match(line)
        if m:
            current = m.group(1)
            clauses.setdefault(current, [])
        if current is not None:
            clauses[current].append(line)

    messages: dict[str, list[str]] = {}
    for name, body_lines in clauses.items():
        body = "\n".join(body_lines)
        gaps = sorted(set(GAP_RE.findall(body)))
        if gaps:
            messages[name] = gaps
    return messages


def _parse_lookup_primop(text: str) -> list[str]:
    """Extract builtin names from lookupPrimOp match arms."""
    block = "\n".join(_extract_block(text, "def lookupPrimOp", "def evalPureBuiltinViaEvmYulLean"))
    return sorted(set(PRIMOP_RE.findall(_strip_lean_comments(block))))


def _parse_pure_bridge(text: str) -> list[str]:
    """Extract builtin names from evalPureBuiltinViaEvmYulLean match arms."""
    block = "\n".join(_extract_block(text, "def evalPureBuiltinViaEvmYulLean", "def evalBuiltinCallViaEvmYulLean"))
    return sorted(set(PURE_BRIDGE_RE.findall(_strip_lean_comments(block))))


def _parse_bridge_lemmas() -> tuple[list[str], list[str]]:
    """Extract builtins with universal bridge lemmas from BridgeLemmas file.

    Returns (all_lemmas, admitted_lemmas) where admitted_lemmas lists builtins
    whose bridge theorems transitively depend on ``sorry``'d helper lemmas.
    Detection: scan forward from each ``sorry`` occurrence (standalone or inline
    ``by sorry``) to the next ``evalBuiltinCall_NAME_bridge`` theorem and mark
    that builtin as admitted.  Comments and doc comments are ignored.
    """
    if not BRIDGE_LEMMAS_FILE.exists():
        raise FileNotFoundError(f"Bridge lemmas file not found: {BRIDGE_LEMMAS_FILE}")
    text = BRIDGE_LEMMAS_FILE.read_text(encoding="utf-8")
    code = _strip_lean_comments(text)
    all_lemmas = sorted(set(BRIDGE_LEMMA_RE.findall(code)))

    # Find sorry-dependent builtins by scanning line-by-line: after a sorry,
    # the next evalBuiltinCall_*_bridge theorem inherits the admission.
    # Detect both standalone `sorry` and inline `by sorry` / `:= sorry` forms.
    admitted: set[str] = set()
    sorry_pending = False
    sorry_re = re.compile(r'\bsorry\b')
    for line in code.splitlines():
        if sorry_re.search(line):
            sorry_pending = True
        if sorry_pending:
            m = BRIDGE_LEMMA_RE.search(line)
            if m:
                admitted.add(m.group(1))
                sorry_pending = False
    return all_lemmas, sorted(admitted)


def _parse_bridge_tests() -> tuple[list[str], int]:
    """Extract builtins with bridge equivalence tests and their count.

    Only counts examples where both verityEval* and bridgeEval appear in the
    same example block (actual bridge equivalence assertions), excluding
    context-only tests and bridge-returns-none boundary checks.
    """
    if not BRIDGE_TEST_FILE.exists():
        raise FileNotFoundError(f"Bridge test file not found: {BRIDGE_TEST_FILE}")
    text = BRIDGE_TEST_FILE.read_text(encoding="utf-8")
    code = _strip_lean_comments(text)
    # Split into individual example blocks
    blocks = EXAMPLE_SPLIT_RE.split(code)[1:]  # skip preamble before first example
    builtins: set[str] = set()
    bridge_test_count = 0
    for block in blocks:
        # Only count blocks that have both verityEval and bridgeEval (true equivalence)
        verity_matches = VERITY_EVAL_RE.findall(block)
        bridge_matches = BRIDGE_EVAL_RE.findall(block)
        if verity_matches and bridge_matches and NATIVE_DECIDE_RE.search(block):
            bridge_test_count += 1
            # Only count builtins that appear on both sides of the bridge
            common = set(verity_matches) & set(bridge_matches)
            builtins.update(common)
    return sorted(builtins), bridge_test_count


def _parse_correctness_proofs() -> dict[str, object]:
    """Parse adapter correctness proof theorems."""
    if not CORRECTNESS_FILE.exists():
        raise FileNotFoundError(f"Correctness proof file not found: {CORRECTNESS_FILE}")
    text = CORRECTNESS_FILE.read_text(encoding="utf-8")
    code = _strip_lean_comments(text)
    theorems = sorted(set(CORRECTNESS_THEOREM_RE.findall(code)))
    if not theorems:
        raise ValueError(
            f"No correctness theorems found in {CORRECTNESS_FILE.relative_to(ROOT)} "
            f"— expected assign_equiv_let or for_init theorems"
        )
    assign_thms = [t for t in theorems if "assign" in t]
    for_thms = [t for t in theorems if "for_" in t or "for_init" in t or "for_empty" in t]
    if not assign_thms:
        raise ValueError(
            f"Missing assign/let correctness theorem family in {CORRECTNESS_FILE.relative_to(ROOT)} "
            f"— expected theorem names containing 'assign'"
        )
    if not for_thms:
        raise ValueError(
            f"Missing for-init-hoisting correctness theorem family in {CORRECTNESS_FILE.relative_to(ROOT)} "
            f"— expected theorem names containing 'for_' or 'for_init'"
        )
    return {
        "file": str(CORRECTNESS_FILE.relative_to(ROOT)),
        "assign_to_let": f"proven ({', '.join(assign_thms)})",
        "for_init_hoisting": f"proven ({', '.join(for_thms)})",
    }


def build_report() -> dict[str, object]:
    if not ADAPTER_FILE.exists():
        raise FileNotFoundError(f"Missing adapter file: {ADAPTER_FILE.relative_to(ROOT)}")

    text = ADAPTER_FILE.read_text(encoding="utf-8")
    expr_lines = _extract_block(text, "def lowerExpr", "partial def lowerStmts")
    stmt_lines = _extract_block(text, "partial def lowerStmt", "def lowerProgram")

    expr_status = _parse_cases(expr_lines)
    stmt_status = _parse_cases(stmt_lines)
    stmt_gap_messages = _parse_gap_messages(stmt_lines)

    missing_expr = sorted(set(EXPECTED_EXPR_CASES) - set(expr_status))
    missing_stmt = sorted(set(EXPECTED_STMT_CASES) - set(stmt_status))

    expr_supported = sorted(k for k, v in expr_status.items() if v == "supported")
    stmt_supported = sorted(k for k, v in stmt_status.items() if v == "supported")
    stmt_partial = sorted(k for k, v in stmt_status.items() if v == "partial")
    stmt_gaps = sorted(k for k, v in stmt_status.items() if v == "gap")

    eval_stub = EVAL_STUB_RE.search(text) is not None

    status = "ok"
    if missing_expr or missing_stmt or stmt_partial or stmt_gaps or eval_stub:
        status = "partial"

    # Schema v4: extract builtin bridge inventories
    lookup_primop = _parse_lookup_primop(text)
    eval_pure = _parse_pure_bridge(text)
    universal_lemmas, admitted_lemmas = _parse_bridge_lemmas()
    tested_builtins, test_count = _parse_bridge_tests()
    if test_count > 0 and not tested_builtins:
        raise ValueError(
            "Bridge test parser found concrete bridge examples but credited no builtins; "
            "expected a non-empty concrete bridge inventory"
        )
    # Concrete-only = concretely tested builtins still lacking universal lemmas
    concrete_only = sorted(set(tested_builtins) - set(universal_lemmas))
    correctness = _parse_correctness_proofs()

    report: dict[str, object] = {
        "schema_version": 4,
        "adapter_file": str(ADAPTER_FILE.relative_to(ROOT)),
        "status": status,
        "expr_supported": expr_supported,
        "stmt_supported": stmt_supported,
        "stmt_partial": stmt_partial,
        "stmt_gaps": stmt_gaps,
        "stmt_gap_messages": stmt_gap_messages,
        "missing_expr_cases": missing_expr,
        "missing_stmt_cases": missing_stmt,
        "eval_builtin_via_evmyullean": "stub-none" if eval_stub else "implemented",
    }

    # Always emit schema inventory keys so that parser drift (yielding
    # empty lists) causes a visible diff in the artifact rather than silently
    # dropping coverage sections that --check would then accept.
    report["admitted_bridge_lemmas"] = admitted_lemmas
    report["fully_proven_bridge_lemmas"] = sorted(
        set(universal_lemmas) - set(admitted_lemmas)
    )
    report["lookup_primop_mapped"] = lookup_primop
    report["eval_pure_bridged"] = eval_pure
    report["universal_bridge_lemmas"] = universal_lemmas
    report["concrete_bridge_tests"] = tested_builtins
    report["concrete_only_bridge_tests"] = concrete_only
    report["concrete_test_count"] = test_count
    report["adapter_correctness_proofs"] = correctness

    return report


def write_report(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True, indent=2) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Output artifact path (default: artifacts/evmyullean_adapter_report.json)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Fail if output artifact is missing or stale",
    )
    args = parser.parse_args()

    payload = build_report()
    rendered = json.dumps(payload, sort_keys=True, indent=2) + "\n"

    if args.check:
        if not args.output.exists():
            print(f"Missing adapter artifact: {args.output}", file=sys.stderr)
            return 1
        existing = args.output.read_text(encoding="utf-8")
        if existing != rendered:
            print(
                "EVMYulLean adapter report is stale. Regenerate with:\n"
                "  python3 scripts/generate_evmyullean_adapter_report.py",
                file=sys.stderr,
            )
            return 1
        print(f"EVMYulLean adapter report is up to date: {args.output}")
        return 0

    write_report(args.output, payload)
    print(f"Wrote EVMYulLean adapter report: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
