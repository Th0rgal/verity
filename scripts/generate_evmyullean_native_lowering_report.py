#!/usr/bin/env python3
"""Generate/check deterministic EVMYulLean native lowering coverage artifact.

Usage:
    python3 scripts/generate_evmyullean_native_lowering_report.py
    python3 scripts/generate_evmyullean_native_lowering_report.py --check
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
NATIVE_LOWERING_FILE = BACKENDS_DIR / "EvmYulLeanNativeLowering.lean"
BRIDGE_PREDICATES_FILE = BACKENDS_DIR / "EvmYulLeanBridgePredicates.lean"
BRIDGE_LEMMAS_FILE = BACKENDS_DIR / "EvmYulLeanBridgeLemmas.lean"
BRIDGE_TEST_FILE = BACKENDS_DIR / "EvmYulLeanBridgeTest.lean"
CORRECTNESS_FILE = BACKENDS_DIR / "EvmYulLeanNativeHarness.lean"
DEFAULT_OUTPUT = ROOT / "artifacts" / "evmyullean_native_lowering_report.json"

EXPECTED_EXPR_CASES = ["lit", "hex", "str", "ident", "call"]
EXPECTED_STMT_CASES = ["comment", "let_", "letMany", "assign", "expr", "leave", "if_", "for_", "switch", "block", "funcDef"]

CASE_RE = re.compile(r"^\s*\|\s*\.([A-Za-z0-9_']+)")
GAP_RE = re.compile(r'(?:\.error|throw)\s+(?:s!)?"([^"]+)"')
EVAL_STUB_RE = re.compile(r"def\s+evalBuiltinCallViaEvmYulLean[\s\S]*?:\s*Option\s+Nat\s*:=\s*none")

# Regex for lookupPrimOp string-keyed match arms: | "name" => some .OP
PRIMOP_RE = re.compile(r'^\s*\|\s*"([a-z0-9_]+)"\s+=>\s*some\s+\.', re.MULTILINE)

# Regex for evalPureBuiltinViaEvmYulLean match arms: | "name", [args] => some (...)
PURE_BRIDGE_RE = re.compile(r'^\s*\|\s*"([a-z0-9_]+)",\s*\[', re.MULTILINE)

# Regex for universal bridge lemmas: theorem evalBuiltinCall_NAME_bridge.
# Anchored to the start of a line and only allows declaration modifiers before
# ``theorem`` so that nested/indented ``have`` / ``theorem`` occurrences inside
# another proof body are not treated as top-level universal bridge lemmas.
BRIDGE_LEMMA_RE = re.compile(
    r'(?m)^(?:(?:private|protected|noncomputable|unsafe|partial|local|@\[[^\]]*\])\s+)*'
    r'theorem\s+evalBuiltinCall_(\w+)_bridge\b'
)

# Regex for direct native context bridge theorems:
# evalBuiltinCall_NAME_bridge
CONTEXT_BRIDGE_RE = re.compile(
    r'evalBuiltinCall_(\w+)_bridge\b'
)

# Regex for fallthrough (none) theorems. Kept for schema stability; native-only
# bridge lemmas do not currently expose fallthrough theorem families.
FALLTHROUGH_RE = re.compile(
    r'evalBuiltinCall_(\w+)_none\b'
)

# Regex for bridgedBuiltins/unbridgedBuiltins definitions
BRIDGED_BUILTINS_RE = re.compile(
    r'def\s+bridgedBuiltins\s*:\s*List\s+String\s*:=\s*\[(.*?)\]',
    re.DOTALL,
)
UNBRIDGED_BUILTINS_RE = re.compile(
    r'def\s+unbridgedBuiltins\s*:\s*List\s+String\s*:=\s*\[(.*?)\]',
    re.DOTALL,
)

# Regex to extract individual examples (multi-line, split on `example`)
EXAMPLE_SPLIT_RE = re.compile(r'\bexample\b')

# Regex for builtins in bridge equivalence tests (both verityEval and bridgeEval present)
VERITY_EVAL_RE = re.compile(r'verityEval\w*\s+"([a-z0-9_]+)"')
BRIDGE_EVAL_RE = re.compile(r'bridgeEval\s+"([a-z0-9_]+)"')
BRIDGE_EQUALITY_RE = re.compile(
    r'(?:'
    r'verityEval\w*\s+"(?P<left>[a-z0-9_]+)"\s+\[[^\]]*\]\s*'
    r'=\s*bridgeEval\s+"(?P=left)"\s+\[[^\]]*\]\s*:=\s*by\s+native_decide'
    r'|'
    r'bridgeEval\s+"(?P<right>[a-z0-9_]+)"\s+\[[^\]]*\]\s*'
    r'=\s*verityEval\w*\s+"(?P=right)"\s+\[[^\]]*\]\s*:=\s*by\s+native_decide'
    r')'
)

# Count native_decide occurrences
NATIVE_DECIDE_RE = re.compile(r'by\s+native_decide')

# Regex for correctness theorems: theorem NAME (including names with apostrophes)
# Handles optional attributes (@[simp], @[ext], etc.) and modifiers before theorem.
CORRECTNESS_THEOREM_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected)\s+)*theorem\s+([\w']+)",
    re.MULTILINE,
)
DECLARATION_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected|unsafe|partial|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|example|opaque|axiom|constant|structure|class|inductive)\b"
    r"|^(?:section|namespace|end)\b",
    re.MULTILINE,
)

DECL_KEYWORDS = (
    r"theorem|lemma|def|abbrev|instance|example|opaque|axiom|constant|"
    r"inductive|structure|class"
)
MODIFIERS = r"(?:(?:private|protected|noncomputable|unsafe|partial|local|@\[[^\]]*\])\s+)*"
TOP_LEVEL_DECL_RE = re.compile(
    rf"(?m)^(?:{MODIFIERS}(?:{DECL_KEYWORDS})(?:\s+([A-Za-z_][A-Za-z0-9_']*))?\b|"
    r"(section|namespace|end)\b)"
)


def _strip_lean_comments(text: str) -> str:
    """Remove Lean line/block comments while preserving line structure."""
    result: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False
    string_escape = False
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

        ch = text[i]
        if in_string:
            result.append(ch)
            if string_escape:
                string_escape = False
            elif ch == "\\":
                string_escape = True
            elif ch == '"':
                in_string = False
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

        if ch == '"':
            in_string = True
        result.append(ch)
        i += 1
    return "".join(result)


def _strip_lean_strings(text: str) -> str:
    """Blank Lean string literal contents while preserving line structure."""
    result: list[str] = []
    i = 0
    n = len(text)
    in_string = False
    string_escape = False
    while i < n:
        ch = text[i]
        if in_string:
            if ch == "\n":
                result.append("\n")
                string_escape = False
            else:
                result.append(" ")
            if string_escape:
                string_escape = False
            elif ch == "\\":
                string_escape = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if ch == '"':
            in_string = True
            result.append(" ")
            i += 1
            continue
        result.append(ch)
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
        if "pure (" in body and gaps:
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
    code = _strip_lean_strings(_strip_lean_comments(text))
    all_lemmas = sorted({
        m.group(1)
        for m in BRIDGE_LEMMA_RE.finditer(code)
    })

    # Attribute each ``sorry`` correctly:
    # * If a ``sorry`` appears inside a bridge theorem's own body
    #   (``evalBuiltinCall_X_bridge``), that bridge theorem is admitted.
    # * If a ``sorry`` appears in a helper declaration (``private theorem``,
    #   ``def``, ...) between two bridge theorems, it is admitted against the
    #   *next* bridge theorem, because helpers are used by the bridge that
    #   follows them.
    # The prior scan was purely forward and, when a bridge's own body
    # contained ``sorry``, misattributed the admission to the *next* bridge.
    sorry_re = re.compile(r'\bsorry\b')
    bridge_name_re = re.compile(
        rf'{MODIFIERS}'
        r'theorem\s+evalBuiltinCall_(\w+)_bridge\b'
    )
    admitted: set[str] = set()
    admitted_helpers: set[str] = set()
    anonymous_helper_sorry = False
    for start, end, name, is_scope in _top_level_blocks(code):
        body = code[start:end]
        body_has_sorry = sorry_re.search(body) is not None
        referenced_admitted_helper = any(
            re.search(rf'\b{re.escape(helper)}\b', body)
            for helper in admitted_helpers
        )
        bridge_match = bridge_name_re.match(body)
        if is_scope:
            admitted_helpers.clear()
            anonymous_helper_sorry = False
        elif bridge_match:
            bridge = bridge_match.group(1)
            if body_has_sorry or referenced_admitted_helper or anonymous_helper_sorry:
                admitted.add(bridge)
            anonymous_helper_sorry = False
        elif body_has_sorry or referenced_admitted_helper or anonymous_helper_sorry:
            if name:
                admitted_helpers.add(name)
                anonymous_helper_sorry = False
            else:
                anonymous_helper_sorry = True
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
    # Compute the positions that are *inside* a Lean string literal so that a
    # plain string containing text like ``example ... verityEval ... =
    # bridgeEval ... := by native_decide`` cannot inflate ``concrete_test_count``
    # or the concrete builtin inventory. The example-splitter also runs on the
    # stripped code, but split points that fall inside a string must not begin
    # a new block: treat the stripped code as a single block if the ``example``
    # keyword itself is inside a string.
    in_string_mask = _compute_in_string_mask(code)
    # Split into individual example blocks, but only at example keywords that
    # are not themselves inside a string literal.
    example_positions = [
        m.start() for m in EXAMPLE_SPLIT_RE.finditer(code)
        if not in_string_mask[m.start()]
    ]
    block_spans: list[tuple[int, int]] = []
    for idx, start in enumerate(example_positions):
        end = example_positions[idx + 1] if idx + 1 < len(example_positions) else len(code)
        block_spans.append((start, end))
    builtins: set[str] = set()
    bridge_test_count = 0
    for start, end in block_spans:
        block = code[start:end]
        if not NATIVE_DECIDE_RE.search(block):
            continue
        matches = [
            m for m in BRIDGE_EQUALITY_RE.finditer(block)
            # Skip matches whose start position in the full file lies inside a
            # string literal — those are quotations of test-like text, not real
            # bridge equivalences.
            if not in_string_mask[start + m.start()]
        ]
        if matches:
            bridge_test_count += 1
            for match in matches:
                builtin = match.group("left") or match.group("right")
                builtins.add(builtin)
    return sorted(builtins), bridge_test_count


def _compute_in_string_mask(code: str) -> list[bool]:
    """Return a list the same length as ``code`` where ``mask[i]`` is True iff
    the character at position ``i`` lies inside a Lean string literal (between
    its opening and closing ``"`` characters). The opening and closing quotes
    themselves are marked False so that regexes anchored on the quote character
    keep matching legitimate short builtin-name strings like ``"add"``.
    """
    mask = [False] * len(code)
    in_string = False
    string_escape = False
    for i, ch in enumerate(code):
        if in_string:
            mask[i] = True
            if string_escape:
                string_escape = False
            elif ch == "\\":
                string_escape = True
            elif ch == '"':
                mask[i] = False  # closing quote itself is not "inside"
                in_string = False
        elif ch == '"':
            in_string = True
    return mask


def _top_level_blocks(code: str) -> list[tuple[int, int, str | None, bool]]:
    """Return top-level declaration/scope blocks.

    The declaration matcher is anchored at column 0 so local declarations in
    theorem bodies are kept inside the enclosing theorem slice.
    """
    matches = list(TOP_LEVEL_DECL_RE.finditer(code))
    blocks: list[tuple[int, int, str | None, bool]] = []
    for idx, match in enumerate(matches):
        start = match.start()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(code)
        blocks.append((start, end, match.group(1), match.group(2) is not None))
    return blocks


def _parse_context_bridge_lemmas() -> tuple[list[str], list[str]]:
    """Extract builtins with direct native bridge and fallthrough theorems.

    Returns (context_bridged, fallthrough) where context_bridged lists builtins
    with evalBuiltinCall_*_bridge theorems, and fallthrough lists builtins with
    *_none theorems.
    """
    if not BRIDGE_LEMMAS_FILE.exists():
        raise FileNotFoundError(f"Bridge lemmas file not found: {BRIDGE_LEMMAS_FILE}")
    text = BRIDGE_LEMMAS_FILE.read_text(encoding="utf-8")
    code = _strip_lean_strings(_strip_lean_comments(text))
    context_bridged: set[str] = set()
    fallthrough: set[str] = set()
    theorem_re = re.compile(rf"{MODIFIERS}theorem\s+([A-Za-z_][A-Za-z0-9_']*)\b", re.DOTALL)
    for start, end, _name, is_scope in _top_level_blocks(code):
        if is_scope:
            continue
        block = code[start:end]
        theorem_match = theorem_re.match(block)
        if not theorem_match:
            continue
        theorem_name = theorem_match.group(1)
        context_match = CONTEXT_BRIDGE_RE.fullmatch(theorem_name)
        if context_match and context_match.group(1) != "pure":
            context_bridged.add(context_match.group(1))
            continue
        fallthrough_match = FALLTHROUGH_RE.fullmatch(theorem_name)
        if fallthrough_match:
            fallthrough.add(fallthrough_match.group(1))
    context_bridged = sorted(context_bridged)
    fallthrough = sorted(fallthrough)
    return context_bridged, fallthrough


def _parse_bridged_builtins_defs() -> tuple[list[str], list[str]]:
    """Extract bridgedBuiltins and unbridgedBuiltins from the predicate module.

    Returns (bridged, unbridged) or empty lists if definitions not found.
    """
    if not BRIDGE_PREDICATES_FILE.exists():
        return [], []
    text = BRIDGE_PREDICATES_FILE.read_text(encoding="utf-8")
    code = _strip_lean_comments(text)

    def _extract_string_list(pattern: re.Pattern[str]) -> list[str]:
        m = pattern.search(code)
        if not m:
            return []
        raw = m.group(1)
        return sorted(re.findall(r'"([a-zA-Z0-9_]+)"', raw))

    bridged = _extract_string_list(BRIDGED_BUILTINS_RE)
    unbridged = _extract_string_list(UNBRIDGED_BUILTINS_RE)
    return bridged, unbridged


def _parse_correctness_proofs() -> dict[str, object]:
    """Report native harness status for the historical correctness slot."""
    if not CORRECTNESS_FILE.exists():
        try:
            file_label = str(CORRECTNESS_FILE.relative_to(ROOT))
        except ValueError:
            file_label = str(CORRECTNESS_FILE)
        return {
            "file": file_label,
            "runtime_lowering": "missing",
            "dispatcher_tail": "missing",
        }
    text = CORRECTNESS_FILE.read_text(encoding="utf-8")
    code = _strip_lean_strings(_strip_lean_comments(text))
    return {
        "file": str(CORRECTNESS_FILE.relative_to(ROOT)),
        "runtime_lowering": "present" if "lowerRuntimeContractNative" in code else "missing",
        "dispatcher_tail": (
            "present" if "NativeGeneratedSelectorHitSuccessBridge" in code else "missing"
        ),
    }


def build_report() -> dict[str, object]:
    if not NATIVE_LOWERING_FILE.exists():
        raise FileNotFoundError(f"Missing native lowering file: {NATIVE_LOWERING_FILE.relative_to(ROOT)}")
    native_text = NATIVE_LOWERING_FILE.read_text(encoding="utf-8")
    expr_lines = _extract_block(native_text, "def lowerExprNative", "theorem lowerExprNative_call_runtimePrimOp")
    stmt_lines = _extract_block(native_text, "def lowerStmtGroupNativeWithSwitchIds", "def lowerStmtsNative")

    expr_status = _parse_cases(expr_lines)
    stmt_status = _parse_cases(stmt_lines)
    stmt_gap_messages = _parse_gap_messages(stmt_lines)

    missing_expr = sorted(set(EXPECTED_EXPR_CASES) - set(expr_status))
    missing_stmt = sorted(set(EXPECTED_STMT_CASES) - set(stmt_status))

    expr_supported = sorted(k for k, v in expr_status.items() if v == "supported")
    stmt_supported = sorted(k for k, v in stmt_status.items() if v == "supported")
    stmt_partial = sorted(k for k, v in stmt_status.items() if v == "partial")
    stmt_gaps = sorted(k for k, v in stmt_status.items() if v == "gap")

    eval_stub = EVAL_STUB_RE.search(native_text) is not None

    status = "ok"
    if missing_expr or missing_stmt or stmt_partial or stmt_gaps or eval_stub:
        status = "partial"

    # Schema v4: extract builtin bridge inventories
    lookup_primop = _parse_lookup_primop(native_text)
    eval_pure = _parse_pure_bridge(native_text)
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

    # Schema v6: Phase 4 complete — direct native bridges + bridged/unbridged defs.
    context_bridged, fallthrough = _parse_context_bridge_lemmas()
    bridged_defs, unbridged_defs = _parse_bridged_builtins_defs()

    report: dict[str, object] = {
        "schema_version": 8,
        "native_lowering_file": str(NATIVE_LOWERING_FILE.relative_to(ROOT)),
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
    report["native_harness_status"] = correctness

    # Phase 4 readiness fields (schema v5)
    report["native_context_bridge_lemmas"] = context_bridged
    report["fallthrough_lemmas"] = fallthrough
    if bridged_defs:
        report["bridged_builtins"] = bridged_defs
    if unbridged_defs:
        report["unbridged_builtins"] = unbridged_defs

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
        help="Output artifact path (default: artifacts/evmyullean_native_lowering_report.json)",
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
            print(f"Missing native lowering artifact: {args.output}", file=sys.stderr)
            return 1
        existing = args.output.read_text(encoding="utf-8")
        if existing != rendered:
            print(
                "EVMYulLean native lowering report is stale. Regenerate with:\n"
                "  python3 scripts/generate_evmyullean_native_lowering_report.py",
                file=sys.stderr,
            )
            return 1
        print(f"EVMYulLean native lowering report is up to date: {args.output}")
        return 0

    write_report(args.output, payload)
    print(f"Wrote EVMYulLean native lowering report: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
