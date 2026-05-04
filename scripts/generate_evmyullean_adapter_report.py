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
RETARGET_FILE = BACKENDS_DIR / "EvmYulLeanRetarget.lean"
BODY_CLOSURE_FILE = BACKENDS_DIR / "EvmYulLeanBodyClosure.lean"
SOURCE_EXPR_CLOSURE_FILE = BACKENDS_DIR / "EvmYulLeanSourceExprClosure.lean"
END_TO_END_FILE = ROOT / "Compiler" / "Proofs" / "EndToEnd.lean"
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

# Regex for universal bridge lemmas: theorem evalBuiltinCall_NAME_bridge.
# Anchored to the start of a line and only allows declaration modifiers before
# ``theorem`` so that nested/indented ``have`` / ``theorem`` occurrences inside
# another proof body are not treated as top-level universal bridge lemmas.
BRIDGE_LEMMA_RE = re.compile(
    r'(?m)^(?:(?:private|protected|noncomputable|unsafe|partial|local|@\[[^\]]*\])\s+)*'
    r'theorem\s+evalBuiltinCall_(\w+)_bridge\b'
)

# Regex for context-lifted bridge theorems:
# evalBuiltinCallWithBackendContext_evmYulLean_NAME_bridge
CONTEXT_BRIDGE_RE = re.compile(
    r'evalBuiltinCallWithBackendContext_evmYulLean_(\w+)_bridge\b'
)

# Regex for fallthrough (none) theorems:
# evalBuiltinCallWithBackendContext_evmYulLean_NAME_none
FALLTHROUGH_RE = re.compile(
    r'evalBuiltinCallWithBackendContext_evmYulLean_(\w+)_none\b'
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
    """Extract builtins with context-lifted bridge and fallthrough theorems.

    Returns (context_bridged, fallthrough) where context_bridged lists builtins
    with evalBuiltinCallWithBackendContext_evmYulLean_*_bridge theorems, and
    fallthrough lists builtins with *_none theorems.
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
    """Extract bridgedBuiltins and unbridgedBuiltins from BridgeLemmas file.

    Returns (bridged, unbridged) or empty lists if definitions not found.
    """
    if not BRIDGE_LEMMAS_FILE.exists():
        return [], []
    text = BRIDGE_LEMMAS_FILE.read_text(encoding="utf-8")
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
    """Parse adapter correctness proof theorems."""
    if not CORRECTNESS_FILE.exists():
        raise FileNotFoundError(f"Correctness proof file not found: {CORRECTNESS_FILE}")
    text = CORRECTNESS_FILE.read_text(encoding="utf-8")
    code = _strip_lean_strings(_strip_lean_comments(text))
    theorem_matches = list(CORRECTNESS_THEOREM_RE.finditer(code))
    theorem_status: dict[str, str] = {}
    for idx, match in enumerate(theorem_matches):
        name = match.group(1)
        next_decl = DECLARATION_RE.search(code, match.end())
        next_theorem = theorem_matches[idx + 1].start() if idx + 1 < len(theorem_matches) else None
        candidates = [pos for pos in [next_decl.start() if next_decl else None, next_theorem] if pos is not None]
        end = min(candidates) if candidates else len(code)
        body = code[match.end():end]
        theorem_status[name] = "sorry" if re.search(r"\bsorry\b", body) else "proven"
    theorems = sorted(theorem_status)
    if not theorems:
        raise ValueError(
            f"No correctness theorems found in {CORRECTNESS_FILE.relative_to(ROOT)} "
            f"— expected assign_equiv_let or for_init theorems"
        )
    required_assign = ["assign_equiv_let"]
    required_for = ["for_init_hoist"]
    missing_assign = [name for name in required_assign if name not in theorem_status]
    missing_for = [name for name in required_for if name not in theorem_status]
    if missing_assign:
        raise ValueError(
            f"Missing assign/let correctness theorem family in {CORRECTNESS_FILE.relative_to(ROOT)} "
            f"— expected exact theorem name(s): {', '.join(required_assign)}"
        )
    if missing_for:
        raise ValueError(
            f"Missing for-init-hoisting correctness theorem family in {CORRECTNESS_FILE.relative_to(ROOT)} "
            f"— expected exact theorem name(s): {', '.join(required_for)}"
        )
    assign_thms = sorted(t for t in theorems if t.startswith("assign_equiv_let"))
    for_thms = sorted(t for t in theorems if t.startswith("for_init_hoist"))

    def family_status(names: list[str]) -> str:
        if any(theorem_status[name] == "sorry" for name in names):
            return f"sorry ({', '.join(names)})"
        return f"proven ({', '.join(names)})"

    return {
        "file": str(CORRECTNESS_FILE.relative_to(ROOT)),
        "assign_to_let": family_status(assign_thms),
        "for_init_hoisting": family_status(for_thms),
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

    # Schema v6: Phase 4 complete — context-lifted bridges + bridged/unbridged defs + retarget
    context_bridged, fallthrough = _parse_context_bridge_lemmas()
    bridged_defs, unbridged_defs = _parse_bridged_builtins_defs()

    # Phase 4 retarget detection
    retarget_file = RETARGET_FILE
    phase4_retarget: dict[str, str] | None = None
    if retarget_file.exists():
        retarget_text = retarget_file.read_text(encoding="utf-8")
        retarget_code = _strip_lean_strings(_strip_lean_comments(retarget_text))

        # Match genuine ``theorem <name>`` declarations (not comments/prose),
        # optionally preceded by modifiers like ``private`` / ``protected`` /
        # ``noncomputable``.  This avoids false positives where a theorem
        # name appears only in a doc comment or summary.
        def _has_theorem_in(code: str, name: str) -> bool:
            pattern = (
                r'^[ \t]{0,2}(?:@\[[^\]]*\]\s*)*'
                r'(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*'
                r'theorem\s+' + re.escape(name) + r'\b'
            )
            return re.search(pattern, code, re.MULTILINE) is not None

        def _has_theorem(name: str) -> bool:
            return _has_theorem_in(retarget_code, name)

        def _theorem_block_in(code: str, name: str) -> str:
            """Return the declaration block for ``theorem name`` if present."""
            header_re = re.compile(
                r'^[ \t]{0,2}(?:@\[[^\]]*\]\s*)*'
                r'(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*'
                r'theorem\s+' + re.escape(name) + r'\b',
                re.MULTILINE,
            )
            m = header_re.search(code)
            if not m:
                return ""
            start = m.start()
            # Slice to the next top-level ``theorem``/``lemma``/``def``/``end``
            # declaration to isolate this theorem's body.
            next_decl = re.compile(
                r'\n[ \t]{0,2}(?:(?:private|protected|noncomputable|unsafe|partial|local|@\[[^\]]*\])\s+)*'
                r'(?:theorem|lemma|def|abbrev|instance|example|opaque|axiom|constant|structure|class|inductive)\b'
                r'|\n[ \t]{0,2}(?:section|namespace|end)\b'
            )
            nxt = None
            for candidate in next_decl.finditer(code, pos=m.end()):
                prefix = code[:candidate.start()]
                prev_lines = [line.strip() for line in prefix.splitlines() if line.strip()]
                if prev_lines and prev_lines[-1] == "where":
                    continue
                nxt = candidate
                break
            end = nxt.start() if nxt else len(code)
            return code[start:end]

        def _theorem_body_has_sorry_in(code: str, name: str) -> bool:
            """Return True iff the body of ``theorem name`` contains ``sorry``."""
            block = _theorem_block_in(code, name)
            return bool(block and re.search(r'\bsorry\b', block))

        def _theorem_body_has_sorry(name: str) -> bool:
            return _theorem_body_has_sorry_in(retarget_code, name)

        has_backends_agree = _has_theorem("backends_agree_on_bridged_builtins")
        has_expr_retarget = _has_theorem("evalYulExpr_evmYulLean_eq_on_bridged")
        has_straight_stmt_retarget = _has_theorem(
            "execYulFuelWithBackend_eq_on_bridged_straight_stmts"
        )
        has_block_stmt_retarget = _has_theorem(
            "execYulFuelWithBackend_block_eq_on_bridged_straight_stmts"
        )
        has_if_stmt_retarget = _has_theorem(
            "execYulFuelWithBackend_if_eq_on_bridged_body"
        )
        has_switch_stmt_retarget = _has_theorem(
            "execYulFuelWithBackend_switch_eq_on_bridged_cases"
        )
        has_for_stmt_retarget = _has_theorem(
            "execYulFuelWithBackend_for_eq_on_bridged_parts"
        )
        has_recursive_target_retarget = _has_theorem(
            "execYulFuelWithBackend_eq_on_bridged_target"
        )
        has_runtime_closure = _has_theorem("emitYul_runtimeCode_bridged")
        has_runtime_backend_eq = _has_theorem(
            "emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies"
        )
        has_layer3_evm_retarget = _has_theorem(
            "yulCodegen_preserves_semantics_evmYulLeanFuelWrapperDefaultFuel_via_reference_oracle"
        )
        if END_TO_END_FILE.exists():
            end_to_end_code = _strip_lean_strings(
                _strip_lean_comments(END_TO_END_FILE.read_text(encoding="utf-8"))
            )
            has_end_to_end_evm_retarget = _has_theorem_in(
                end_to_end_code, "layers2_3_ir_matches_yul_evmYulLeanFuelWrapperDefaultFuel"
            )
            end_to_end_evm_retarget_has_sorry = _theorem_body_has_sorry_in(
                end_to_end_code, "layers2_3_ir_matches_yul_evmYulLeanFuelWrapperDefaultFuel"
            )
            end_to_end_evm_retarget_block = _theorem_block_in(
                end_to_end_code, "layers2_3_ir_matches_yul_evmYulLeanFuelWrapperDefaultFuel"
            )
            end_to_end_evm_retarget_has_body_hypotheses = bool(
                re.search(
                    r'\b(?:hFunctions|hFallback|hReceive|hBodyBridged|hInternals)\b'
                    r'|BridgedStmts',
                    end_to_end_evm_retarget_block,
                )
            )
        else:
            has_end_to_end_evm_retarget = False
            end_to_end_evm_retarget_has_sorry = False
            end_to_end_evm_retarget_has_body_hypotheses = False
        backends_agree_has_sorry = _theorem_body_has_sorry("backends_agree_on_bridged_builtins")
        expr_retarget_has_sorry = _theorem_body_has_sorry("evalYulExpr_evmYulLean_eq_on_bridged")
        straight_stmt_retarget_has_sorry = _theorem_body_has_sorry(
            "execYulFuelWithBackend_eq_on_bridged_straight_stmts"
        )
        block_stmt_retarget_has_sorry = _theorem_body_has_sorry(
            "execYulFuelWithBackend_block_eq_on_bridged_straight_stmts"
        )
        if_stmt_retarget_has_sorry = _theorem_body_has_sorry(
            "execYulFuelWithBackend_if_eq_on_bridged_body"
        )
        switch_stmt_retarget_has_sorry = _theorem_body_has_sorry(
            "execYulFuelWithBackend_switch_eq_on_bridged_cases"
        )
        for_stmt_retarget_has_sorry = _theorem_body_has_sorry(
            "execYulFuelWithBackend_for_eq_on_bridged_parts"
        )
        recursive_target_retarget_has_sorry = _theorem_body_has_sorry(
            "execYulFuelWithBackend_eq_on_bridged_target"
        )
        runtime_closure_has_sorry = _theorem_body_has_sorry("emitYul_runtimeCode_bridged")
        runtime_backend_eq_has_sorry = _theorem_body_has_sorry(
            "emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies"
        )
        layer3_evm_retarget_has_sorry = _theorem_body_has_sorry(
            "yulCodegen_preserves_semantics_evmYulLeanFuelWrapperDefaultFuel_via_reference_oracle"
        )
        admitted_deps = sorted(admitted_lemmas)
        admitted_dep_status = (
            "sorry-dependent (depends on admitted bridge lemmas: "
            + ", ".join(admitted_deps)
            + ")"
        )
        if not has_backends_agree:
            backends_agree_status = "missing"
        elif backends_agree_has_sorry:
            backends_agree_status = "sorry (dispatch; relies on 34 per-builtin bridge theorems)"
        elif admitted_deps:
            backends_agree_status = admitted_dep_status
        else:
            backends_agree_status = "proven"
        if not has_expr_retarget:
            expr_retarget_status = "missing"
        elif expr_retarget_has_sorry:
            expr_retarget_status = "sorry"
        elif admitted_deps:
            expr_retarget_status = admitted_dep_status
        else:
            expr_retarget_status = "proven"
        if not has_straight_stmt_retarget:
            straight_stmt_retarget_status = "missing"
        elif straight_stmt_retarget_has_sorry:
            straight_stmt_retarget_status = "sorry"
        elif admitted_deps:
            straight_stmt_retarget_status = admitted_dep_status
        else:
            straight_stmt_retarget_status = "proven"
        if not has_block_stmt_retarget:
            block_stmt_retarget_status = "missing"
        elif block_stmt_retarget_has_sorry:
            block_stmt_retarget_status = "sorry"
        elif admitted_deps:
            block_stmt_retarget_status = admitted_dep_status
        else:
            block_stmt_retarget_status = "proven"
        if not has_if_stmt_retarget:
            if_stmt_retarget_status = "missing"
        elif if_stmt_retarget_has_sorry:
            if_stmt_retarget_status = "sorry"
        elif admitted_deps:
            if_stmt_retarget_status = admitted_dep_status
        else:
            if_stmt_retarget_status = "proven"
        if not has_switch_stmt_retarget:
            switch_stmt_retarget_status = "missing"
        elif switch_stmt_retarget_has_sorry:
            switch_stmt_retarget_status = "sorry"
        elif admitted_deps:
            switch_stmt_retarget_status = admitted_dep_status
        else:
            switch_stmt_retarget_status = "proven"
        if not has_for_stmt_retarget:
            for_stmt_retarget_status = "missing"
        elif for_stmt_retarget_has_sorry:
            for_stmt_retarget_status = "sorry"
        elif admitted_deps:
            for_stmt_retarget_status = admitted_dep_status
        else:
            for_stmt_retarget_status = "proven"
        if not has_recursive_target_retarget:
            recursive_target_retarget_status = "missing"
        elif recursive_target_retarget_has_sorry:
            recursive_target_retarget_status = "sorry"
        elif admitted_deps:
            recursive_target_retarget_status = admitted_dep_status
        else:
            recursive_target_retarget_status = "proven"
        if not has_runtime_closure:
            runtime_closure_status = "missing"
        elif runtime_closure_has_sorry:
            runtime_closure_status = "sorry"
        else:
            runtime_closure_status = "proven (conditional on bridged IR bodies)"
        if not has_runtime_backend_eq:
            runtime_backend_eq_status = "missing"
        elif runtime_backend_eq_has_sorry:
            runtime_backend_eq_status = "sorry"
        elif admitted_deps:
            runtime_backend_eq_status = admitted_dep_status
        else:
            runtime_backend_eq_status = "proven (conditional on bridged IR bodies)"
        if not has_layer3_evm_retarget:
            layer3_evm_retarget_status = "missing"
        elif layer3_evm_retarget_has_sorry:
            layer3_evm_retarget_status = "sorry"
        elif admitted_deps:
            layer3_evm_retarget_status = admitted_dep_status
        else:
            layer3_evm_retarget_status = "proven (conditional on bridged IR bodies)"
        if not has_end_to_end_evm_retarget:
            end_to_end_evm_retarget_status = "missing"
        elif end_to_end_evm_retarget_has_sorry:
            end_to_end_evm_retarget_status = "sorry"
        elif admitted_deps:
            end_to_end_evm_retarget_status = admitted_dep_status
        elif end_to_end_evm_retarget_has_body_hypotheses:
            end_to_end_evm_retarget_status = (
                "proven (conditional on bridged IR bodies)"
            )
        else:
            end_to_end_evm_retarget_status = "proven (body hypotheses discharged)"
        if BODY_CLOSURE_FILE.exists():
            body_closure_code = _strip_lean_strings(
                _strip_lean_comments(BODY_CLOSURE_FILE.read_text(encoding="utf-8"))
            )
            has_scalar_param_body_closure = _has_theorem_in(
                body_closure_code, "genParamLoads_scalar_bridged"
            )
            scalar_param_body_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "genParamLoads_scalar_bridged"
            )
            has_static_type_body_closure = _has_theorem_in(
                body_closure_code, "genStaticTypeLoads_calldataload_bridged"
            )
            static_type_body_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "genStaticTypeLoads_calldataload_bridged"
            )
            has_static_param_body_closure = _has_theorem_in(
                body_closure_code, "genParamLoads_static_scalar_bridged"
            )
            static_param_body_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "genParamLoads_static_scalar_bridged"
            )
            has_binding_stmt_body_closure = _has_theorem_in(
                body_closure_code, "compileStmtList_binding_leaf_bridged"
            )
            binding_stmt_body_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "compileStmtList_binding_leaf_bridged"
            )
            has_pure_binding_stmt_body_closure = _has_theorem_in(
                body_closure_code, "compileStmtList_pure_binding_bridged"
            )
            pure_binding_stmt_body_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "compileStmtList_pure_binding_bridged"
            )
            has_storage_fragment_body_closure = _has_theorem_in(
                body_closure_code, "compileStmtList_storage_fragment_bridged"
            )
            storage_fragment_body_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "compileStmtList_storage_fragment_bridged"
            )
            has_terminator_body_closure = _has_theorem_in(
                body_closure_code, "compileStmtList_terminator_external_bridged"
            )
            terminator_body_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "compileStmtList_terminator_external_bridged"
            )
            has_internal_return_body_closure = _has_theorem_in(
                body_closure_code, "compileStmtList_internal_return_bridged"
            )
            internal_return_body_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "compileStmtList_internal_return_bridged"
            )
            has_require_body_closure = _has_theorem_in(
                body_closure_code, "compileStmtList_require_bridged"
            )
            require_body_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "compileStmtList_require_bridged"
            )
            has_external_body_fragment_closure = _has_theorem_in(
                body_closure_code, "compileStmtList_external_body_fragment_bridged"
            )
            external_body_fragment_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "compileStmtList_external_body_fragment_bridged"
            )
            has_internal_body_fragment_closure = _has_theorem_in(
                body_closure_code, "compileStmtList_internal_body_fragment_bridged"
            )
            internal_body_fragment_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "compileStmtList_internal_body_fragment_bridged"
            )
            has_external_structured_body_fragment_closure = _has_theorem_in(
                body_closure_code, "compileStmtList_external_structured_body_fragment_bridged"
            )
            external_structured_body_fragment_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "compileStmtList_external_structured_body_fragment_bridged"
            )
            has_internal_structured_body_fragment_closure = _has_theorem_in(
                body_closure_code, "compileStmtList_internal_structured_body_fragment_bridged"
            )
            internal_structured_body_fragment_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "compileStmtList_internal_structured_body_fragment_bridged"
            )
            has_external_nested_body_fragment_closure = _has_theorem_in(
                body_closure_code, "compileStmtList_external_nested_body_fragment_bridged"
            )
            external_nested_body_fragment_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "compileStmtList_external_nested_body_fragment_bridged"
            )
            has_internal_nested_body_fragment_closure = _has_theorem_in(
                body_closure_code, "compileStmtList_internal_nested_body_fragment_bridged"
            )
            internal_nested_body_fragment_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "compileStmtList_internal_nested_body_fragment_bridged"
            )
            has_external_recursive_body_fragment_closure = _has_theorem_in(
                body_closure_code, "compileStmtList_external_recursive_body_fragment_bridged"
            )
            external_recursive_body_fragment_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "compileStmtList_external_recursive_body_fragment_bridged"
            )
            has_internal_recursive_body_fragment_closure = _has_theorem_in(
                body_closure_code, "compileStmtList_internal_recursive_body_fragment_bridged"
            )
            internal_recursive_body_fragment_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "compileStmtList_internal_recursive_body_fragment_bridged"
            )
            # Universal body-closure metatheorem (plan #1722 B7). When present and
            # proven, every compileStmtList output for external-safe source
            # statement lists discharges `BridgedStmts` without per-call
            # hypotheses. The phase4 status only reaches
            # "full_semantic_integration" after the public EndToEnd theorem
            # stops carrying explicit BridgedStmts body hypotheses as well.
            has_universal_body_closure = _has_theorem_in(
                body_closure_code, "compileStmtList_always_bridged"
            )
            universal_body_closure_has_sorry = _theorem_body_has_sorry_in(
                body_closure_code, "compileStmtList_always_bridged"
            )
        else:
            has_scalar_param_body_closure = False
            scalar_param_body_closure_has_sorry = False
            has_static_type_body_closure = False
            static_type_body_closure_has_sorry = False
            has_static_param_body_closure = False
            static_param_body_closure_has_sorry = False
            has_binding_stmt_body_closure = False
            binding_stmt_body_closure_has_sorry = False
            has_pure_binding_stmt_body_closure = False
            pure_binding_stmt_body_closure_has_sorry = False
            has_storage_fragment_body_closure = False
            storage_fragment_body_closure_has_sorry = False
            has_terminator_body_closure = False
            terminator_body_closure_has_sorry = False
            has_internal_return_body_closure = False
            internal_return_body_closure_has_sorry = False
            has_require_body_closure = False
            require_body_closure_has_sorry = False
            has_external_body_fragment_closure = False
            external_body_fragment_closure_has_sorry = False
            has_internal_body_fragment_closure = False
            internal_body_fragment_closure_has_sorry = False
            has_external_structured_body_fragment_closure = False
            external_structured_body_fragment_closure_has_sorry = False
            has_internal_structured_body_fragment_closure = False
            internal_structured_body_fragment_closure_has_sorry = False
            has_external_nested_body_fragment_closure = False
            external_nested_body_fragment_closure_has_sorry = False
            has_internal_nested_body_fragment_closure = False
            internal_nested_body_fragment_closure_has_sorry = False
            has_external_recursive_body_fragment_closure = False
            external_recursive_body_fragment_closure_has_sorry = False
            has_internal_recursive_body_fragment_closure = False
            internal_recursive_body_fragment_closure_has_sorry = False
            has_universal_body_closure = False
            universal_body_closure_has_sorry = False
        if SOURCE_EXPR_CLOSURE_FILE.exists():
            source_expr_closure_code = _strip_lean_strings(
                _strip_lean_comments(SOURCE_EXPR_CLOSURE_FILE.read_text(encoding="utf-8"))
            )
            has_source_expr_leaf_closure = _has_theorem_in(
                source_expr_closure_code, "compileExpr_bridgedSource_leaf"
            )
            source_expr_leaf_closure_has_sorry = _theorem_body_has_sorry_in(
                source_expr_closure_code, "compileExpr_bridgedSource_leaf"
            )
            has_source_expr_pure_closure = _has_theorem_in(
                source_expr_closure_code, "compileExpr_bridgedSource"
            )
            source_expr_pure_closure_has_sorry = _theorem_body_has_sorry_in(
                source_expr_closure_code, "compileExpr_bridgedSource"
            )
        else:
            has_source_expr_leaf_closure = False
            source_expr_leaf_closure_has_sorry = False
            has_source_expr_pure_closure = False
            source_expr_pure_closure_has_sorry = False
        if not has_scalar_param_body_closure:
            scalar_param_body_closure_status = "missing"
        elif scalar_param_body_closure_has_sorry:
            scalar_param_body_closure_status = "sorry"
        else:
            scalar_param_body_closure_status = "proven (scalar calldata parameters)"
        if not has_static_type_body_closure:
            static_type_body_closure_status = "missing"
        elif static_type_body_closure_has_sorry:
            static_type_body_closure_status = "sorry"
        else:
            static_type_body_closure_status = "proven (static scalar calldata leaves)"
        if not has_static_param_body_closure:
            static_param_body_closure_status = "missing"
        elif static_param_body_closure_has_sorry:
            static_param_body_closure_status = "sorry"
        else:
            static_param_body_closure_status = "proven (static scalar calldata parameters)"
        if not has_binding_stmt_body_closure:
            binding_stmt_body_closure_status = "missing"
        elif binding_stmt_body_closure_has_sorry:
            binding_stmt_body_closure_status = "sorry"
        else:
            binding_stmt_body_closure_status = "proven (scalar let/assign statement lists)"
        if not has_pure_binding_stmt_body_closure:
            pure_binding_stmt_body_closure_status = "missing"
        elif pure_binding_stmt_body_closure_has_sorry:
            pure_binding_stmt_body_closure_status = "sorry"
        else:
            pure_binding_stmt_body_closure_status = "proven (pure let/assign statement lists)"
        if not has_storage_fragment_body_closure:
            storage_fragment_body_closure_status = "missing"
        elif storage_fragment_body_closure_has_sorry:
            storage_fragment_body_closure_status = "sorry"
        else:
            storage_fragment_body_closure_status = (
                "proven (pure bindings plus single-slot setStorage statement lists)"
            )
        if not has_terminator_body_closure:
            terminator_body_closure_status = "missing"
        elif terminator_body_closure_has_sorry:
            terminator_body_closure_status = "sorry"
        else:
            terminator_body_closure_status = "proven (external stop/return statement lists)"
        if not has_internal_return_body_closure:
            internal_return_body_closure_status = "missing"
        elif internal_return_body_closure_has_sorry:
            internal_return_body_closure_status = "sorry"
        else:
            internal_return_body_closure_status = "proven (internal return statement lists)"
        if not has_require_body_closure:
            require_body_closure_status = "missing"
        elif require_body_closure_has_sorry:
            require_body_closure_status = "sorry"
        else:
            require_body_closure_status = "proven (require statement lists)"
        if not has_external_body_fragment_closure:
            external_body_fragment_closure_status = "missing"
        elif external_body_fragment_closure_has_sorry:
            external_body_fragment_closure_status = "sorry"
        else:
            external_body_fragment_closure_status = "proven (mixed external body fragment)"
        if not has_internal_body_fragment_closure:
            internal_body_fragment_closure_status = "missing"
        elif internal_body_fragment_closure_has_sorry:
            internal_body_fragment_closure_status = "sorry"
        else:
            internal_body_fragment_closure_status = "proven (mixed internal body fragment)"
        if not has_external_structured_body_fragment_closure:
            external_structured_body_fragment_closure_status = "missing"
        elif external_structured_body_fragment_closure_has_sorry:
            external_structured_body_fragment_closure_status = "sorry"
        else:
            external_structured_body_fragment_closure_status = (
                "proven (mixed external body fragment plus one ite layer)"
            )
        if not has_internal_structured_body_fragment_closure:
            internal_structured_body_fragment_closure_status = "missing"
        elif internal_structured_body_fragment_closure_has_sorry:
            internal_structured_body_fragment_closure_status = "sorry"
        else:
            internal_structured_body_fragment_closure_status = (
                "proven (mixed internal body fragment plus one ite layer)"
            )
        if not has_external_nested_body_fragment_closure:
            external_nested_body_fragment_closure_status = "missing"
        elif external_nested_body_fragment_closure_has_sorry:
            external_nested_body_fragment_closure_status = "sorry"
        else:
            external_nested_body_fragment_closure_status = (
                "proven (mixed external body fragment plus two ite layers)"
            )
        if not has_internal_nested_body_fragment_closure:
            internal_nested_body_fragment_closure_status = "missing"
        elif internal_nested_body_fragment_closure_has_sorry:
            internal_nested_body_fragment_closure_status = "sorry"
        else:
            internal_nested_body_fragment_closure_status = (
                "proven (mixed internal body fragment plus two ite layers)"
            )
        if not has_external_recursive_body_fragment_closure:
            external_recursive_body_fragment_closure_status = "missing"
        elif external_recursive_body_fragment_closure_has_sorry:
            external_recursive_body_fragment_closure_status = "sorry"
        else:
            external_recursive_body_fragment_closure_status = (
                "proven (mixed external body fragment plus recursive ite closure)"
            )
        if not has_internal_recursive_body_fragment_closure:
            internal_recursive_body_fragment_closure_status = "missing"
        elif internal_recursive_body_fragment_closure_has_sorry:
            internal_recursive_body_fragment_closure_status = "sorry"
        else:
            internal_recursive_body_fragment_closure_status = (
                "proven (mixed internal body fragment plus recursive ite closure)"
            )
        if not has_source_expr_leaf_closure:
            source_expr_leaf_closure_status = "missing"
        elif source_expr_leaf_closure_has_sorry:
            source_expr_leaf_closure_status = "sorry"
        else:
            source_expr_leaf_closure_status = "proven (scalar source-expression leaves)"
        if not has_source_expr_pure_closure:
            source_expr_pure_closure_status = "missing"
        elif source_expr_pure_closure_has_sorry:
            source_expr_pure_closure_status = "sorry"
        else:
            source_expr_pure_closure_status = "proven (pure source-expression fragment)"
        if not has_universal_body_closure:
            universal_body_closure_status = "missing"
        elif universal_body_closure_has_sorry:
            universal_body_closure_status = "sorry"
        else:
            universal_body_closure_status = (
                "proven (universal compileStmtList body closure for BridgedSafeStmts; "
                "external-call family carved out)"
            )

        if (
            has_universal_body_closure
            and not universal_body_closure_has_sorry
            and has_end_to_end_evm_retarget
            and not end_to_end_evm_retarget_has_sorry
            and not end_to_end_evm_retarget_has_body_hypotheses
            and has_layer3_evm_retarget
            and not layer3_evm_retarget_has_sorry
            and
            has_runtime_backend_eq
            and not runtime_backend_eq_has_sorry
            and
            has_runtime_closure
            and not runtime_closure_has_sorry
            and
            has_recursive_target_retarget
            and not recursive_target_retarget_has_sorry
            and
            has_for_stmt_retarget
            and not for_stmt_retarget_has_sorry
            and
            has_switch_stmt_retarget
            and not switch_stmt_retarget_has_sorry
            and
            has_if_stmt_retarget
            and not if_stmt_retarget_has_sorry
            and
            has_block_stmt_retarget
            and not block_stmt_retarget_has_sorry
            and has_straight_stmt_retarget
            and not straight_stmt_retarget_has_sorry
            and has_expr_retarget
            and not expr_retarget_has_sorry
            and not admitted_deps
        ):
            phase4_status = "full_semantic_integration"
        elif (
            has_universal_body_closure
            and not universal_body_closure_has_sorry
            and has_end_to_end_evm_retarget
            and not end_to_end_evm_retarget_has_sorry
            and has_layer3_evm_retarget
            and not layer3_evm_retarget_has_sorry
            and has_runtime_backend_eq
            and not runtime_backend_eq_has_sorry
            and has_runtime_closure
            and not runtime_closure_has_sorry
            and has_recursive_target_retarget
            and not recursive_target_retarget_has_sorry
            and has_for_stmt_retarget
            and not for_stmt_retarget_has_sorry
            and has_switch_stmt_retarget
            and not switch_stmt_retarget_has_sorry
            and has_if_stmt_retarget
            and not if_stmt_retarget_has_sorry
            and has_block_stmt_retarget
            and not block_stmt_retarget_has_sorry
            and has_straight_stmt_retarget
            and not straight_stmt_retarget_has_sorry
            and has_expr_retarget
            and not expr_retarget_has_sorry
            and not admitted_deps
        ):
            phase4_status = "universal-safe-body-closure"
        elif (
            has_end_to_end_evm_retarget
            and not end_to_end_evm_retarget_has_sorry
            and
            has_layer3_evm_retarget
            and not layer3_evm_retarget_has_sorry
            and
            has_runtime_backend_eq
            and not runtime_backend_eq_has_sorry
            and
            has_runtime_closure
            and not runtime_closure_has_sorry
            and
            has_recursive_target_retarget
            and not recursive_target_retarget_has_sorry
            and
            has_for_stmt_retarget
            and not for_stmt_retarget_has_sorry
            and
            has_switch_stmt_retarget
            and not switch_stmt_retarget_has_sorry
            and
            has_if_stmt_retarget
            and not if_stmt_retarget_has_sorry
            and
            has_block_stmt_retarget
            and not block_stmt_retarget_has_sorry
            and has_straight_stmt_retarget
            and not straight_stmt_retarget_has_sorry
            and has_expr_retarget
            and not expr_retarget_has_sorry
            and not admitted_deps
        ):
            phase4_status = "layer3-contract-evmyullean-target"
        elif (
            has_runtime_backend_eq
            and not runtime_backend_eq_has_sorry
            and
            has_runtime_closure
            and not runtime_closure_has_sorry
            and
            has_recursive_target_retarget
            and not recursive_target_retarget_has_sorry
            and
            has_for_stmt_retarget
            and not for_stmt_retarget_has_sorry
            and
            has_switch_stmt_retarget
            and not switch_stmt_retarget_has_sorry
            and
            has_if_stmt_retarget
            and not if_stmt_retarget_has_sorry
            and
            has_block_stmt_retarget
            and not block_stmt_retarget_has_sorry
            and has_straight_stmt_retarget
            and not straight_stmt_retarget_has_sorry
            and has_expr_retarget
            and not expr_retarget_has_sorry
            and not admitted_deps
        ):
            phase4_status = "runtime-backend-equality-recursive-statement-target-level"
        elif (
            has_runtime_closure
            and not runtime_closure_has_sorry
            and
            has_recursive_target_retarget
            and not recursive_target_retarget_has_sorry
            and
            has_for_stmt_retarget
            and not for_stmt_retarget_has_sorry
            and
            has_switch_stmt_retarget
            and not switch_stmt_retarget_has_sorry
            and
            has_if_stmt_retarget
            and not if_stmt_retarget_has_sorry
            and
            has_block_stmt_retarget
            and not block_stmt_retarget_has_sorry
            and has_straight_stmt_retarget
            and not straight_stmt_retarget_has_sorry
            and has_expr_retarget
            and not expr_retarget_has_sorry
            and not admitted_deps
        ):
            phase4_status = "runtime-closure-recursive-statement-target-level"
        elif (
            has_recursive_target_retarget
            and not recursive_target_retarget_has_sorry
            and
            has_for_stmt_retarget
            and not for_stmt_retarget_has_sorry
            and
            has_switch_stmt_retarget
            and not switch_stmt_retarget_has_sorry
            and
            has_if_stmt_retarget
            and not if_stmt_retarget_has_sorry
            and
            has_block_stmt_retarget
            and not block_stmt_retarget_has_sorry
            and has_straight_stmt_retarget
            and not straight_stmt_retarget_has_sorry
            and has_expr_retarget
            and not expr_retarget_has_sorry
            and not admitted_deps
        ):
            phase4_status = "recursive-statement-target-level"
        elif (
            has_for_stmt_retarget
            and not for_stmt_retarget_has_sorry
            and
            has_switch_stmt_retarget
            and not switch_stmt_retarget_has_sorry
            and
            has_if_stmt_retarget
            and not if_stmt_retarget_has_sorry
            and
            has_block_stmt_retarget
            and not block_stmt_retarget_has_sorry
            and has_straight_stmt_retarget
            and not straight_stmt_retarget_has_sorry
            and has_expr_retarget
            and not expr_retarget_has_sorry
            and not admitted_deps
        ):
            phase4_status = "for-switch-if-straight-line-statement-level"
        elif (
            has_switch_stmt_retarget
            and not switch_stmt_retarget_has_sorry
            and has_if_stmt_retarget
            and not if_stmt_retarget_has_sorry
            and has_block_stmt_retarget
            and not block_stmt_retarget_has_sorry
            and has_straight_stmt_retarget
            and not straight_stmt_retarget_has_sorry
            and has_expr_retarget
            and not expr_retarget_has_sorry
            and not admitted_deps
        ):
            phase4_status = "switch-if-straight-line-statement-level"
        elif (
            has_if_stmt_retarget
            and not if_stmt_retarget_has_sorry
            and has_block_stmt_retarget
            and not block_stmt_retarget_has_sorry
            and has_straight_stmt_retarget
            and not straight_stmt_retarget_has_sorry
            and has_expr_retarget
            and not expr_retarget_has_sorry
            and not admitted_deps
        ):
            phase4_status = "if-straight-line-statement-level"
        elif (
            has_block_stmt_retarget
            and not block_stmt_retarget_has_sorry
            and has_straight_stmt_retarget
            and not straight_stmt_retarget_has_sorry
            and has_expr_retarget
            and not expr_retarget_has_sorry
            and not admitted_deps
        ):
            phase4_status = "block-wrapped-straight-line-statement-level"
        elif (
            has_straight_stmt_retarget
            and not straight_stmt_retarget_has_sorry
            and has_expr_retarget
            and not expr_retarget_has_sorry
            and not admitted_deps
        ):
            phase4_status = "straight-line-statement-level"
        elif has_expr_retarget and not expr_retarget_has_sorry and not admitted_deps:
            phase4_status = "expression-level"
        elif has_backends_agree and not backends_agree_has_sorry and not admitted_deps:
            phase4_status = "pointwise"
        else:
            phase4_status = "incomplete"

        remaining_for_whole_program_retargeting = []
        if admitted_deps:
            remaining_for_whole_program_retargeting.append(
                f"{'/'.join(admitted_deps)} core equivalence"
                f"{'s' if len(admitted_deps) != 1 else ''} "
                "(complex Int↔UInt256 sign/bit semantics)"
            )
        if not has_universal_body_closure or universal_body_closure_has_sorry:
            remaining_for_whole_program_retargeting.extend(
                [
                    "ABI-encoded return/error closures: returnArray, returnBytes, returnStorageWords, emit, revertError/requireError with args",
                    "new BridgedStraightStmt ctors for calldatacopy, returndatacopy, and revertReturndata (currently no bridged ctor)",
                    "universal compileStmtList_always_bridged metatheorem with a BridgedSafeStmts whitelist predicate (external-call family — internalCall, internalCallAssign, externalCallBind, ecm — remains explicitly carved out behind hFunctions hypotheses)",
                ]
            )
        if (
            not has_end_to_end_evm_retarget
            or end_to_end_evm_retarget_has_sorry
            or end_to_end_evm_retarget_has_body_hypotheses
        ):
            remaining_for_whole_program_retargeting.append(
                "discharge the conditional EndToEnd theorem's bridged-body hypotheses for full compiler-produced contracts"
            )

        phase4_trust_boundary = (
            "recursive BridgedTarget statement fragment: EVMYulLean execution model "
            "matches EVM (upstream conformance tests) for BridgedExpr expressions, "
            "BridgedStraightStmts (including mapping-slot, literal-slot, and "
            "identifier-slot sstore), and recursively nested BridgedStmt targets; "
            "generated runtime-code closure, emitted-runtime backend equality, and the "
            "lower-level Layer-3 EVMYulLean retarget theorem are proven under bridged "
            "IR-body witnesses; the public EndToEnd safe-body wrapper discharges raw "
            "BridgedStmts body hypotheses from SupportedSpec, static-parameter, and "
            "BridgedSafeStmts source witnesses; "
            "compileStmtList_always_bridged proves a universal BridgedSafeStmts aggregation "
            "theorem with the external-call family carved out behind explicit function-table "
            "hypotheses"
        )

        phase4_retarget = {
            "retarget_file": str(retarget_file.relative_to(ROOT)),
            "status": phase4_status,
            "admitted_bridge_dependencies": admitted_deps,
            "backends_agree_on_bridged_builtins": backends_agree_status,
            "evalYulExpr_evmYulLean_eq_on_bridged": expr_retarget_status,
            "execYulFuelWithBackend_eq_on_bridged_straight_stmts": straight_stmt_retarget_status,
            "execYulFuelWithBackend_block_eq_on_bridged_straight_stmts": block_stmt_retarget_status,
            "execYulFuelWithBackend_if_eq_on_bridged_body": if_stmt_retarget_status,
            "execYulFuelWithBackend_switch_eq_on_bridged_cases": switch_stmt_retarget_status,
            "execYulFuelWithBackend_for_eq_on_bridged_parts": for_stmt_retarget_status,
            "execYulFuelWithBackend_eq_on_bridged_target": recursive_target_retarget_status,
            "emitYul_runtimeCode_bridged": runtime_closure_status,
            "emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies": runtime_backend_eq_status,
            "yulCodegen_preserves_semantics_evmYulLeanFuelWrapperDefaultFuel_via_reference_oracle": layer3_evm_retarget_status,
            "layers2_3_ir_matches_yul_evmYulLeanFuelWrapperDefaultFuel": end_to_end_evm_retarget_status,
            "genParamLoads_scalar_bridged": scalar_param_body_closure_status,
            "genStaticTypeLoads_calldataload_bridged": static_type_body_closure_status,
            "genParamLoads_static_scalar_bridged": static_param_body_closure_status,
            "compileStmtList_binding_leaf_bridged": binding_stmt_body_closure_status,
            "compileStmtList_pure_binding_bridged": pure_binding_stmt_body_closure_status,
            "compileStmtList_storage_fragment_bridged": storage_fragment_body_closure_status,
            "compileStmtList_terminator_external_bridged": terminator_body_closure_status,
            "compileStmtList_internal_return_bridged": internal_return_body_closure_status,
            "compileStmtList_require_bridged": require_body_closure_status,
            "compileStmtList_external_body_fragment_bridged": external_body_fragment_closure_status,
            "compileStmtList_internal_body_fragment_bridged": internal_body_fragment_closure_status,
            "compileStmtList_external_structured_body_fragment_bridged": external_structured_body_fragment_closure_status,
            "compileStmtList_internal_structured_body_fragment_bridged": internal_structured_body_fragment_closure_status,
            "compileStmtList_external_nested_body_fragment_bridged": external_nested_body_fragment_closure_status,
            "compileStmtList_internal_nested_body_fragment_bridged": internal_nested_body_fragment_closure_status,
            "compileStmtList_external_recursive_body_fragment_bridged": external_recursive_body_fragment_closure_status,
            "compileStmtList_internal_recursive_body_fragment_bridged": internal_recursive_body_fragment_closure_status,
            "compileExpr_bridgedSource_leaf": source_expr_leaf_closure_status,
            "compileExpr_bridgedSource": source_expr_pure_closure_status,
            "compileStmtList_always_bridged": universal_body_closure_status,
            "trust_boundary": phase4_trust_boundary,
            "remaining_for_whole_program_retargeting": remaining_for_whole_program_retargeting,
        }

    report: dict[str, object] = {
        "schema_version": 7,
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

    # Phase 4 readiness fields (schema v5)
    report["context_lifted_bridge_lemmas"] = context_bridged
    report["fallthrough_lemmas"] = fallthrough
    if bridged_defs:
        report["bridged_builtins"] = bridged_defs
    if unbridged_defs:
        report["unbridged_builtins"] = unbridged_defs

    # Phase 4 retarget (schema v6)
    if phase4_retarget:
        report["phase4_retarget"] = phase4_retarget

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
