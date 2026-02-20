#!/usr/bin/env python3
"""Validate selector hashing against solc fixtures.

Runs `solc --hashes` on a small Solidity fixture and compares the
reported selectors to the keccak implementation used by our tools.
"""

from __future__ import annotations

import re
import subprocess

from keccak256 import keccak_256, selector as compute_selector
from property_utils import ROOT, die, report_errors
FIXTURE = ROOT / "scripts" / "fixtures" / "SelectorFixtures.sol"

FUNCTION_START_RE = re.compile(r"\bfunction\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(")
EVENT_START_RE = re.compile(r"\bevent\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(")
SELECTOR_VISIBILITY_RE = re.compile(r"\b(external|public)\b")
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
ARRAY_SUFFIX_RE = re.compile(r"(\[[0-9]*\]\s*)+$")
HASH_RE = re.compile(r"^(0x)?([0-9a-fA-F]{8}|[0-9a-fA-F]{64})$")
CONTRACT_LIKE_DECL_RE = re.compile(r"\b(?:contract|interface|library)\s+([A-Za-z_][A-Za-z0-9_]*)\b")
ENUM_DECL_RE = re.compile(r"\benum\s+([A-Za-z_][A-Za-z0-9_]*)\s*\{")
UDVT_DECL_RE = re.compile(r"\btype\s+([A-Za-z_][A-Za-z0-9_]*)\s+is\s+([^;]+);")
STRUCT_DECL_RE = re.compile(r"\bstruct\s+([A-Za-z_][A-Za-z0-9_]*)\s*\{")


def _split_top_level_commas(params: str) -> list[str]:
    items: list[str] = []
    depth = 0
    start = 0
    for i, ch in enumerate(params):
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth = max(0, depth - 1)
        elif ch == "," and depth == 0:
            items.append(params[start:i].strip())
            start = i + 1
    tail = params[start:].strip()
    if tail:
        items.append(tail)
    return items


def _split_top_level_semicolons(text: str) -> list[str]:
    items: list[str] = []
    paren_depth = 0
    bracket_depth = 0
    brace_depth = 0
    start = 0
    for i, ch in enumerate(text):
        if ch == "(":
            paren_depth += 1
        elif ch == ")":
            paren_depth = max(0, paren_depth - 1)
        elif ch == "[":
            bracket_depth += 1
        elif ch == "]":
            bracket_depth = max(0, bracket_depth - 1)
        elif ch == "{":
            brace_depth += 1
        elif ch == "}":
            brace_depth = max(0, brace_depth - 1)
        elif ch == ";" and paren_depth == 0 and bracket_depth == 0 and brace_depth == 0:
            items.append(text[start:i].strip())
            start = i + 1
    tail = text[start:].strip()
    if tail:
        items.append(tail)
    return items


def _split_array_suffix(text: str) -> tuple[str, str]:
    suffix_match = ARRAY_SUFFIX_RE.search(text)
    if not suffix_match or suffix_match.end() != len(text):
        return text, ""
    base = text[: suffix_match.start()].strip()
    suffix = re.sub(r"\s+", "", suffix_match.group(0))
    return base, suffix


def _canonical_base_type(text: str, user_aliases: dict[str, str]) -> str:
    if text == "uint":
        return "uint256"
    if text == "int":
        return "int256"
    if text == "fixed":
        return "fixed128x18"
    if text == "ufixed":
        return "ufixed128x18"
    if text.startswith("tuple("):
        return text
    if text.startswith("(") and text.endswith(")"):
        return text

    current = text
    seen: set[str] = set()
    while current not in seen:
        seen.add(current)
        alias = user_aliases.get(current)
        if alias is None and "." in current:
            alias = user_aliases.get(current.split(".")[-1])
        if alias is None:
            break
        current = alias
    return current


def _canonical_param_type(raw: str, user_aliases: dict[str, str]) -> str:
    # Remove data location and declaration keywords from declarations.
    text = re.sub(r"\b(memory|calldata|storage|payable|indexed)\b", " ", raw)
    text = re.sub(r"\s+", " ", text).strip()
    if not text:
        return ""

    text = _drop_trailing_param_name(text)

    # Solidity function types are selector-encoded as `function`,
    # regardless of their full internal signature.
    text = re.sub(r"\s*([\[\]\(\),])\s*", r"\1", text)

    if text.startswith("function"):
        _, suffix = _split_array_suffix(text)
        return f"function{suffix}"

    base, suffix = _split_array_suffix(text)
    return f"{_canonical_base_type(base, user_aliases)}{suffix}"


def _drop_trailing_param_name(text: str) -> str:
    paren_depth = 0
    bracket_depth = 0
    last_space = -1
    for idx, ch in enumerate(text):
        if ch == "(":
            paren_depth += 1
        elif ch == ")":
            paren_depth = max(0, paren_depth - 1)
        elif ch == "[":
            bracket_depth += 1
        elif ch == "]":
            bracket_depth = max(0, bracket_depth - 1)
        elif ch == " " and paren_depth == 0 and bracket_depth == 0:
            last_space = idx
    if last_space == -1:
        return text

    tail = text[last_space + 1 :].strip()
    if IDENT_RE.fullmatch(tail):
        return text[:last_space].rstrip()
    return text


def _strip_param_names(params: str, user_aliases: dict[str, str]) -> str:
    if not params.strip():
        return ""
    cleaned: list[str] = []
    for raw in _split_top_level_commas(params):
        canonical = _canonical_param_type(raw, user_aliases)
        if canonical:
            cleaned.append(canonical)
    return ",".join(cleaned)


def _collect_user_defined_type_aliases(text: str) -> dict[str, str]:
    aliases: dict[str, str] = {}
    for match in CONTRACT_LIKE_DECL_RE.finditer(text):
        aliases[match.group(1)] = "address"
    for match in ENUM_DECL_RE.finditer(text):
        aliases[match.group(1)] = "uint8"

    udvt: list[tuple[str, str]] = []
    for match in UDVT_DECL_RE.finditer(text):
        name = match.group(1)
        underlying = re.sub(r"\s+", "", match.group(2))
        udvt.append((name, underlying))

    # Resolve UDVT aliases after collecting all declarations.
    for _ in range(4):
        for name, underlying in udvt:
            aliases[name] = _canonical_base_type(underlying, aliases)

    struct_fields = _collect_struct_field_types(text)
    # Resolve nested struct aliases after primitives/enums/contracts/UDVTs.
    for _ in range(len(struct_fields) + 2):
        for name, fields in struct_fields.items():
            canonical_fields = [_canonical_param_type(field, aliases) for field in fields]
            aliases[name] = f"({','.join(canonical_fields)})"
    return aliases


def _strip_solidity_comments_and_strings(text: str) -> str:
    """Strip comments and strings while preserving newlines."""
    out: list[str] = []
    i = 0
    n = len(text)
    in_line_comment = False
    in_block_comment = False
    quote: str | None = None

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue

        if in_block_comment:
            if ch == "*" and nxt == "/":
                out.extend([" ", " "])
                i += 2
                in_block_comment = False
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
            continue

        if quote is not None:
            if ch == "\\" and i + 1 < n:
                out.extend([" ", " "])
                i += 2
                continue
            if ch == quote:
                out.append(" ")
                quote = None
                i += 1
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        if ch == "/" and nxt == "/":
            out.extend([" ", " "])
            i += 2
            in_line_comment = True
            continue
        if ch == "/" and nxt == "*":
            out.extend([" ", " "])
            i += 2
            in_block_comment = True
            continue
        if ch in {'"', "'"}:
            out.append(" ")
            quote = ch
            i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def _find_matching_paren(text: str, open_index: int) -> int:
    depth = 0
    for idx in range(open_index, len(text)):
        ch = text[idx]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return idx
    return -1


def _find_matching_brace(text: str, open_index: int) -> int:
    depth = 0
    for idx in range(open_index, len(text)):
        ch = text[idx]
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return idx
    return -1


def _collect_struct_field_types(text: str) -> dict[str, list[str]]:
    structs: dict[str, list[str]] = {}
    for match in STRUCT_DECL_RE.finditer(text):
        name = match.group(1)
        open_brace = match.end() - 1
        close_brace = _find_matching_brace(text, open_brace)
        if close_brace == -1:
            continue
        body = text[open_brace + 1 : close_brace]
        fields: list[str] = []
        for decl in _split_top_level_semicolons(body):
            field_type = _drop_trailing_param_name(re.sub(r"\s+", " ", decl).strip())
            if field_type:
                fields.append(field_type)
        structs[name] = fields
    return structs


def _find_header_end(text: str, start: int) -> int:
    depth = 0
    for idx in range(start, len(text)):
        ch = text[idx]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth = max(0, depth - 1)
        elif depth == 0 and ch in "{;":
            return idx
    return -1


def _iter_function_signatures(text: str) -> list[tuple[str, str]]:
    signatures: list[tuple[str, str]] = []
    for match in FUNCTION_START_RE.finditer(text):
        name = match.group(1)
        open_paren = match.end() - 1
        close_paren = _find_matching_paren(text, open_paren)
        if close_paren == -1:
            continue
        header_end = _find_header_end(text, close_paren + 1)
        if header_end == -1:
            continue

        suffix = text[close_paren + 1 : header_end]
        # solc --hashes only reports selectors for public/external functions.
        if not SELECTOR_VISIBILITY_RE.search(suffix):
            continue

        params = text[open_paren + 1 : close_paren].strip()
        signatures.append((name, params))
    return signatures


def _iter_event_signatures(text: str) -> list[tuple[str, str]]:
    signatures: list[tuple[str, str]] = []
    for match in EVENT_START_RE.finditer(text):
        name = match.group(1)
        open_paren = match.end() - 1
        close_paren = _find_matching_paren(text, open_paren)
        if close_paren == -1:
            continue
        decl_end = _find_header_end(text, close_paren + 1)
        if decl_end == -1 or text[decl_end] != ";":
            continue
        params = text[open_paren + 1 : close_paren].strip()
        signatures.append((name, params))
    return signatures


def _load_fixture_text_and_aliases() -> tuple[str, dict[str, str]]:
    if not FIXTURE.exists():
        die(f"Missing fixture file: {FIXTURE}")
    text = _strip_solidity_comments_and_strings(FIXTURE.read_text(encoding="utf-8"))
    aliases = _collect_user_defined_type_aliases(text)
    return text, aliases


def load_fixture_function_signatures() -> list[str]:
    text, aliases = _load_fixture_text_and_aliases()
    sigs: list[str] = []
    for name, params in _iter_function_signatures(text):
        params = _strip_param_names(params, aliases)
        sigs.append(f"{name}({params})")
    if not sigs:
        die("No function signatures found in fixture")
    return sigs


def load_fixture_event_signatures() -> list[str]:
    text, aliases = _load_fixture_text_and_aliases()
    sigs: list[str] = []
    for name, params in _iter_event_signatures(text):
        params = _strip_param_names(params, aliases)
        sigs.append(f"{name}({params})")
    if not sigs:
        die("No event signatures found in fixture")
    return sigs


def _parse_hash_fixture_line(line: str) -> tuple[str, str] | None:
    if ":" not in line:
        return None
    left, right = [part.strip() for part in line.split(":", 1)]
    if not left or not right:
        return None

    left_hash = HASH_RE.fullmatch(left)
    right_hash = HASH_RE.fullmatch(right)

    if left_hash and "(" in right and right.endswith(")"):
        return right, left_hash.group(2).lower()
    if right_hash and "(" in left and left.endswith(")"):
        return left, right_hash.group(2).lower()
    return None


def run_solc_hashes() -> dict[str, str]:
    result = subprocess.run(
        ["solc", "--hashes", str(FIXTURE)],
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        die(f"solc --hashes failed: {result.stderr.strip()}")
    hashes: dict[str, str] = {}
    for line in result.stdout.splitlines():
        line = line.strip()
        if not line or line.endswith(":"):
            continue
        parsed = _parse_hash_fixture_line(line)
        if parsed is not None:
            signature, digest = parsed
            hashes[signature] = digest
            continue
    if not hashes:
        die("No signature hashes parsed from solc output")
    return hashes


def run_keccak_selectors(signatures: list[str]) -> dict[str, str]:
    return {sig: compute_selector(sig).replace("0x", "") for sig in signatures}


def run_keccak_event_hashes(signatures: list[str]) -> dict[str, str]:
    return {sig: keccak_256(sig.encode("utf-8")).hex() for sig in signatures}


def main() -> None:
    function_signatures = load_fixture_function_signatures()
    event_signatures = load_fixture_event_signatures()
    solc_hashes = run_solc_hashes()
    keccak_selectors = run_keccak_selectors(function_signatures)
    keccak_event_hashes = run_keccak_event_hashes(event_signatures)
    overlap = sorted(set(keccak_selectors).intersection(keccak_event_hashes))
    if overlap:
        die(
            "Fixture contains function/event signature overlaps that make "
            f"`solc --hashes` mapping ambiguous: {', '.join(overlap)}"
        )

    expected_hashes = {**keccak_selectors, **keccak_event_hashes}
    signature_set = set(expected_hashes)

    errors: list[str] = []
    for signature in sorted(solc_hashes):
        if signature not in signature_set:
            errors.append(f"Fixture extraction missed solc signature: {signature}")

    for signature, expected_hash in expected_hashes.items():
        solc_hash = solc_hashes.get(signature)
        if solc_hash is None:
            errors.append(f"Missing solc hash for {signature}")
            continue
        if len(solc_hash) != len(expected_hash):
            errors.append(
                f"Hash width mismatch for {signature}: solc={len(solc_hash)} expected={len(expected_hash)}"
            )
            continue
        if solc_hash != expected_hash:
            errors.append(
                f"Hash mismatch for {signature}: solc={solc_hash} keccak={expected_hash}"
            )

    report_errors(errors, "Selector/event fixture check failed")

    print("Selector/event fixture check passed.")


if __name__ == "__main__":
    main()
