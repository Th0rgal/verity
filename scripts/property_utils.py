#!/usr/bin/env python3
"""Shared utilities for property manifest and coverage checking."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

# Path constants
ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "test" / "property_manifest.json"
EXCLUSIONS = ROOT / "test" / "property_exclusions.json"
TEST_DIR = ROOT / "test"
PROOFS_DIR = ROOT / "Contracts"
EXAMPLES_DIR = ROOT / "Contracts"
YUL_DIR = ROOT / "compiler" / "yul"

# Regex patterns for extracting property tags from test files
PROPERTY_WITH_NUM_RE = re.compile(
    r"^\s*(?:///|\*)\s*Property\s+\d+[A-Za-z]*\s*:\s*([A-Za-z0-9_']+)(?:\s*\(.*\))?\s*$"
)
PROPERTY_SIMPLE_RE = re.compile(
    r"^\s*(?:///|\*)\s*Property\s*:\s*([A-Za-z0-9_']+)(?:\s*\(.*\))?\s*$"
)
FILE_RE = re.compile(r"^Property(.+)\.t\.sol$")
CONTRACT_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
THEOREM_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
LEAN_IMPORT_RE = re.compile(r"^\s*import\b(?P<body>.*)$")
LEAN_MODULE_NAME_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_.']*$")

# Regex pattern for theorem/lemma declarations with optional Lean prefixes.
THEOREM_RE = re.compile(
    r"^\s*(?P<attrs>(?:@\[[^\]]*\]\s*)*)(?P<visibility>(?:(?:private|protected)\s+)*)"
    r"(?P<kind>theorem|lemma)\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b"
)


def _require_contract_identifier(contract: str, source: Path) -> str:
    """Validate and return a contract identifier from a filesystem-derived source."""
    if contract != contract.strip() or not CONTRACT_NAME_RE.fullmatch(contract):
        raise SystemExit(
            f"Invalid contract identifier from {source}: {contract!r}"
        )
    return contract


def _require_theorem_identifier(
    theorem: str, source: Path, *, context: str | None = None
) -> str:
    """Validate and return a theorem identifier from a filesystem-derived source."""
    if theorem != theorem.strip() or not THEOREM_NAME_RE.fullmatch(theorem):
        location = f"{source} ({context})" if context else str(source)
        raise SystemExit(
            f"Invalid theorem identifier from {location}: {theorem!r}"
        )
    return theorem


def load_manifest() -> dict[str, set[str]]:
    """Load property manifest from JSON file.

    Returns:
        Dictionary mapping contract names to sets of theorem names.

    Raises:
        SystemExit: If manifest file does not exist.
    """
    return _load_contract_name_sets(MANIFEST, missing_ok=False)


def load_exclusions() -> dict[str, set[str]]:
    """Load property exclusions from JSON file.

    Returns:
        Dictionary mapping contract names to sets of excluded theorem names.
        Returns empty dict if exclusions file does not exist.
    """
    return _load_contract_name_sets(EXCLUSIONS, missing_ok=True)


def extract_lean_import_modules(line: str) -> list[str]:
    """Extract imported module names from a Lean `import` line.

    Supports multiple modules on one line and ignores `as Alias` clauses.
    Returns an empty list for non-import lines.
    """
    match = LEAN_IMPORT_RE.match(line)
    if match is None:
        return []

    modules: list[str] = []
    tokens = match.group("body").split()
    skip_alias = False
    for token in tokens:
        if skip_alias:
            skip_alias = False
            continue
        if token == "as":
            skip_alias = True
            continue
        if LEAN_MODULE_NAME_RE.fullmatch(token):
            modules.append(token)
    return modules


def _load_contract_name_sets(path: Path, *, missing_ok: bool) -> dict[str, set[str]]:
    """Load and validate a `{contract: [name, ...]}` JSON object."""
    if not path.exists():
        if missing_ok:
            return {}
        raise SystemExit(f"Missing property manifest: {path}")

    try:
        raw: object = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=_reject_duplicate_object_keys,
        )
    except (json.JSONDecodeError, ValueError) as exc:
        raise SystemExit(f"Invalid JSON in {path}: {exc}") from exc

    if not isinstance(raw, dict):
        raise SystemExit(
            f"Invalid schema in {path}: expected top-level object "
            "mapping contract names to string arrays."
        )

    validated: dict[str, set[str]] = {}
    for contract, names in raw.items():
        if not isinstance(contract, str) or not contract:
            raise SystemExit(
                f"Invalid schema in {path}: contract key {contract!r} must be a non-empty string."
            )
        if contract != contract.strip() or not CONTRACT_NAME_RE.fullmatch(contract):
            raise SystemExit(
                f"Invalid schema in {path}: contract key {contract!r} must match {CONTRACT_NAME_RE.pattern!r}."
            )
        if not isinstance(names, list):
            raise SystemExit(
                f"Invalid schema in {path}: value for {contract!r} must be an array of strings."
            )
        for name in names:
            if not isinstance(name, str) or not name:
                raise SystemExit(
                    f"Invalid schema in {path}: entry {name!r} in {contract!r} must be a non-empty string."
                )
            _require_theorem_identifier(name, path, context=f"contract {contract!r}")
        duplicate_names = _find_duplicates(names)
        if duplicate_names:
            raise SystemExit(
                f"Invalid schema in {path}: value for {contract!r} contains duplicate name(s): {', '.join(duplicate_names)}."
            )
        validated[contract] = set(names)

    return validated


def _reject_duplicate_object_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    """Reject JSON objects with duplicate keys."""
    seen: set[str] = set()
    duplicates: list[str] = []
    out: dict[str, object] = {}
    for key, value in pairs:
        if key in seen:
            duplicates.append(repr(key))
        else:
            seen.add(key)
        out[key] = value
    if duplicates:
        raise ValueError(f"duplicate object key(s): {', '.join(sorted(set(duplicates)))}")
    return out


def _find_duplicates(items: list[str]) -> list[str]:
    """Return sorted duplicate values in insertion-insensitive order."""
    seen: set[str] = set()
    duplicates: set[str] = set()
    for item in items:
        if item in seen:
            duplicates.add(item)
        else:
            seen.add(item)
    return sorted(duplicates)


def extract_property_names(path: Path) -> list[str]:
    """Extract property theorem names from a Solidity test file.

    Parses comments like:
    - /// Property 1: theorem_name
    - /// Property: theorem_name

    Args:
        path: Path to Solidity test file.

    Returns:
        List of theorem names found in property tags.
    """
    text = path.read_text(encoding="utf-8")
    names: list[str] = []
    for line in text.splitlines():
        match = PROPERTY_WITH_NUM_RE.search(line)
        if match:
            names.append(_require_theorem_identifier(match.group(1), path))
            continue
        match = PROPERTY_SIMPLE_RE.search(line)
        if match:
            names.append(_require_theorem_identifier(match.group(1), path))
    return names


def collect_covered() -> dict[str, set[str]]:
    """Collect all property tests from test directory.

    Scans Property*.t.sol files and extracts property tags.

    Returns:
        Dictionary mapping contract names to sets of covered theorem names.
    """
    covered: dict[str, set[str]] = {}
    for path in sorted(TEST_DIR.glob("Property*.t.sol")):
        match = FILE_RE.match(path.name)
        if not match:
            continue
        contract = _require_contract_identifier(match.group(1), path)
        covered.setdefault(contract, set()).update(extract_property_names(path))
    return covered


def _is_helper_declaration(attrs: str, visibility: str) -> bool:
    """Return True for declarations intentionally excluded from manifest coverage.

    The property manifest tracks externally-audited contract properties, not local
    helper lemmas. We treat `private`/`protected` declarations and declarations
    tagged with `simp` as helper-only by default.
    """
    if visibility.strip():
        return True
    # Keep this simple and conservative: if any attribute block mentions simp,
    # treat the theorem as a helper declaration for manifest purposes.
    return bool(re.search(r"@\[[^\]]*\bsimp\b[^\]]*\]", attrs))


def collect_theorems(path: Path, *, include_helpers: bool = False) -> list[str]:
    """Extract theorem/lemma names from a Lean proof file.

    Args:
        path: Path to Lean file.

    Returns:
        List of theorem/lemma names found in the file.
        By default helper declarations (`private`/`protected` and `@[simp]`)
        are excluded to preserve property-manifest semantics.
    """
    names: list[str] = []
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise SystemExit(f"Cannot read Lean proof file {path}: {exc}") from exc
    stripped = strip_lean_comments(text)
    for line in stripped.splitlines():
        match = THEOREM_RE.match(line)
        if match:
            attrs = match.group("attrs")
            visibility = match.group("visibility")
            if not include_helpers and _is_helper_declaration(attrs, visibility):
                continue
            names.append(_require_theorem_identifier(match.group("name"), path))
    return names


def extract_manifest_from_proofs() -> dict[str, list[str]]:
    """Extract theorem names from Lean proof files.

    Scans Contracts/<Contract>/Proofs/ directories and Contracts/<Contract>/<Contract>.lean
    files that contain inline theorems (e.g., ReentrancyExample).

    Returns:
        Dictionary mapping contract names to sorted, deduplicated lists of theorem names.
    """
    if not PROOFS_DIR.exists():
        raise SystemExit(f"Missing contracts dir: {PROOFS_DIR}")
    manifest: dict[str, list[str]] = {}
    for contract_dir in sorted(PROOFS_DIR.iterdir()):
        if not contract_dir.is_dir():
            continue
        contract = _require_contract_identifier(contract_dir.name, contract_dir)
        proofs_subdir = contract_dir / "Proofs"
        if proofs_subdir.is_dir():
            theorems: list[str] = []
            for lean in sorted(proofs_subdir.rglob("*.lean")):
                theorems.extend(collect_theorems(lean))
            if theorems:
                manifest[contract] = sorted(dict.fromkeys(theorems))

    # Also scan Contracts/<Contract>/<Contract>.lean for contracts with inline theorems (no separate Proofs dir)
    if EXAMPLES_DIR.exists():
        for contract_dir in sorted(EXAMPLES_DIR.iterdir()):
            if not contract_dir.is_dir():
                continue
            contract = _require_contract_identifier(contract_dir.name, contract_dir)
            if contract in manifest:
                continue  # Already found via Proofs/
            contract_lean = contract_dir / f"{contract}.lean"
            if not contract_lean.exists():
                contract_lean = contract_dir / "Contract.lean"
            if contract_lean.exists():
                theorems = collect_theorems(contract_lean)
                if theorems:
                    manifest[contract] = sorted(dict.fromkeys(theorems))

    return manifest


def die(msg: str) -> None:
    """Print error message and exit with status 1.

    Args:
        msg: Error message to print.
    """
    print(f"error: {msg}", file=sys.stderr)
    raise SystemExit(1)


def report_errors(errors: list[str], message: str) -> None:
    """Print error list to stderr and exit with code 1.

    Args:
        errors: List of error messages to report.
        message: Header message to print before error list.
    """
    if errors:
        print(f"{message}:", file=sys.stderr)
        for item in errors:
            print(f"  - {item}", file=sys.stderr)
        raise SystemExit(1)


def strip_lean_comments(text: str) -> str:
    """Strip Lean line/block comments while preserving line structure.

    This parser is string-aware, so comment markers that appear inside Lean
    string literals are preserved as code.
    """
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False
    raw_string_hashes: int | None = None

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if raw_string_hashes is not None:
            out.append(ch)
            if ch == '"':
                j = i + 1
                hashes = 0
                while j < n and text[j] == "#" and hashes < raw_string_hashes:
                    hashes += 1
                    j += 1
                if hashes == raw_string_hashes:
                    out.extend("#" * hashes)
                    i = j
                    raw_string_hashes = None
                    continue
            i += 1
            continue

        if in_string:
            out.append(ch)
            # Preserve escape sequences inside string literals.
            if ch == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue

        if block_depth == 0 and ch == '"':
            in_string = True
            out.append(ch)
            i += 1
            continue

        # Lean raw string literal: r"...", r#"..."#, r##"..."##, ...
        if block_depth == 0 and ch == "r":
            j = i + 1
            hashes = 0
            while j < n and text[j] == "#":
                hashes += 1
                j += 1
            if j < n and text[j] == '"':
                out.append("r")
                out.extend("#" * hashes)
                out.append('"')
                i = j + 1
                raw_string_hashes = hashes
                continue

        # Start of nested block comment: /- ... -/
        if ch == "/" and nxt == "-":
            block_depth += 1
            out.extend("  ")
            i += 2
            continue

        # End of nested block comment.
        if block_depth > 0 and ch == "-" and nxt == "/":
            block_depth -= 1
            out.extend("  ")
            i += 2
            continue

        # Inside block comment: preserve newlines, blank everything else.
        if block_depth > 0:
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        # Line comment: -- ... (to end of line).
        if ch == "-" and nxt == "-":
            out.extend("  ")
            i += 2
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def _strip_lean_strings(text: str) -> str:
    """Replace string literal contents with spaces, preserving line structure."""
    out: list[str] = []
    i = 0
    n = len(text)
    in_string = False
    raw_hashes: int | None = None

    while i < n:
        ch = text[i]

        if raw_hashes is not None:
            if ch == "\n":
                out.append("\n")
                i += 1
                continue
            if ch == '"':
                j = i + 1
                hashes = 0
                while j < n and text[j] == "#" and hashes < raw_hashes:
                    hashes += 1
                    j += 1
                if hashes == raw_hashes:
                    out.append('"')
                    out.extend("#" * hashes)
                    i = j
                    raw_hashes = None
                    continue
            out.append(" ")
            i += 1
            continue

        if in_string:
            if ch == "\n":
                out.append("\n")
                i += 1
                continue
            if ch == "\\" and i + 1 < n:
                out.extend([" ", " "])
                i += 2
                continue
            if ch == '"':
                out.append('"')
                in_string = False
                i += 1
                continue
            out.append(" ")
            i += 1
            continue

        if ch == '"':
            out.append('"')
            in_string = True
            i += 1
            continue

        if ch == "r":
            j = i + 1
            hashes = 0
            while j < n and text[j] == "#":
                hashes += 1
                j += 1
            if j < n and text[j] == '"':
                out.append("r")
                out.extend("#" * hashes)
                out.append('"')
                i = j + 1
                raw_hashes = hashes
                continue

        out.append(ch)
        i += 1

    return "".join(out)


def scrub_lean_code(text: str) -> str:
    """Remove comments and string literal contents from Lean source text."""
    return _strip_lean_strings(strip_lean_comments(text))
