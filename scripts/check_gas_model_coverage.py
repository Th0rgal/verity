#!/usr/bin/env python3
"""Ensure static gas builtin coverage matches generated Yul call sites."""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT

STATIC_ANALYSIS = ROOT / "Compiler" / "Gas" / "StaticAnalysis.lean"
YUL_DIR = ROOT / "compiler" / "yul"

FUNCTION_DEF_RE = re.compile(r"\bfunction\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(")
CALL_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(")
MODELED_CALL_RE = re.compile(r'name\s*=\s*"([A-Za-z_][A-Za-z0-9_]*)"')

NON_CALL_KEYWORDS = {"function", "if", "switch", "object", "code"}


def load_modeled_calls() -> set[str]:
    text = STATIC_ANALYSIS.read_text(encoding="utf-8")
    return set(MODELED_CALL_RE.findall(text))


def strip_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    text = re.sub(r"//.*", "", text)
    return text


def collect_yul_calls() -> set[str]:
    calls: set[str] = set()
    for yul_path in sorted(YUL_DIR.glob("*.yul")):
        source = strip_comments(yul_path.read_text(encoding="utf-8"))
        function_names = set(FUNCTION_DEF_RE.findall(source))
        for line in source.splitlines():
            clean = line.strip()
            for match in CALL_RE.finditer(clean):
                name = match.group(1)
                if name in NON_CALL_KEYWORDS or name in function_names:
                    continue
                calls.add(name)
    return calls


def main() -> int:
    if not STATIC_ANALYSIS.exists():
        print(f"ERROR: missing {STATIC_ANALYSIS}", file=sys.stderr)
        return 1
    if not YUL_DIR.exists():
        print(f"ERROR: missing {YUL_DIR}", file=sys.stderr)
        return 1

    modeled = load_modeled_calls()
    emitted = collect_yul_calls()

    missing = sorted(emitted - modeled)
    if missing:
        print("ERROR: Static gas model is missing emitted Yul calls:", file=sys.stderr)
        for name in missing:
            print(f"  - {name}", file=sys.stderr)
        return 1

    print(f"OK: static gas model covers all emitted Yul calls ({len(emitted)} names)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
