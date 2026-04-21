#!/usr/bin/env python3
"""Enforce EVMYulLean capability boundary for reference-oracle Yul builtins.

Issue #294 tracks replacing hand-rolled semantics with EVMYulLean. This check
keeps `Compiler/Proofs/YulGeneration/ReferenceOracle/Builtins.lean` within an explicitly
supported builtin surface so migration cannot silently expand into unsupported
operations.
"""

from __future__ import annotations

import sys

from evmyullean_capability import (
    BUILTINS_FILE,
    EVMYULLEAN_OVERLAP_BUILTINS,
    EVMYULLEAN_UNSUPPORTED_BUILTINS,
    VERITY_HELPER_BUILTINS,
    extract_found_builtins_with_diagnostics,
)
from property_utils import ROOT


def main() -> int:
    if not BUILTINS_FILE.exists():
        print(
            f"EVMYulLean capability boundary check failed: missing {BUILTINS_FILE.relative_to(ROOT)}",
            file=sys.stderr,
        )
        return 1

    found, diagnostics = extract_found_builtins_with_diagnostics(BUILTINS_FILE)

    allowed = EVMYULLEAN_OVERLAP_BUILTINS | VERITY_HELPER_BUILTINS

    errors: list[str] = []

    unsupported_present = sorted(found & EVMYULLEAN_UNSUPPORTED_BUILTINS)
    if unsupported_present:
        errors.append(
            "contains EVMYulLean-unsupported builtins: " + ", ".join(unsupported_present)
        )

    unknown = sorted(found - allowed)
    if unknown:
        errors.append(
            "introduces builtins outside capability boundary: " + ", ".join(unknown)
        )
    if diagnostics:
        errors.append(
            "uses non-literal builtin dispatch patterns (fail-closed): "
            + "; ".join(diagnostics)
        )

    if errors:
        print("EVMYulLean capability boundary check failed:", file=sys.stderr)
        print(f"  - file: {BUILTINS_FILE.relative_to(ROOT)}", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        print(
            "  - action: keep unsupported builtins in legacy fallback semantics, "
            "or update #294 capability matrix with proof/test justification",
            file=sys.stderr,
        )
        return 1

    print("✓ EVMYulLean capability boundary is enforced")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
