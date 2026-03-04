#!/usr/bin/env python3
"""Fail closed on regressions while migrating proofs to macro-generated artifacts.

Issue #997 tracks proof migration from legacy/manual references:
- `Verity.Examples.{Counter,SimpleStorage,Owned,Ledger,OwnedCounter,SimpleToken,SafeCounter}`
- `Compiler.Specs.*Spec` (legacy manual specs)

This check enforces:
1) No legacy references may appear outside the explicit temporary allowlist.
2) Allowlisted files must still contain at least one legacy reference (stale entries fail).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT, scrub_lean_code

PROOF_ROOTS = [
    ROOT / "Compiler" / "Proofs",
    ROOT / "Verity" / "Proofs",
]

ALLOWLIST = {
    Path("Compiler/Proofs/SemanticBridge.lean"),
    Path("Verity/Proofs/Ledger/Basic.lean"),
    Path("Verity/Proofs/Ledger/Conservation.lean"),
    Path("Verity/Proofs/Ledger/Correctness.lean"),
    Path("Verity/Proofs/OwnedCounter/Basic.lean"),
    Path("Verity/Proofs/OwnedCounter/Correctness.lean"),
    Path("Verity/Proofs/OwnedCounter/Isolation.lean"),
    Path("Verity/Proofs/SimpleToken/Basic.lean"),
    Path("Verity/Proofs/SimpleToken/Correctness.lean"),
    Path("Verity/Proofs/SimpleToken/Isolation.lean"),
    Path("Verity/Proofs/SimpleToken/Supply.lean"),
}

LEGACY_RE = re.compile(
    r"\b(?:"
    r"Verity\.Examples\.(?:Counter|SimpleStorage|Owned|Ledger|OwnedCounter|SimpleToken|SafeCounter)"
    r"|Compiler\.Specs\.(?:counterSpec|simpleStorageSpec|ownedSpec|ledgerSpec|ownedCounterSpec|simpleTokenSpec|safeCounterSpec)"
    r")\b"
)


def _proof_files() -> list[Path]:
    files: list[Path] = []
    for root in PROOF_ROOTS:
        files.extend(sorted(root.rglob("*.lean")))
    return files


def _find_legacy_refs(path: Path) -> list[str]:
    text = scrub_lean_code(path.read_text(encoding="utf-8"))
    return [m.group(0) for m in LEGACY_RE.finditer(text)]


def main() -> int:
    files = _proof_files()
    errors: list[str] = []
    found_allowlisted: set[Path] = set()

    for file_path in files:
        rel = file_path.relative_to(ROOT)
        hits = _find_legacy_refs(file_path)
        if not hits:
            continue
        unique_hits = sorted(set(hits))
        if rel not in ALLOWLIST:
            errors.append(
                f"{rel}: unexpected legacy proof reference(s): {', '.join(unique_hits)}"
            )
            continue
        found_allowlisted.add(rel)

    stale_allowlist = sorted(ALLOWLIST - found_allowlisted)
    for stale in stale_allowlist:
        errors.append(
            f"{stale}: stale allowlist entry (no legacy references found; remove from ALLOWLIST)"
        )

    if errors:
        print("Spec-proof migration boundary check failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        print(
            "\nIssue #997 guard: keep legacy references confined to the explicit allowlist and "
            "delete allowlist entries as proofs migrate to MacroContracts artifacts.",
            file=sys.stderr,
        )
        return 1

    print(
        "Spec-proof migration boundary check passed "
        f"({len(ALLOWLIST)} allowlisted files; no out-of-bound legacy references)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
