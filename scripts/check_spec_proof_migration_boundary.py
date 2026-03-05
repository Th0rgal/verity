#!/usr/bin/env python3
"""Fail closed on regressions while migrating proofs to macro-generated artifacts.

Issue #997 tracks proof migration from legacy/manual references:
- `Contracts.{Counter,SimpleStorage,Owned,Ledger,OwnedCounter,SimpleToken}` (was `Verity.Examples.*`)
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
    ROOT / "Contracts",
]

ALLOWLIST: set[Path] = {
    Path("Contracts/Counter/Proofs/Basic.lean"),
    Path("Contracts/Counter/Proofs/Correctness.lean"),
    Path("Contracts/Ledger/Proofs/Basic.lean"),
    Path("Contracts/Ledger/Proofs/Conservation.lean"),
    Path("Contracts/Ledger/Proofs/Correctness.lean"),
    Path("Contracts/Owned/Proofs/Basic.lean"),
    Path("Contracts/Owned/Proofs/Correctness.lean"),
    Path("Contracts/OwnedCounter/Proofs/Basic.lean"),
    Path("Contracts/OwnedCounter/Proofs/Correctness.lean"),
    Path("Contracts/OwnedCounter/Proofs/Isolation.lean"),
    Path("Contracts/SimpleStorage/Proofs/Basic.lean"),
    Path("Contracts/SimpleStorage/Proofs/Correctness.lean"),
    Path("Contracts/SimpleToken/Proofs/Basic.lean"),
    Path("Contracts/SimpleToken/Proofs/Correctness.lean"),
    Path("Contracts/SimpleToken/Proofs/Isolation.lean"),
    Path("Contracts/SimpleToken/Proofs/Supply.lean"),
}

LEGACY_RE = re.compile(
    r"\b(?:"
    r"Contracts\.(?:Counter|SimpleStorage|Owned|Ledger|OwnedCounter|SimpleToken)(?:\.Contract)?"
    r"|Compiler\.Specs\.(?:counterSpec|simpleStorageSpec|ownedSpec|ledgerSpec|ownedCounterSpec|simpleTokenSpec)"
    r")\b"
)


def _proof_files() -> list[Path]:
    files: list[Path] = []
    for root in PROOF_ROOTS:
        if root == ROOT / "Contracts":
            # Scan Contracts/*/Proofs/ directories
            for contract_dir in sorted(root.iterdir()):
                proofs_dir = contract_dir / "Proofs"
                if proofs_dir.is_dir():
                    files.extend(sorted(proofs_dir.rglob("*.lean")))
        else:
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
