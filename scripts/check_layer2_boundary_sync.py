#!/usr/bin/env python3
"""Keep Layer 2 proof-boundary claims aligned across docs surfaces."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    "COMPILER_PROOFS_README": ROOT / "Compiler" / "Proofs" / "README.md",
    "VERIFICATION_STATUS": ROOT / "docs" / "VERIFICATION_STATUS.md",
    "ROADMAP": ROOT / "docs" / "ROADMAP.md",
    "ROOT_README": ROOT / "README.md",
    "TRUST_ASSUMPTIONS": ROOT / "TRUST_ASSUMPTIONS.md",
    "DOCS_SITE_COMPILER": ROOT / "docs-site" / "content" / "compiler.mdx",
    "DOCS_SITE_RESEARCH": ROOT / "docs-site" / "content" / "research.mdx",
    "LLMS": ROOT / "docs-site" / "public" / "llms.txt",
}


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def expected_snippets() -> dict[str, list[str]]:
    return {
        "COMPILER_PROOFS_README": [
            "there is not yet a single generic theorem saying `CompilationModel.compile` preserves semantics for every supported full contract.",
            "`Contracts/Proofs/SemanticBridge.lean`: contract-level bridge theorems",
        ],
        "VERIFICATION_STATUS": [
            "## Layer 2: CompilationModel → IR — PARTIAL GENERIC",
            "there is not yet a single compiler-level theorem quantified over arbitrary supported `CompilationModel` programs and successful `CompilationModel.compile` output.",
        ],
        "ROADMAP": [
            "🟡 **Layer 2 Partial Generic**",
            "generic whole-contract `CompilationModel.compile` theorem is still tracked in [#1510]",
        ],
        "ROOT_README": [
            "Layer 2: CompilationModel → IR        [PARTIAL GENERIC, CONTRACT BRIDGES ACTIVE]",
            "Layer 2 currently combines a generic supported-statement theorem with contract-specific full-contract bridges.",
        ],
        "TRUST_ASSUMPTIONS": [
            "Layer 2: PARTIAL GENERIC — CompilationModel → IR + contract bridges",
            "whole-contract Layer 2 preservation still relies on contract-specific bridge theorems.",
        ],
        "DOCS_SITE_COMPILER": [
            "**Layer 2 boundary today**",
            "full-contract Layer 2 preservation still relies on contract-specific bridge theorems.",
        ],
        "DOCS_SITE_RESEARCH": [
            "Partial generic coverage only.",
            "generic `CompilationModel.compile` theorem is tracked in [#1510]",
        ],
        "LLMS": [
            "partial generic CompilationModel -> IR boundary",
            "generic supported-statement theorem plus contract-specific full-contract bridges.",
        ],
    }


def forbidden_snippets() -> dict[str, list[str]]:
    return {
        "VERIFICATION_STATUS": [
            "## Layer 2: CompilationModel → IR — COMPLETE",
        ],
        "ROADMAP": [
            "✅ **Layer 2 Complete**",
        ],
        "ROOT_README": [
            "Layer 2: CompilationModel → IR        [PROVEN]",
            "| 2 | CompilationModel → IR preserves behavior |",
        ],
        "TRUST_ASSUMPTIONS": [
            "FULLY VERIFIED — CompilationModel → IR",
            "All three layers are proven in Lean",
        ],
        "DOCS_SITE_COMPILER": [
            "**Layer 2 framework proof**: `CompilationModel -> IR` preserves semantics.",
        ],
        "DOCS_SITE_RESEARCH": [
            "Complete for all 7 contracts",
        ],
        "LLMS": [
            "CompilationModel -> IR preservation",
        ],
    }


def main() -> int:
    errors: list[str] = []
    required = expected_snippets()
    forbidden = forbidden_snippets()

    for label, path in TARGETS.items():
        if not path.exists():
            errors.append(f"Missing: {path.relative_to(ROOT)}")
            continue
        normalized = normalize_ws(path.read_text(encoding="utf-8"))
        for snippet in required.get(label, []):
            if normalize_ws(snippet) not in normalized:
                errors.append(
                    f"{path.relative_to(ROOT)} is out of sync with the Layer 2 boundary: missing `{snippet}`"
                )
        for snippet in forbidden.get(label, []):
            if normalize_ws(snippet) in normalized:
                errors.append(
                    f"{path.relative_to(ROOT)} still over-claims the Layer 2 boundary: found forbidden snippet `{snippet}`"
                )

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    print("layer2 boundary sync passed: partial-generic/compiler-bridge split documented")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
