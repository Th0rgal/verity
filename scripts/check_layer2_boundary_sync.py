#!/usr/bin/env python3
"""Keep Layer 2 proof-boundary claims aligned across docs surfaces."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    "COMPILER_PROOFS_README": ROOT / "Compiler" / "Proofs" / "README.md",
    "GENERIC_PLAN": ROOT / "docs" / "GENERIC_LAYER2_PLAN.md",
    "VERIFICATION_STATUS": ROOT / "docs" / "VERIFICATION_STATUS.md",
    "ROADMAP": ROOT / "docs" / "ROADMAP.md",
    "ROOT_README": ROOT / "README.md",
    "TRUST_ASSUMPTIONS": ROOT / "TRUST_ASSUMPTIONS.md",
    "SEMANTIC_BRIDGE": ROOT / "Contracts" / "Proofs" / "SemanticBridge.lean",
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
            "it still depends on 1 documented axiom in `Compiler.Proofs.IRGeneration.Function`",
        ],
        "GENERIC_PLAN": [
            "avoid any `post`/`hpost`/contract-specific bridge premise",
            "`Contracts/Proofs/SemanticBridge.lean` becomes client/example layer only.",
        ],
        "VERIFICATION_STATUS": [
            "## Layer 2: CompilationModel → IR — PARTIAL GENERIC",
            "there is not yet a single compiler-level theorem quantified over arbitrary supported `CompilationModel` programs and successful `CompilationModel.compile` output.",
            "it still depends on 1 documented Layer-2 axiom in [`Function.lean`](../Compiler/Proofs/IRGeneration/Function.lean)",
            "Still axiomatized: generic supported body simulation",
        ],
        "ROADMAP": [
            "🟡 **Layer 2 Partial Generic**",
            "generic whole-contract `CompilationModel.compile` theorem is still tracked in [#1510]",
        ],
        "ROOT_README": [
            "Layer 2: CompilationModel → IR        [PARTIAL GENERIC, CONTRACT BRIDGES ACTIVE]",
            "Layer 2 currently combines a generic supported-statement theorem with contract-specific full-contract bridges.",
            "its non-core function-level closure still depends on 1 documented axiom",
            "There are currently 2 documented Lean axioms in total: 1 selector axiom and 1 generic non-core Layer 2 axiom.",
            "Layer 3 keeps its remaining dispatch bridge as an explicit theorem hypothesis rather than a Lean axiom.",
        ],
        "TRUST_ASSUMPTIONS": [
            "Layer 2: PARTIAL GENERIC — CompilationModel → IR + contract bridges",
            "whole-contract Layer 2 preservation still relies on contract-specific bridge theorems.",
            "The theorem surface still depends on 1 documented sub-axiom for generic body simulation",
            "it still has 2 documented Lean axioms",
        ],
        "SEMANTIC_BRIDGE": [
            "This is not a generic compiler-correctness theorem for `CompilationModel.compile`.",
            "The actual semantic work still lives in the contract-specific bridge theorem passed in as `hpost`.",
        ],
        "DOCS_SITE_COMPILER": [
            "**Layer 2 boundary today**",
            "full-contract Layer 2 preservation still relies on contract-specific bridge theorems.",
            "the remaining non-core closure still depends on 1 documented axiom.",
            "explicit theorem hypothesis rather than a Lean axiom",
        ],
        "DOCS_SITE_RESEARCH": [
            "Partial generic coverage only.",
            "generic `CompilationModel.compile` theorem is tracked in [#1510]",
            "`Contracts/Proofs/SemanticBridge.lean`",
            "`Compiler/Proofs/IRGeneration/Contract.lean`",
        ],
        "LLMS": [
            "partial generic CompilationModel -> IR boundary",
            "generic supported-statement theorem plus contract-specific full-contract bridges.",
            "2 documented Lean axioms",
        ],
    }


def forbidden_snippets() -> dict[str, list[str]]:
    return {
        "COMPILER_PROOFS_README": [
            "it still depends on 2 documented axioms in `Compiler.Proofs.IRGeneration.Function`",
            "generic body simulation and `execIRFunctionFuel`/`execIRFunction` bridging",
        ],
        "VERIFICATION_STATUS": [
            "## Layer 2: CompilationModel → IR — COMPLETE",
            "it still depends on 2 documented Layer-2 axioms",
            "Still axiomatized: generic supported body simulation and the `execIRFunctionFuel` to `execIRFunction` bridge",
        ],
        "GENERIC_PLAN": [
            "use the old `hpost`-based bridge theorem as the solution",
        ],
        "ROADMAP": [
            "✅ **Layer 2 Complete**",
        ],
        "ROOT_README": [
            "Layer 2: CompilationModel → IR        [PROVEN]",
            "| 2 | CompilationModel → IR preserves behavior |",
            "depends on 2 documented axioms",
            "documented bridge axiom",
            "There are currently 3 documented Lean axioms in total",
            "There are currently 4 documented Lean axioms in total",
        ],
        "TRUST_ASSUMPTIONS": [
            "FULLY VERIFIED — CompilationModel → IR",
            "All three layers are proven in Lean",
            "2 documented sub-axioms for generic body simulation and the `execIRFunctionFuel`/`execIRFunction` bridge",
            "3 documented Lean axioms",
            "4 documented Lean axioms",
            "1 documented bridge axiom",
        ],
        "SEMANTIC_BRIDGE": [
            "proofs use placeholders until",
        ],
        "DOCS_SITE_COMPILER": [
            "**Layer 2 framework proof**: `CompilationModel -> IR` preserves semantics.",
            "depends on 2 documented axioms.",
            "1 documented bridge axiom",
        ],
        "DOCS_SITE_RESEARCH": [
            "Complete for all 7 contracts",
            "`Verity/Examples/X.lean`",
            "`Compiler/TypedIRCompilerCorrectness.lean` — Compilation correctness (generic theorem, 36 supported fragments)",
        ],
        "LLMS": [
            "CompilationModel -> IR preservation",
            "3 documented axioms",
            "4 documented axioms",
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
