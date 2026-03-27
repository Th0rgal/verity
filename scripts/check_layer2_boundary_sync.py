#!/usr/bin/env python3
"""Keep Layer 2 proof-boundary claims aligned across docs surfaces."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    "AXIOMS": ROOT / "AXIOMS.md",
    "COMPILER_PROOFS_README": ROOT / "Compiler" / "Proofs" / "README.md",
    "GENERIC_PLAN": ROOT / "docs" / "GENERIC_LAYER2_PLAN.md",
    "VERIFICATION_STATUS": ROOT / "docs" / "VERIFICATION_STATUS.md",
    "ROADMAP": ROOT / "docs" / "ROADMAP.md",
    "ROOT_README": ROOT / "README.md",
    "TRUST_ASSUMPTIONS": ROOT / "TRUST_ASSUMPTIONS.md",
    "DOCS_SITE_COMPILER": ROOT / "docs-site" / "content" / "compiler.mdx",
    "DOCS_SITE_INDEX": ROOT / "docs-site" / "content" / "index.mdx",
    "DOCS_SITE_EXAMPLES": ROOT / "docs-site" / "content" / "examples.mdx",
    "DOCS_SITE_FIRST_CONTRACT": ROOT / "docs-site" / "content" / "guides" / "first-contract.mdx",
    "DOCS_SITE_VERIFICATION": ROOT / "docs-site" / "content" / "verification.mdx",
    "DOCS_SITE_RESEARCH": ROOT / "docs-site" / "content" / "research.mdx",
    "LLMS": ROOT / "docs-site" / "public" / "llms.txt",
}


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def expected_snippets() -> dict[str, list[str]]:
    return {
        "AXIOMS": [
            "### 1. `keccak256_first_4_bytes`",
            "- Active axioms: 3",
        ],
        "COMPILER_PROOFS_README": [
            "`Compiler.Proofs.IRGeneration.Contract.compile_preserves_semantics`",
            "The former exact-state body-simulation axiom in `Compiler.Proofs.IRGeneration.Function` has now been eliminated",
        ],
        "GENERIC_PLAN": [
            "avoid any `post`/`hpost`/contract-specific bridge premise",
            "The main objective of issue #1618 is therefore complete.",
        ],
        "VERIFICATION_STATUS": [
            "## Layer 2: CompilationModel → IR — GENERIC WHOLE-CONTRACT THEOREM",
            "a whole-contract theorem surface, [`compile_preserves_semantics`](../Compiler/Proofs/IRGeneration/Contract.lean), quantified over arbitrary supported `CompilationModel`s",
            "What is not fully migrated yet",
            "No Lean axioms remain in Layer 2",
        ],
        "ROADMAP": [
            "🟢 **Layer 2 Generic Theorem**",
            "generic whole-contract `CompilationModel.compile` theorem is proved for the current supported fragment",
        ],
        "ROOT_README": [
            "Layer 2: CompilationModel → IR        [GENERIC WHOLE-CONTRACT THEOREM]",
            "Layer 2 now has a generic whole-contract theorem for the explicit supported fragment.",
            "its function-level closure now runs by theorem rather than axiom",
            "There are currently 3 documented Lean axioms in total: the selector axiom and 2 mapping-slot range axioms.",
            "Layer 3 keeps its remaining dispatch bridge as an explicit theorem hypothesis rather than a Lean axiom.",
        ],
        "TRUST_ASSUMPTIONS": [
            "Layer 2: SUPPORTED-FRAGMENT GENERIC THEOREM — CompilationModel → IR",
            "A generic whole-contract theorem is proved for the current supported `CompilationModel` fragment.",
            "former generic body-simulation axiom has been eliminated",
            "it now has 3 documented Lean axioms",
            "explicit theorem hypothesis rather than a Lean axiom",
        ],
        "DOCS_SITE_COMPILER": [
            "**Layer 2 boundary today**",
            "the generic whole-contract `CompilationModel -> IR` theorem is proved for the current explicit supported fragment.",
            "former exact-state body-simulation axiom has been eliminated",
            "explicit theorem hypothesis rather than a Lean axiom",
        ],
        "DOCS_SITE_INDEX": [
            "`Compiler/Proofs/IRGeneration/Contract.lean` (generic whole-contract `CompilationModel -> IR` theorem for the current supported fragment)",
        ],
        "DOCS_SITE_EXAMPLES": [
            "`Compiler/Proofs/IRGeneration/Contract.lean` for the current supported fragment",
        ],
        "DOCS_SITE_FIRST_CONTRACT": [
            "the compiler-level `CompilationModel -> IR` result now lives in `Compiler/Proofs/IRGeneration/Contract.lean`",
        ],
        "DOCS_SITE_VERIFICATION": [
            "**Generic whole-contract Layer 2 theorem**: `Compiler/Proofs/IRGeneration/Contract.lean`",
        ],
        "DOCS_SITE_RESEARCH": [
            "Supported-fragment generic theorem in place.",
            "`Compiler/Proofs/IRGeneration/Contract.lean`",
        ],
        "LLMS": [
            "generic whole-contract CompilationModel -> IR theorem for the supported fragment",
            "3 documented Lean axioms",
        ],
    }


def forbidden_snippets() -> dict[str, list[str]]:
    return {
        "COMPILER_PROOFS_README": [
            "it still depends on 2 documented axioms in `Compiler.Proofs.IRGeneration.Function`",
            "generic body simulation and `execIRFunctionFuel`/`execIRFunction` bridging",
        ],
        "AXIOMS": [
            "### 2. `supported_function_body_correct_from_exact_state`",
            "supported_function_body_correct_from_exact_state",
            "- Active axioms: 2",
        ],
        "VERIFICATION_STATUS": [
            "## Layer 2: CompilationModel → IR — COMPLETE",
            "it still depends on 2 documented Layer-2 axioms",
            "Still axiomatized: generic supported body simulation and the `execIRFunctionFuel` to `execIRFunction` bridge",
            "PARTIAL GENERIC, 2 AXIOMS, CONTRACT BRIDGES ACTIVE",
            "there is not yet a single compiler-level theorem quantified over arbitrary supported `CompilationModel` programs and successful `CompilationModel.compile` output.",
        ],
        "GENERIC_PLAN": [
            "use the old `hpost`-based bridge theorem as the solution",
        ],
        "ROADMAP": [
            "✅ **Layer 2 Complete**",
            "Layer 2 Partial Generic",
        ],
        "ROOT_README": [
            "Layer 2: CompilationModel → IR        [PROVEN]",
            "| 2 | CompilationModel → IR preserves behavior |",
            "depends on 2 documented axioms",
            "documented bridge axiom",
            "1 generic non-core Layer 2 axiom",
            "There are currently 4 documented Lean axioms in total",
        ],
        "TRUST_ASSUMPTIONS": [
            "FULLY VERIFIED — CompilationModel → IR",
            "All three layers are proven in Lean",
            "2 documented sub-axioms for generic body simulation and the `execIRFunctionFuel`/`execIRFunction` bridge",
            "4 documented Lean axioms",
            "1 documented bridge axiom",
            "2 documented axioms in [AXIOMS.md](AXIOMS.md): 1 selector axiom and 1 generic non-core Layer 2 axiom",
            "Layer 3: GENERIC SURFACE, 1 axiom — IR → Yul",
            "1 Layer 3 dispatch bridge axiom",
        ],
        "DOCS_SITE_COMPILER": [
            "**Layer 2 framework proof**: `CompilationModel -> IR` preserves semantics.",
            "depends on 2 documented axioms.",
            "1 documented bridge axiom",
            "depends on 1 documented axiom",
            "full-contract Layer 2 preservation still relies on contract-specific bridge theorems.",
        ],
        "DOCS_SITE_FIRST_CONTRACT": [
            "18 proof terms currently use `sorry`",
        ],
        "DOCS_SITE_RESEARCH": [
            "Complete for all 7 contracts",
            "`Verity/Examples/X.lean`",
            "`Compiler/TypedIRCompilerCorrectness.lean` — Compilation correctness (generic theorem, 36 supported fragments)",
            "Partial generic coverage only.",
        ],
        "LLMS": [
            "CompilationModel -> IR preservation",
            "3 documented axioms",
            "4 documented axioms",
            "2 documented Lean axioms",
            "partial generic CompilationModel -> IR boundary",
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

    print("layer2 boundary sync passed: generic Layer 2 theorem boundary documented")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
