#!/usr/bin/env python3
"""Keep Layer 2 docs aligned with the machine-readable boundary catalog."""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CATALOG = ROOT / "artifacts" / "layer2_boundary_catalog.json"
TARGET_FILES = {
    "GENERIC_PLAN": ROOT / "docs" / "GENERIC_LAYER2_PLAN.md",
    "ROADMAP": ROOT / "docs" / "ROADMAP.md",
    "VERIFICATION_STATUS": ROOT / "docs" / "VERIFICATION_STATUS.md",
    "COMPILER_PROOFS_README": ROOT / "Compiler" / "Proofs" / "README.md",
}


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def load_catalog(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def validate_catalog(catalog: dict) -> None:
    target = catalog.get("theorem_target", {})
    if target.get("intended_claim") != "proof_complete_macro_lowered_verity_contract_image":
        raise ValueError("unexpected theorem target claim in Layer 2 boundary catalog")
    if target.get("excludes_arbitrary_lean_compilation_models") is not True:
        raise ValueError("Layer 2 boundary catalog must exclude arbitrary Lean-produced models")

    helper = catalog.get("supported_spec_split", {}).get("helper_boundary", {})
    if helper.get("current_fail_closed_gate") != "SupportedBodyInterface.stmtList":
        raise ValueError("Layer 2 boundary catalog is missing the helper fail-closed gate")
    if not helper.get("blocking_seams"):
        raise ValueError("Layer 2 boundary catalog is missing helper blocking seams")


def expected_snippets(catalog: dict) -> dict[str, list[str]]:
    helper = catalog["supported_spec_split"]["helper_boundary"]
    theorem_target = catalog["theorem_target"]
    assert theorem_target["intended_claim"] == "proof_complete_macro_lowered_verity_contract_image"
    assert helper["current_fail_closed_gate"] == "SupportedBodyInterface.stmtList"
    return {
        "GENERIC_PLAN": [
            "`artifacts/layer2_boundary_catalog.json`",
            "proof-complete `CompilationModel` subset",
            "macro-lowered image of `verity_contract`",
            "helper-free `SupportedStmtList` witness",
            "`SupportedFunctionBodyWithHelpersIRPreservationGoal`",
            "`SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal`",
            "legacy-compatible external-body Yul subset",
            "`InterpretIRWithInternalsZeroConservativeExtensionGoal`",
            "`InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal`",
            "`interpretIRWithInternalsZeroConservativeExtensionGoal_of_dispatchGoal`",
            "`InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals`",
            "`interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtSubgoals`",
            "`interpretIRWithInternalsZeroConservativeExtensionGoal_closed`",
            "`compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal`",
            "`compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed`",
            "total fuel-indexed helper-aware IR semantics",
            "`exprStmtUsesDedicatedBuiltinSemantics`",
            "direct helper-free lemmas for `stop`, `mstore`, `revert`, `return`, and mapping-slot `sstore`",
            "helper-free conservative-extension goal is now closed",
        ],
        "ROADMAP": [
            "`artifacts/layer2_boundary_catalog.json`",
            "macro-lowered `verity_contract` image",
            "`SupportedStmtList.helperSurfaceClosed`",
            "`SupportedFunctionBodyWithHelpersIRPreservationGoal`",
            "`SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal`",
            "`execIRFunctionWithInternals` / `interpretIRWithInternals`",
            "conservative extension of `interpretIR`",
            "`InterpretIRWithInternalsZeroConservativeExtensionGoal`",
            "`InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal`",
            "`interpretIRWithInternalsZeroConservativeExtensionGoal_of_dispatchGoal`",
            "`InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals`",
            "`interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtSubgoals`",
            "`interpretIRWithInternalsZeroConservativeExtensionGoal_closed`",
            "`compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal`",
            "`compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed`",
            "total fuel-indexed helper-aware IR semantics",
            "`exprStmtUsesDedicatedBuiltinSemantics`",
            "direct helper-free lemmas for `stop`, `mstore`, `revert`, `return`, and mapping-slot `sstore`",
            "helper-free conservative-extension goal is now closed",
            "[#1638]",
        ],
        "VERIFICATION_STATUS": [
            "`artifacts/layer2_boundary_catalog.json`",
            "macro-lowered image of `verity_contract`",
            "`SupportedBodyInterface.stmtList` gate",
            "`SupportedFunctionBodyWithHelpersIRPreservationGoal`",
            "`SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal`",
            "helper-aware body theorem does not yet consume helper-summary soundness/rank evidence",
            "legacy-compatible external-body Yul subset",
            "`InterpretIRWithInternalsZeroConservativeExtensionGoal`",
            "`InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal`",
            "`interpretIRWithInternalsZeroConservativeExtensionGoal_of_dispatchGoal`",
            "`InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals`",
            "`interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtSubgoals`",
            "`interpretIRWithInternalsZeroConservativeExtensionGoal_closed`",
            "`compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal`",
            "`compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed`",
            "total fuel-indexed helper-aware IR semantics",
            "`exprStmtUsesDedicatedBuiltinSemantics`",
            "direct helper-free lemmas for `stop`, `mstore`, `revert`, `return`, and mapping-slot `sstore`",
            "helper-free conservative-extension goal is now closed",
            "[#1638]",
        ],
        "COMPILER_PROOFS_README": [
            "`artifacts/layer2_boundary_catalog.json`",
            "`SupportedSpec` split",
            "`calls.helpers`",
            "summary-soundness evidence",
            "`SupportedFunctionBodyWithHelpersIRPreservationGoal`",
            "`SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal`",
            "legacy-compatible external-body Yul subset",
            "`InterpretIRWithInternalsZeroConservativeExtensionGoal`",
            "`InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal`",
            "`interpretIRWithInternalsZeroConservativeExtensionGoal_of_dispatchGoal`",
            "`InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals`",
            "`interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtSubgoals`",
            "`interpretIRWithInternalsZeroConservativeExtensionGoal_closed`",
            "`compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal`",
            "`compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed`",
            "total fuel-indexed helper-aware IR semantics",
            "`exprStmtUsesDedicatedBuiltinSemantics`",
            "direct helper-free lemmas for `stop`, `mstore`, `revert`, `return`, and mapping-slot `sstore`",
            "helper-free conservative-extension goal is now closed",
            "[#1638]",
        ],
    }


def main() -> int:
    if not CATALOG.exists():
        print(f"Missing: {CATALOG.relative_to(ROOT)}", file=sys.stderr)
        return 1

    try:
        catalog = load_catalog(CATALOG)
        validate_catalog(catalog)
    except (json.JSONDecodeError, ValueError) as exc:
        print(f"{CATALOG.relative_to(ROOT)}: {exc}", file=sys.stderr)
        return 1

    errors: list[str] = []
    expected = expected_snippets(catalog)
    for label, path in TARGET_FILES.items():
        if not path.exists():
            errors.append(f"Missing: {path.relative_to(ROOT)}")
            continue
        normalized = normalize_ws(path.read_text(encoding="utf-8"))
        for snippet in expected[label]:
            if normalize_ws(snippet) not in normalized:
                errors.append(
                    f"{path.relative_to(ROOT)} is out of sync with the Layer 2 boundary catalog: missing `{snippet}`"
                )

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    print("layer2 boundary catalog sync passed: docs reference the machine-readable Layer 2 boundary")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
