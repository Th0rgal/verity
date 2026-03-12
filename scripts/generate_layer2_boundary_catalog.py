#!/usr/bin/env python3
"""Generate artifacts/layer2_boundary_catalog.json."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from property_utils import ROOT


def build_catalog() -> dict:
    return {
        "schema_version": 1,
        "description": (
            "Machine-readable Layer 2 proof-boundary catalog for the generic "
            "CompilationModel -> IR theorem."
        ),
        "theorem_target": {
            "intended_claim": "proof_complete_macro_lowered_verity_contract_image",
            "generic_theorem_domain": "supported_compilation_model_subset",
            "excludes_arbitrary_lean_compilation_models": True,
            "issue_refs": {
                "theorem_shape": 1510,
                "completeness": 1630,
                "helper_ir_semantics": 1638,
            },
            "source_refs": [
                "docs/GENERIC_LAYER2_PLAN.md",
                "docs/ROADMAP.md",
                "docs/VERIFICATION_STATUS.md",
            ],
        },
        "current_theorem": {
            "theorem": "Compiler.Proofs.IRGeneration.Contract.compile_preserves_semantics",
            "helper_proof_ready_variant": (
                "Compiler.Proofs.IRGeneration.Contract."
                "compile_preserves_semantics_with_helper_proofs"
            ),
            "helper_ir_ready_variant": (
                "Compiler.Proofs.IRGeneration.Contract."
                "compile_preserves_semantics_with_helper_proofs_and_helper_ir"
            ),
            "helper_ir_goal_ready_variant": (
                "Compiler.Proofs.IRGeneration.Contract."
                "compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal"
            ),
            "helper_ir_closed_variant": (
                "Compiler.Proofs.IRGeneration.Contract."
                "compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed"
            ),
            "source_semantics": (
                "Compiler.Proofs.IRGeneration.SourceSemantics.supportedSourceContractSemantics"
            ),
            "supported_spec": "Compiler.Proofs.IRGeneration.SupportedSpec",
            "layer2_axioms": [],
            "remaining_global_hypotheses": [
                "CompilationModel.compile spec selectors = Except.ok ir",
                "Function.TxContextNormalized tx",
                "Function.TxCalldataSizeFitsEvm tx",
            ],
            "trusted_boundary_change": "none",
        },
        "supported_spec_split": {
            "global_invariants": [
                {
                    "name": "normalizedFields",
                    "source": "SupportedSpecInvariants.normalizedFields",
                    "kind": "global_precondition",
                },
                {
                    "name": "noPackedFields",
                    "source": "SupportedSpecInvariants.noPackedFields",
                    "kind": "global_precondition",
                },
                {
                    "name": "selectorCount",
                    "source": "SupportedSpecInvariants.selectorCount",
                    "kind": "global_precondition",
                },
                {
                    "name": "selectorsDistinct",
                    "source": "SupportedSpecInvariants.selectorsDistinct",
                    "kind": "global_precondition",
                },
            ],
            "global_surface_exclusions": [
                {
                    "name": "constructor",
                    "source": "SupportedSpecSurface.noConstructor",
                    "kind": "temporary_surface_boundary",
                },
                {
                    "name": "events",
                    "source": "SupportedSpecSurface.noEvents",
                    "kind": "temporary_surface_boundary",
                },
                {
                    "name": "errors",
                    "source": "SupportedSpecSurface.noErrors",
                    "kind": "temporary_surface_boundary",
                },
                {
                    "name": "externals",
                    "source": "SupportedSpecSurface.noExternals",
                    "kind": "temporary_surface_boundary",
                },
                {
                    "name": "fallback",
                    "source": "SupportedSpecSurface.noFallback",
                    "kind": "temporary_surface_boundary",
                },
                {
                    "name": "receive",
                    "source": "SupportedSpecSurface.noReceive",
                    "kind": "temporary_surface_boundary",
                },
            ],
            "function_interfaces": [
                {
                    "name": "params",
                    "source": "SupportedFunction.params",
                    "kind": "feature_local_interface",
                },
                {
                    "name": "returns",
                    "source": "SupportedFunction.returns",
                    "kind": "feature_local_interface",
                },
                {
                    "name": "body",
                    "source": "SupportedFunction.body",
                    "kind": "feature_local_interface",
                },
            ],
            "body_interfaces": [
                {
                    "name": "core",
                    "source": "SupportedBodyCoreInterface.surfaceClosed",
                    "kind": "feature_local_interface",
                },
                {
                    "name": "state",
                    "source": "SupportedBodyStateInterface.surfaceClosed",
                    "kind": "feature_local_interface",
                },
                {
                    "name": "calls",
                    "source": "SupportedBodyCallInterface",
                    "kind": "feature_local_interface",
                },
                {
                    "name": "effects",
                    "source": "SupportedBodyEffectInterface.surfaceClosed",
                    "kind": "feature_local_interface",
                },
            ],
            "helper_boundary": {
                "inventory_source": "SupportedBodyHelperInterface.summaryOf",
                "proof_contract": "InternalHelperSummaryContract",
                "proof_soundness_slot": "SupportedSpecHelperProofs",
                "compiled_side_blocker_issue": 1638,
                "compiled_target_compatibility_subset": {
                    "name": "legacy_compatible_external_body_yul_subset",
                    "status": "helper_free_conservative_extension_goal_closed",
                    "remaining_stmt_compatibility_surface": [],
                    "source": (
                        "Compiler.Proofs.IRGeneration.IRInterpreter."
                        "LegacyCompatibleExternalStmtList"
                    ),
                    "dispatch_local_surface": (
                        "Compiler.Proofs.IRGeneration.IRInterpreter."
                        "LegacyCompatibleRuntimeDispatch"
                    ),
                    "dispatch_goal_surface": (
                        "Compiler.Proofs.IRGeneration.IRInterpreter."
                        "InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal"
                    ),
                    "goal_surface": (
                        "Compiler.Proofs.IRGeneration.IRInterpreter."
                        "InterpretIRWithInternalsZeroConservativeExtensionGoal"
                    ),
                    "goal_composition_surface": (
                        "Compiler.Proofs.IRGeneration.IRInterpreter."
                        "interpretIRWithInternalsZeroConservativeExtensionGoal_"
                        "of_dispatchGoal"
                    ),
                    "goal_decomposition_surface": (
                        "Compiler.Proofs.IRGeneration.IRInterpreter."
                        "InterpretIRWithInternalsZeroConservativeExtensionInterfaces"
                    ),
                    "interface_builder_surface": (
                        "Compiler.Proofs.IRGeneration.IRInterpreter."
                        "interpretIRWithInternalsZeroConservativeExtensionInterfaces_"
                        "of_stmtCompatibility"
                    ),
                    "stmt_subgoal_surface": (
                        "Compiler.Proofs.IRGeneration.IRInterpreter."
                        "InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals"
                    ),
                    "stmt_subgoal_builder_surface": (
                        "Compiler.Proofs.IRGeneration.IRInterpreter."
                        "execIRStmtWithInternals_eq_execIRStmt_of_stmtSubgoals"
                    ),
                    "stmt_subgoal_closed_surface": (
                        "Compiler.Proofs.IRGeneration.IRInterpreter."
                        "interpretIRWithInternalsZeroConservativeExtensionStmtSubgoals_closed"
                    ),
                    "expr_stmt_dedicated_builtin_classifier": (
                        "Compiler.Proofs.IRGeneration.IRInterpreter."
                        "exprStmtUsesDedicatedBuiltinSemantics"
                    ),
                    "closed_expr_stmt_subcases": [
                        "special_expr_stmt_stop",
                        "special_expr_stmt_mstore",
                        "special_expr_stmt_return",
                        "special_expr_stmt_revert",
                        "special_expr_stmt_mapping_slot_sstore",
                    ],
                    "required_goal": (
                        "the zero-helper-fuel conservative-extension path for "
                        "helper-free runtime contracts with legacy-compatible "
                        "external bodies is now closed in IRInterpreter.lean: "
                        "the remaining stmt-subgoal object is discharged by "
                        "interpretIRWithInternalsZeroConservativeExtensionStmtSubgoals_closed, "
                        "and the full helper-free conservative-extension "
                        "interface and contract-level goal are closed by "
                        "interpretIRWithInternalsZeroConservativeExtensionInterfaces_closed "
                        "and interpretIRWithInternalsZeroConservativeExtensionGoal_closed"
                    ),
                },
                "compiled_target_proof_surface": {
                    "status": "helper_aware_ir_target_now_total_fuel_indexed_defs",
                    "source": (
                        "Compiler.Proofs.IRGeneration.IRInterpreter."
                        "evalIRExprWithInternals"
                    ),
                    "required_follow_on": (
                        "consume the now-closed helper-free conservative-"
                        "extension theorem through the helper-aware wrappers "
                        "in Function.lean / Dispatch.lean / Contract.lean, "
                        "separate the weaker LegacyCompatibleExternalBodies "
                        "witness from the stronger "
                        "LegacyCompatibleRuntimeContract boundary, retarget "
                        "the compiled-side theorem so helper tables can remain "
                        "present without affecting helper-free external "
                        "execution, and then thread helper-summary "
                        "soundness/rank evidence so calls.helperCompatibility "
                        "can disappear"
                    ),
                },
                "decreasing_rank_measure": (
                    "SupportedBodyHelperInterface.calleeRanksDecrease"
                ),
                "current_fail_closed_gate": (
                    "SupportedBodyCallInterface.helperCompatibility"
                ),
                "next_required_proof_step": (
                    "the helper-free compiled-side conservative-extension goal "
                    "is now closed on LegacyCompatibleRuntimeContract via "
                    "interpretIRWithInternalsZeroConservativeExtensionGoal_closed, "
                    "and Dispatch.lean / Contract.lean now expose direct "
                    "helper-aware closed wrappers "
                    "(interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir_closed "
                    "and compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed). "
                    "The highest-leverage next step is therefore no longer "
                    "stmt compatibility, and it is not merely to derive one "
                    "whole-contract witness from supported compile outputs: "
                    "the weaker external-body witness is plausibly derivable, "
                    "but the stronger LegacyCompatibleRuntimeContract side "
                    "condition still bakes in internalFunctions = []. The next "
                    "retarget must weaken that compiled-side boundary so "
                    "helper tables can remain present without affecting "
                    "helper-free external execution, and then consume helper-"
                    "summary soundness/rank evidence in the body/IR "
                    "composition interface so calls.helperCompatibility can "
                    "disappear"
                ),
                "blocking_seams": [
                    {
                        "name": "legacy_stmt_fragment_witness",
                        "source": "SupportedBodyInterface.stmtList",
                        "status": (
                            "callers still derive generic body proofs through "
                            "SupportedStmtList, which excludes helper-call forms"
                        ),
                    },
                    {
                        "name": "ir_internal_call_semantics",
                        "source": (
                            "Compiler.Proofs.IRGeneration.IRInterpreter."
                            "execIRFunctionWithInternals"
                        ),
                        "status": (
                            "a helper-aware IR execution target now exists and "
                            "can resolve IRContract.internalFunctions, and the "
                            "public theorem stack now exposes helper-aware "
                            "wrapper theorems parameterized by conservative-"
                            "extension equalities; the default theorem path "
                            "still closes through legacy execIRFunction / "
                            "interpretIR until that equality is proved"
                        ),
                    },
                    {
                        "name": "legacy_ir_target_compatibility_subset",
                        "source": (
                            "Compiler.Proofs.IRGeneration.IRInterpreter."
                            "interpretIRWithInternals"
                        ),
                        "status": (
                            "the helper-free external-body compatibility subset "
                            "is now formalized in IRInterpreter.lean as "
                            "LegacyCompatibleExternalStmtList, the helper-free "
                            "runtime-contract shape is captured by "
                            "LegacyCompatibleRuntimeContract, and "
                            "InterpretIRWithInternalsZeroConservativeExtensionGoal "
                            "now encodes the exact first compiled-side retarget "
                            "theorem, and IRInterpreter.lean now closes it on "
                            "that helper-free runtime subset via "
                            "interpretIRWithInternalsZeroConservativeExtensionGoal_closed. "
                            "Dispatch.lean and Contract.lean now also expose "
                            "direct helper-aware closed wrappers that consume "
                            "that closed theorem on an explicit "
                            "legacy-compatibility witness"
                        ),
                    },
                    {
                        "name": "summary_soundness_not_yet_consumed",
                        "source": (
                            "GenericInduction."
                            "supported_function_body_correct_from_exact_state_"
                            "generic_with_helpers"
                        ),
                        "status": (
                            "the helper-aware body theorem exists, but helper "
                            "summary-soundness/rank evidence is not yet "
                            "threaded through that body proof"
                        ),
                    },
                ],
            },
        },
        "current_out_of_scope_surfaces": [
            {
                "name": "helper_composition",
                "status": "blocked_at_body_ir_composition_seam",
                "issue": 1630,
            },
            {
                "name": "low_level_calls_and_returndata",
                "status": "not_in_generic_theorem",
                "issue": 1630,
            },
            {
                "name": "proxy_upgradeability_delegatecall",
                "status": "not_in_generic_theorem",
                "issue": 1630,
            },
            {
                "name": "events_and_typed_errors",
                "status": "not_in_generic_theorem",
                "issue": 1630,
            },
            {
                "name": "storage_layout_rich_features",
                "status": "partially_outside_generic_theorem",
                "issue": 1630,
            },
            {
                "name": "constructors_fallback_receive",
                "status": "not_in_generic_theorem",
                "issue": 1630,
            },
            {
                "name": "local_obligations",
                "status": "explicitly_excluded_from_supported_fragment",
                "issue": 1630,
            },
        ],
        "ranked_next_steps": [
            {
                "rank": "P1",
                "name": "replace exclusions with compositional interfaces",
                "status": "in_progress",
            },
            {
                "rank": "P2",
                "name": (
                    "internal helper compositional proof reuse at the body/IR "
                    "seam, starting with compiled-side IR helper semantics "
                    "(#1638)"
                ),
                "status": "next_structural_blocker",
            },
            {
                "rank": "P3",
                "name": "low-level calls, returndata, and proxy modeling",
                "status": "pending",
            },
            {
                "rank": "P4",
                "name": "events, logs, and typed errors",
                "status": "pending",
            },
            {
                "rank": "P5",
                "name": "storage and layout rich whole-contract coverage",
                "status": "pending",
            },
            {
                "rank": "P6",
                "name": "constructor, fallback, and receive semantics",
                "status": "pending",
            },
            {
                "rank": "P7",
                "name": "local obligations as proof-carrying extensions",
                "status": "pending",
            },
        ],
    }


def render_catalog() -> str:
    return json.dumps(build_catalog(), indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate the Layer 2 proof-boundary catalog artifact."
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "artifacts" / "layer2_boundary_catalog.json",
        help="Output artifact path.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Fail if the output file is missing or stale; do not write changes.",
    )
    args = parser.parse_args()

    rendered = render_catalog()
    output = args.output

    if args.check:
        if not output.exists():
            raise SystemExit(f"Missing Layer 2 boundary artifact: {output}")
        existing = output.read_text(encoding="utf-8")
        if existing != rendered:
            raise SystemExit(
                f"Stale Layer 2 boundary artifact: {output}\n"
                "Run `python3 scripts/generate_layer2_boundary_catalog.py`."
            )
        print(f"Layer 2 boundary artifact is up to date: {output}")
        return

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(f"Wrote Layer 2 boundary artifact: {output}")


if __name__ == "__main__":
    main()
