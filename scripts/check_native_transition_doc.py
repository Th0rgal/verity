#!/usr/bin/env python3
"""Keep the native EVMYulLean transition document honest.

PR #1743 deliberately introduces an executable native harness without moving the
public theorem target. This checker prevents the transition note from losing the
explicit blocker list or overstating native EVMYulLean as the current public
semantic target.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / "docs" / "NATIVE_EVMYULLEAN_TRANSITION.md"
DOD_DOC = ROOT / "docs" / "NATIVE_EVMYULLEAN_FULL_TRANSITION_DONE.md"
END_TO_END = ROOT / "Compiler" / "Proofs" / "EndToEnd.lean"
NATIVE_HARNESS = (
    ROOT
    / "Compiler"
    / "Proofs"
    / "YulGeneration"
    / "Backends"
    / "EvmYulLeanNativeHarness.lean"
)
RETARGET = (
    ROOT
    / "Compiler"
    / "Proofs"
    / "YulGeneration"
    / "Backends"
    / "EvmYulLeanRetarget.lean"
)
BUILTINS = (
    ROOT
    / "Compiler"
    / "Proofs"
    / "YulGeneration"
    / "ReferenceOracle"
    / "Builtins.lean"
)
PRESERVATION = ROOT / "Compiler" / "Proofs" / "YulGeneration" / "Preservation.lean"
NATIVE_ADAPTER = (
    ROOT
    / "Compiler"
    / "Proofs"
    / "YulGeneration"
    / "Backends"
    / "EvmYulLeanAdapter.lean"
)
NATIVE_SMOKE_TEST = (
    ROOT
    / "Compiler"
    / "Proofs"
    / "YulGeneration"
    / "Backends"
    / "EvmYulLeanNativeSmokeTest.lean"
)

REQUIRED_SNIPPETS = (
    "interpretYulRuntimeWithBackend .evmYulLean",
    "Verity's custom fuel-based Yul statement interpreter",
    "not the final architecture",
    "Native.interpretRuntimeNative",
    "Native.interpretIRRuntimeNative",
    "EvmYul.Yul.callDispatcher",
    "observable storage slot set explicitly",
    "only materializes pre-state storage for those slots",
    "nativeResultsMatchOn",
    "explicitly observable final-storage slots",
    "exec_lowerNativeSwitchBlock_selector_find_hit_error_projectResult_eq",
    "contractDispatcherExecResult_block_lowerNativeSwitchBlock_selector_find_hit_error_projectResult_eq",
    "exec_lowerNativeSwitchBlock_selector_find_hit_error_store_projectResult_eq",
    "exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult_eq",
    "contractDispatcherExecResult_block_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult_eq",
    "exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_store_projectResult_eq",
    "exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_projectResult_eq",
    "exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq",
    "exec_lowerNativeSwitchBlock_selector_find_hit_ok_projectResult_eq",
    "exec_lowerNativeSwitchBlock_selector_find_hit_ok_store_projectResult_eq",
    "exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq",
    "contractDispatcherExecResult_block_lowerNativeSwitchBlock_selector_find_hit_ok_projectResult_eq",
    "nativeDispatcherExecMatchesIRPositive_of_project_eq_match",
    "lowerSwitchCasesNativeWithSwitchIds_find?_some_of_find_function",
    "lowerSwitchCasesNativeWithSwitchIds_find?_none_of_find_function",
    "buildSwitchSourceCases_eq_switchCases",
    "lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_some_of_find_function",
    "lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_none_of_find_function",
    "lowerStmtsNative_single_block_ok_singleton",
    "lowerStmtsNative_block_stmts_eq",
    "lowerStmtsNativeWithSwitchIds_let_head_eq",
    "lowerStmtsNativeWithSwitchIds_if_head_eq",
    "lowerStmtsNativeWithSwitchIds_singleton_switch_eq",
    "lowerRuntimeContractNative_emitYul_noMapping_noInternals_noFallback_noReceive",
    "lowerRuntimeContractNative_emitYul_mapping_noInternals_noFallback_noReceive_reserved",
    "lowerStmtsNativeWithSwitchIds_revert_zero_zero",
    "lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq",
    "lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq_sourceLowered",
    "buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered",
    "buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function",
    "buildSwitch_noFallback_noReceive_lowered_inner_find?_none_of_find_function",
    "same explicit fuel",
    "default runtime fuel",
    "retargeting evidence remains isolated",
    "not yet proved",
    "`yulCodegen_preserves_semantics_evmYulLeanBackend`",
    "`yulCodegen_preserves_semantics_evmYulLeanBackend_via_reference_oracle`",
    "`yulCodegen_preserves_semantics_via_reference_oracle`",
    "not yet a native source-of-truth Layer 3 proof",
    "#1741",
    "#1738",
    "#1742",
    "`blockTimestamp`",
    "mapping-struct",
    "signature-based identity model",
    "`YulTransaction.chainId` must match",
    "EvmYul.chainId",
    "`chainid()` and `blobbasefee()` now fail closed on the selected native runtime path",
    "EvmYul.MIN_BASE_FEE_PER_BLOB_GAS",
    "`initialState_unbridgedEnvironmentDefaults`",
)

FORBIDDEN_SNIPPETS = (
    "native EVMYulLean is the authoritative semantic target today",
    "native EVMYulLean is now the authoritative semantic target",
    "public theorem targets `interpretIRRuntimeNative`",
    "public theorem target is `interpretIRRuntimeNative`",
    "custom Yul interpreter is only a regression oracle",
)


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def check_doc(text: str) -> list[str]:
    normalized = normalize_ws(text)
    errors: list[str] = []

    for snippet in REQUIRED_SNIPPETS:
        if normalize_ws(snippet) not in normalized:
            errors.append(
                f"{DOC.relative_to(ROOT)} is missing required native-transition status text: `{snippet}`"
            )

    normalized_lower = normalized.lower()
    for snippet in FORBIDDEN_SNIPPETS:
        if normalize_ws(snippet).lower() in normalized_lower:
            errors.append(
                f"{DOC.relative_to(ROOT)} overstates the current native-transition status: `{snippet}`"
            )

    if "#1741" in normalized:
        issue_1741 = normalized.index("#1741")
        issue_1738 = normalized.find("#1738", issue_1741)
        issue_1742 = normalized.find("#1742", issue_1738 if issue_1738 >= 0 else issue_1741)
        if issue_1738 < 0 or issue_1742 < 0:
            errors.append(
                f"{DOC.relative_to(ROOT)} must list blockers #1741, #1738, and #1742 together"
            )

    return errors


def check_definition_of_done_doc(text: str) -> list[str]:
    """Keep the definition-of-done baseline synchronized with current names."""

    normalized = normalize_ws(text)
    errors: list[str] = []

    for required in (
        "interpretYulRuntimeWithBackend .evmYulLean",
        "yulCodegen_preserves_semantics_evmYulLeanBackend_via_reference_oracle",
        "Native.interpretIRRuntimeNative",
        "EvmYul.Yul.callDispatcher",
    ):
        if normalize_ws(required) not in normalized:
            errors.append(
                f"{DOD_DOC.relative_to(ROOT)} is missing current native-transition "
                f"definition-of-done text: `{required}`"
            )

    for forbidden in (
        "interpretYulRuntimeEvmYulLeanFuelWrapperDefaultFuel",
        "interpretYulRuntimeEvmYulLeanFuelWrapper",
        "evmYulLeanFuelWrapperDefaultFuel",
    ):
        if forbidden in normalized:
            errors.append(
                f"{DOD_DOC.relative_to(ROOT)} must not mention removed "
                f"EVMYulLean fuel-wrapper surface `{forbidden}`"
            )

    return errors


def check_public_theorem_target(
    end_to_end_text: str, native_harness_text: str, retarget_text: str
) -> list[str]:
    """Pin the current transition boundary after EndToEnd wrapper removal.

    Public EndToEnd correctness targets native dispatcher execution. The old
    backend-parameterized interpreter lemmas remain isolated in the lower
    retargeting module while generated native direct-match coverage is widened.
    """

    errors: list[str] = []
    normalized_end_to_end = normalize_ws(end_to_end_text)
    normalized_native_harness = normalize_ws(native_harness_text)
    normalized_retarget = normalize_ws(retarget_text)

    if "interpretYulRuntimeWithBackend .evmYulLean" in normalized_end_to_end:
        errors.append(
            "Compiler/Proofs/EndToEnd.lean must not mention the legacy "
            "`interpretYulRuntimeWithBackend .evmYulLean` transition target; "
            "keep that evidence isolated in EvmYulLeanRetarget.lean"
        )

    for required_native_surface in (
        "def nativeResultsMatch",
        "def nativeResultsMatchOn",
        "def nativeDispatcherExecMatchesIRPositive",
        "theorem nativeIRRuntimeMatchesIR_of_lowered_dispatcherExec_positive_match",
        "theorem nativeIRRuntimeMatchesIR_of_generated_lowered_dispatcherExec_positive_match",
        "def nativeIRRuntimeMatchesIR",
        "theorem validateNativeRuntimeEnvironment_ofIR_representableEnvironment",
        "theorem validateNativeRuntimeEnvironment_ofIR_globalDefaults",
        "theorem nativeDispatcherExecMatchesIRPositive_of_project_eq_match",
        "theorem nativeIRRuntimeMatchesIR_of_lowered_dispatcherExec_project_eq_match",
        "theorem nativeIRRuntimeMatchesIR_of_generated_lowered_dispatcherExec_project_eq_match",
        "theorem nativeDispatcherExecMatchesIRPositive_of_exec_ok_match",
        "theorem nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match",
        "theorem nativeDispatcherExecMatchesIRPositive_of_exec_yulHalt_project_eq_match",
        "theorem nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match",
        "def nativeMappingSlotFunctionDefinition",
        "theorem lowerFunctionDefinitionNativeWithReserved_mappingSlotFuncAt_zero",
        "theorem lowerFunctionDefinitionNativeWithReserved_mappingSlotFuncAt_zero_body",
        "theorem lowerRuntimeContractNative_emitYul_mapping_noInternals_noFallback_noReceive_reserved",
        "theorem lowerRuntimeContractNative_emitYul_mapping_ok_dispatcher_reserved",
    ):
        if required_native_surface not in normalized_native_harness:
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean "
                "must own the native theorem/result surface "
                f"`{required_native_surface}` until the generated-fragment "
                "native bridge is discharged"
            )

    for required_native_seam in (
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_match",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure_ofIR_environment",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure_ofIR_environment_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure_ofIR_globalDefaults",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure_ofIR_globalDefaults_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_eq_match",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure_ofIR_environment",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure_ofIR_environment_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure_ofIR_globalDefaults",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure_ofIR_globalDefaults_canonicalFuel",
        "theorem generatedRuntimeNativeFragment_of_compile_ok_supported_safe",
        "theorem validateGeneratedRuntimeNativeFragment_of_compile_ok_supported_safe",
        "theorem lowerRuntimeContractNative_of_compile_ok_supported_noMapping",
        "theorem lowerRuntimeContractNative_of_compile_ok_supported_noMapping_ok_dispatcher",
        "theorem lowerRuntimeContractNative_of_compile_ok_supported_mapping_reserved",
        "theorem lowerRuntimeContractNative_of_compile_ok_supported_mapping_ok_dispatcher_reserved",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_globalDefaults",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_environment",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_globalDefaults",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_mapping_reserved",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_environment",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_mapping_reserved",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_environment",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_project_body_closure_noMapping",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_mapping_reserved",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_project_body_closure_mapping_reserved",
        "theorem layer3_contract_preserves_semantics_native_of_generated_dispatcherExec_positive_match",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_positive_external_bodies_match",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_positive_body_closure",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_positive_body_closure_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_project_external_bodies_match",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_project_body_closure",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_project_body_closure_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_globalDefaults",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_environment",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_globalDefaults",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_environment",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_environment",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_project_body_closure_noMapping",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_mapping_reserved",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_project_body_closure_mapping_reserved",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_external_bodies_match",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_match",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure_ofIR_environment_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure_ofIR_globalDefaults_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_external_bodies_match",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_match",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_ofIR_environment_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_ofIR_globalDefaults_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_noMapping",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_mapping_reserved",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_mapping_reserved",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_noMapping_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_noMapping_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem simpleStorage_endToEnd_native_evmYulLean_of_positive_dispatcherExec_match",
        "theorem simpleStorage_endToEnd_native_evmYulLean_of_lowered_runtime_dispatcherStmts_match",
        "theorem simpleStorageNativeCallDispatcherMatchBridge_of_per_case",
        "theorem simpleStorageNativeRetrieveHitMatchBridge_proved",
        "theorem simpleStorageNativeStoreHitMatchBridge_proved",
        "theorem simpleStorageNativeSelectorMissMatchBridge_proved",
    ):
        if required_native_seam not in normalized_end_to_end:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must keep the native theorem seam "
                f"`{required_native_seam}` explicit until the generated-fragment "
                "native bridge is discharged"
            )

    for removed_transition_seam in (
        "layer3_contract_preserves_semantics_evmYulLeanBackend_with_function_bridge",
        "layer3_contract_preserves_semantics_evmYulLeanBackend",
        "layer3_contract_preserves_semantics_native_of_evmYulLean_bridge",
        "layers2_3_ir_matches_yul_evmYulLeanBackend_with_function_bridge",
        "layers2_3_ir_matches_yul_evmYulLeanBackend",
        "layers2_3_ir_matches_native_evmYulLean_of_evmYulLean_bridge",
        "simpleStorage_endToEnd_evmYulLeanBackend",
    ):
        if re.search(
            r"^\s*(?:private\s+)?theorem\s+"
            + re.escape(removed_transition_seam)
            + r"\b",
            end_to_end_text,
            re.MULTILINE,
        ):
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must not define removed "
                f"backend-wrapper transition lemma `{removed_transition_seam}`"
            )

    for private_native_identity_seam in (
        "layer3_contract_preserves_semantics_native",
        "layers2_3_ir_matches_native_evmYulLean",
    ):
        if re.search(
            r"^\s*theorem\s+"
            + re.escape(private_native_identity_seam)
            + r"\b",
            end_to_end_text,
            re.MULTILINE,
        ):
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must not export arbitrary-fuel "
                f"native identity seam `{private_native_identity_seam}`; keep "
                "the public surface on generated-dispatcher native wrappers"
            )

    for removed_fuel_wrapper_seam in (
        "def yulResultsAgreeOn",
        "def nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper",
        "def nativeCallDispatcherAgreesWithEvmYulLeanFuelWrapper",
        "def nativeDispatcherBlockAgreesWithEvmYulLeanFuelWrapper",
        "def nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper",
        "def nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapperPositive",
        "theorem nativeResultsMatchOn_ok_of_resultsMatch_of_yulResultsAgreeOn",
        "theorem yulResultsAgreeOn_of_resultsMatch_of_nativeResultsMatchOn",
        "theorem nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper_of_ok_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapperPositive_of_exec_ok_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapperPositive_of_exec_yulHalt_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapperPositive_of_exec_yulHalt_project_eq_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapperPositive_of_exec_error_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapperPositive_of_exec_error_project_eq_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper_of_positive",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper_of_exec_ok_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper_of_exec_yulHalt_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper_of_exec_error_agree",
        "theorem nativeDispatcherBlockAgreesWithEvmYulLeanFuelWrapper_of_exec_agree",
        "theorem nativeCallDispatcherAgreesWithEvmYulLeanFuelWrapper_of_dispatcherBlock_agree",
        "theorem nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper_of_lowered_callDispatcher_agree",
        "theorem nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper_of_lowered_dispatcherExec_positive_agree",
        "theorem nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper_of_generated_lowered_callDispatcher_agree",
        "theorem nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper_of_generated_lowered_dispatcherExec_positive_agree",
    ):
        if removed_fuel_wrapper_seam in normalized_end_to_end:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must not reintroduce the removed "
                "native fuel-wrapper agreement seam "
                f"`{removed_fuel_wrapper_seam.removeprefix('theorem ').removeprefix('def ')}`"
            )

    for forbidden_ir_runtime_alias in (
        "def nativeIRRuntimeAgreesWithEvmYulLean ",
        "theorem nativeIRRuntimeAgreesWithEvmYulLean_of_ok_agree ",
        "theorem nativeIRRuntimeAgreesWithEvmYulLean_of_nativeIRRuntimeMatchesIR ",
        "theorem nativeIRRuntimeAgreesWithEvmYulLean_of_ok_nativeResultsMatchOn ",
        "theorem nativeIRRuntimeAgreesWithEvmYulLean_of_lowered_callDispatcher_agree ",
        "theorem nativeIRRuntimeAgreesWithEvmYulLean_of_lowered_dispatcherExec_positive_agree ",
        "theorem nativeIRRuntimeAgreesWithEvmYulLean_of_generated_lowered_callDispatcher_agree ",
        "theorem nativeIRRuntimeAgreesWithEvmYulLean_of_generated_lowered_dispatcherExec_positive_agree ",
        "theorem nativeIRRuntimeAgreesWithEvmYulLean_of_compiled_generated_lowered_dispatcherExec_positive_agree ",
        "theorem nativeIRRuntimeAgreesWithEvmYulLean_of_compiled_generated_lowered_dispatcherExec_positive_body_closure ",
    ):
        if forbidden_ir_runtime_alias in normalized_end_to_end:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must not reintroduce the hidden "
                "native IR-runtime fuel-wrapper alias "
                f"`{forbidden_ir_runtime_alias.strip()}`"
            )

    for forbidden_dispatcher_alias in (
        "def nativeCallDispatcherAgreesWithEvmYulLean ",
        "def nativeDispatcherBlockAgreesWithEvmYulLean ",
        "def nativeDispatcherExecAgreesWithEvmYulLean ",
        "def nativeDispatcherExecAgreesWithEvmYulLeanPositive ",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanPositive_of_exec_ok_agree ",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanPositive_of_exec_yulHalt_agree ",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanPositive_of_exec_yulHalt_project_eq_agree ",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanPositive_of_exec_error_agree ",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanPositive_of_exec_error_project_eq_agree ",
        "theorem nativeDispatcherExecAgreesWithEvmYulLean_of_positive ",
        "theorem nativeDispatcherExecAgreesWithEvmYulLean_of_exec_ok_agree ",
        "theorem nativeDispatcherExecAgreesWithEvmYulLean_of_exec_yulHalt_agree ",
        "theorem nativeDispatcherExecAgreesWithEvmYulLean_of_exec_error_agree ",
        "theorem nativeDispatcherBlockAgreesWithEvmYulLean_of_exec_agree ",
        "theorem nativeCallDispatcherAgreesWithEvmYulLean_of_dispatcherBlock_agree ",
    ):
        if forbidden_dispatcher_alias in normalized_end_to_end:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must not reintroduce the hidden "
                "native dispatcher fuel-wrapper alias "
                f"`{forbidden_dispatcher_alias.strip()}`"
            )

    for forbidden_positive_alias in (
        "theorem layer3_contract_preserves_semantics_native_of_generated_dispatcherExec_positive ",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive ",
    ):
        if forbidden_positive_alias in normalized_end_to_end:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must not reintroduce the "
                "misleading positive dispatcher-exec compatibility alias "
                f"`{forbidden_positive_alias.removeprefix('theorem ').strip()}`; "
                "use the explicit `_positive_match` theorem name"
            )

    for forbidden_simple_storage_bridge_surface in (
        "def simpleStorageNativeCallDispatcherBridge ",
        "def simpleStorageNativeRetrieveHitBridge ",
        "def simpleStorageNativeStoreHitBridge ",
        "def simpleStorageNativeSelectorMissBridge ",
        "theorem simpleStorageNativeRetrieveHitBridge_proved ",
        "theorem simpleStorageNativeStoreHitBridge_proved ",
        "theorem simpleStorageNativeSelectorMissBridge_proved ",
        "theorem simpleStorageNativeCallDispatcherBridge_of_per_case ",
    ):
        if forbidden_simple_storage_bridge_surface in normalized_end_to_end:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must not reintroduce the "
                "obsolete SimpleStorage fuel-wrapper bridge surface "
                f"`{forbidden_simple_storage_bridge_surface.strip()}`"
            )

    for forbidden_reference_oracle_seam in (
        "theorem layer3_contract_preserves_semantics_via_reference_oracle ",
        "theorem layer3_contract_preserves_semantics_via_reference_oracle_with_function_bridge ",
        "theorem layers2_3_ir_matches_yul_via_reference_oracle ",
        "theorem simpleStorage_endToEnd_via_reference_oracle ",
    ):
        if forbidden_reference_oracle_seam in normalized_end_to_end:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must not reintroduce the "
                "legacy Verity-backed public entry point "
                f"`{forbidden_reference_oracle_seam.strip()}`"
            )

    for forbidden_public_alias in (
        "theorem layer3_contract_preserves_semantics ",
        "theorem simpleStorage_endToEnd ",
    ):
        if forbidden_public_alias in normalized_end_to_end:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must not reintroduce hidden "
                "default-fuel public theorem alias "
                f"`{forbidden_public_alias.strip()}`"
            )

    simple_storage_native_marker = "theorem simpleStorage_endToEnd_native_evmYulLean "
    simple_storage_native_start = normalized_end_to_end.find(simple_storage_native_marker)
    if simple_storage_native_start < 0:
        errors.append(
            "Compiler/Proofs/EndToEnd.lean must keep the public native "
            "`simpleStorage_endToEnd_native_evmYulLean` theorem explicit"
        )
    else:
        next_theorem = normalized_end_to_end.find(
            " theorem ",
            simple_storage_native_start + len(simple_storage_native_marker),
        )
        simple_storage_native_span = (
            normalized_end_to_end[simple_storage_native_start:]
            if next_theorem < 0
            else normalized_end_to_end[simple_storage_native_start:next_theorem]
        )
        for required_direct_target in (
            "simpleStorage_endToEnd_native_evmYulLean_of_lowered_runtime_dispatcherStmts_match",
            "simpleStorageNativeCallDispatcherMatchBridge_of_per_case",
        ):
            if required_direct_target not in simple_storage_native_span:
                errors.append(
                    "Compiler/Proofs/EndToEnd.lean public native SimpleStorage "
                    "theorem must consume the full-runtime native dispatcher "
                    f"target `{required_direct_target}`"
                )
        for forbidden_compat_target in (
            "simpleStorage_endToEnd_native_evmYulLean_of_positive_dispatcherExec_bridge",
            "simpleStorageNativeCallDispatcherBridge_of_per_case",
        ):
            if forbidden_compat_target in simple_storage_native_span:
                errors.append(
                    "Compiler/Proofs/EndToEnd.lean public native SimpleStorage "
                    "theorem must not consume the compatibility dispatcher "
                    f"bridge `{forbidden_compat_target}`"
                )

    for required_fuel_surface in (
        "def interpretYulRuntimeWithBackend",
    ):
        if required_fuel_surface not in normalized_retarget:
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/"
                "EvmYulLeanRetarget.lean must keep the backend-parameterized "
                f"EVMYulLean interpreter surface `{required_fuel_surface}` explicit"
            )

    for forbidden_fuel_alias in (
        "def interpretYulRuntimeEvmYulLeanFuel ",
        "def interpretYulRuntimeEvmYulLean ",
        "theorem interpretYulRuntimeEvmYulLean_eq_backend ",
    ):
        if forbidden_fuel_alias in normalized_retarget:
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/"
                "EvmYulLeanRetarget.lean must not reintroduce hidden "
                f"EVMYulLean fuel-wrapper alias `{forbidden_fuel_alias.strip()}`"
            )

    forbidden_native_in_end_to_end = (
        "theorem target: interpretRuntimeNative",
        "theorem target: EvmYul.Yul.callDispatcher",
    )
    for native_target in forbidden_native_in_end_to_end:
        if native_target in normalized_end_to_end:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean should target the native IR "
                "runtime seam, not the lower-level harness implementation "
                f"`{native_target.removeprefix('theorem target: ')}`"
            )

    for required_native_entrypoint in (
        "def interpretRuntimeNative",
        "def interpretIRRuntimeNative",
        "EvmYul.Yul.callDispatcher",
        "def generatedRuntimeNativeFragment",
        "def validateGeneratedRuntimeNativeFragment",
        "unsupportedGeneratedRuntimeNativeFragmentError",
        "def generatedRuntimeFunctionNamesUnique",
        "def generatedRuntimeDispatcherHasNoFuncDefs",
        "def generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs",
        "def buildSwitchSourceCases",
        "theorem buildSwitchSourceCases_eq_switchCases",
        "theorem lowerSwitchCasesNativeWithSwitchIds_find?_some_of_find_function",
        "theorem lowerSwitchCasesNativeWithSwitchIds_find?_none_of_find_function",
        "theorem lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_some_of_find_function",
        "theorem lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_none_of_find_function",
        "theorem lowerRuntimeContractNative_single_stmt_eq_lowerStmtsNative",
        "theorem lowerRuntimeContractNative_emitYul_noMapping_ok_dispatcher",
        "theorem lowerStmtsNative_single_block_ok_singleton",
        "theorem lowerStmtsNative_block_stmts_eq",
        "theorem lowerStmtsNativeWithSwitchIds_let_head_eq",
        "theorem lowerStmtsNativeWithSwitchIds_if_head_eq",
        "theorem lowerStmtsNativeWithSwitchIds_singleton_switch_eq",
        "theorem lowerStmtsNativeWithSwitchIds_revert_zero_zero",
        "theorem lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq",
        "theorem lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq_sourceLowered",
        "theorem buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered",
        "theorem buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function",
        "theorem buildSwitch_noFallback_noReceive_lowered_inner_find?_none_of_find_function",
        "theorem NativeBlockPreservesWord_singleton",
        "theorem NativeBlockPreservesWord_of_forall_stmt",
        "theorem NativeBlockPreservesWord_of_forall_stmt_write_not_mem",
        "theorem NativeStmtPreservesWord_block",
        "theorem exec_lowerNativeSwitchBlock_selector_find_hit_error_projectResult_eq",
        "theorem contractDispatcherExecResult_block_lowerNativeSwitchBlock_selector_find_hit_error_projectResult_eq",
        "theorem exec_lowerNativeSwitchBlock_selector_find_hit_error_store_projectResult_eq",
        "theorem exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult_eq",
        "theorem contractDispatcherExecResult_block_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult_eq",
        "theorem exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_store_projectResult_eq",
        "theorem exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_projectResult_eq",
        "theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq",
        "theorem exec_lowerNativeSwitchBlock_selector_find_hit_ok_projectResult_eq",
        "theorem exec_lowerNativeSwitchBlock_selector_find_hit_ok_store_projectResult_eq",
        "theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq",
        "theorem contractDispatcherExecResult_block_lowerNativeSwitchBlock_selector_find_hit_ok_projectResult_eq",
        "theorem NativeStmtPreservesWord_if_of_eval_self",
        "theorem NativeStmtPreservesWord_if_of_eval_preserves",
        "theorem NativeStmtPreservesWord_if_of_cond_preserves",
        "theorem nativeSwitchBranchFold_ok_preserves_word",
        "theorem execSwitchCases_ok_branch_preserves_word",
        "theorem NativeStmtPreservesWord_switch_of_eval_preserves",
        "theorem NativeStmtPreservesWord_switch_of_cond_preserves",
        "theorem NativeStmtPreservesWord_switch_of_cond_preserves_and_nativeStmtsWriteNames_not_mem",
        "theorem NativeStmtPreservesWord_switch_of_eval_preserves_and_nativeStmtsWriteNames_not_mem",
        "theorem NativeStmtPreservesWord_lowerAssignNative_lit_of_ne",
        "theorem NativeStmtPreservesWord_lowerAssignNative_hex_of_ne",
        "theorem NativeStmtPreservesWord_lowerAssignNative_ident_of_ne",
        "theorem NativeStmtPreservesWord_lowerAssignNative_str_of_ne",
        "theorem NativeStmtPreservesWord_let_none_of_not_mem",
        "theorem NativeStmtPreservesWord_let_var_of_not_mem",
        "theorem NativeStmtPreservesWord_let_lit_of_not_mem",
        "theorem NativeStmtPreservesWord_let_lowerExprNative_lit_of_not_mem",
        "theorem NativeStmtPreservesWord_let_lowerExprNative_hex_of_not_mem",
        "theorem NativeStmtPreservesWord_let_lowerExprNative_str_of_not_mem",
        "theorem NativeStmtPreservesWord_let_lowerExprNative_ident_of_not_mem",
        "theorem NativeStmtPreservesWord_let_prim_of_evalArgs_primCall_preserves",
        "theorem NativeStmtPreservesWord_let_user_of_evalArgs_call_preserves",
        "theorem NativeStmtPreservesWord_let_prim_of_nativeEvalArgs_primCall_preserves",
        "theorem NativeStmtPreservesWord_let_user_of_nativeEvalArgs_call_preserves",
        "theorem NativeStmtPreservesWord_let_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves",
        "theorem NativeStmtPreservesWord_let_lowerExprNative_call_userFunction_of_evalArgs_call_preserves",
        "theorem NativeStmtPreservesWord_let_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves",
        "theorem NativeStmtPreservesWord_let_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves",
        "theorem NativeStmtPreservesWord_lowerAssignNative_call_runtimePrimOp_of_evalArgs_primCall_preserves",
        "theorem NativeStmtPreservesWord_lowerAssignNative_call_userFunction_of_evalArgs_call_preserves",
        "theorem NativeStmtPreservesWord_lowerAssignNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves",
        "theorem NativeStmtPreservesWord_lowerAssignNative_call_userFunction_of_nativeEvalArgs_call_preserves",
        "theorem NativePrimCallPreservesWord_calldatasize",
        "theorem NativePrimCallPreservesWord_callvalue",
        "theorem NativePrimCallPreservesWord_address",
        "theorem NativePrimCallPreservesWord_balance",
        "theorem NativePrimCallPreservesWord_origin",
        "theorem NativePrimCallPreservesWord_caller",
        "theorem NativePrimCallPreservesWord_timestamp",
        "theorem NativePrimCallPreservesWord_number",
        "theorem NativePrimCallPreservesWord_chainid",
        "theorem NativePrimCallPreservesWord_blobbasefee",
        "theorem NativePrimCallPreservesWord_gasprice",
        "theorem NativePrimCallPreservesWord_coinbase",
        "theorem NativePrimCallPreservesWord_gaslimit",
        "theorem NativePrimCallPreservesWord_selfbalance",
        "theorem NativePrimCallPreservesWord_unary_same_state",
        "theorem NativePrimCallPreservesWord_binary_same_state",
        "theorem NativePrimCallPreservesWord_ternary_same_state",
        "theorem NativePrimCallPreservesWord_iszero",
        "theorem NativePrimCallPreservesWord_shr",
        "theorem NativePrimCallPreservesWord_add",
        "theorem NativePrimCallPreservesWord_sub",
        "theorem NativePrimCallPreservesWord_mul",
        "theorem NativePrimCallPreservesWord_div",
        "theorem NativePrimCallPreservesWord_mod",
        "theorem NativePrimCallPreservesWord_sdiv",
        "theorem NativePrimCallPreservesWord_smod",
        "theorem NativePrimCallPreservesWord_addmod",
        "theorem NativePrimCallPreservesWord_mulmod",
        "theorem NativePrimCallPreservesWord_exp",
        "theorem NativePrimCallPreservesWord_signextend",
        "theorem NativePrimCallPreservesWord_eq",
        "theorem NativePrimCallPreservesWord_lt",
        "theorem NativePrimCallPreservesWord_gt",
        "theorem NativePrimCallPreservesWord_slt",
        "theorem NativePrimCallPreservesWord_sgt",
        "theorem NativePrimCallPreservesWord_and",
        "theorem NativePrimCallPreservesWord_or",
        "theorem NativePrimCallPreservesWord_xor",
        "theorem NativePrimCallPreservesWord_not",
        "theorem NativePrimCallPreservesWord_shl",
        "theorem NativePrimCallPreservesWord_byte",
        "theorem NativePrimCallPreservesWord_sar",
        "theorem NativePrimCallPreservesWord_sload",
        "theorem NativePrimCallPreservesWord_calldataload",
        "theorem NativePrimCallPreservesWord_mload",
        "theorem NativePrimCallPreservesWord_mstore",
        "theorem NativePrimCallPreservesWord_mstore8",
        "theorem NativePrimCallPreservesWord_tload",
        "theorem NativePrimCallPreservesWord_tstore",
        "theorem NativePrimCallPreservesWord_sstore",
        "theorem NativePrimCallPreservesWord_stop",
        "theorem NativePrimCallPreservesWord_return",
        "theorem NativePrimCallPreservesWord_revert",
        "theorem NativePrimCallPreservesWord_msize",
        "theorem NativePrimCallPreservesWord_gas",
        "theorem NativePrimCallPreservesWord_returndatasize",
        "theorem NativePrimCallPreservesWord_calldatacopy",
        "theorem NativePrimCallPreservesWord_returndatacopy",
        "theorem NativePrimCallPreservesWord_pop",
        "theorem NativePrimCallPreservesWord_keccak256",
        "theorem NativePrimCallPreservesWord_log0",
        "theorem NativePrimCallPreservesWord_log1",
        "theorem NativePrimCallPreservesWord_log2",
        "theorem NativePrimCallPreservesWord_log3",
        "theorem NativePrimCallPreservesWord_log4",
        "def NativeExprPreservesWord",
        "def NativeEvalArgsPreservesWord",
        "theorem NativeExprPreservesWord_var",
        "theorem NativeExprPreservesWord_lit",
        "theorem NativeEvalArgsPreservesWord_nil",
        "theorem NativeEvalArgsPreservesWord_cons",
        "theorem NativeEvalArgsPreservesWord_map_lowerExprNative",
        "theorem NativeEvalArgsPreservesWord_map_lowerExprNative_reverse",
        "theorem NativeExprPreservesWord_lowerExprNative_lit",
        "theorem NativeExprPreservesWord_lowerExprNative_hex",
        "theorem NativeExprPreservesWord_lowerExprNative_str",
        "theorem NativeExprPreservesWord_lowerExprNative_ident",
        "theorem NativeExprPreservesWord_call_prim_of_evalArgs_primCall_preserves",
        "theorem NativeExprPreservesWord_call_prim_of_nativeEvalArgs_primCall_preserves",
        "theorem NativeExprPreservesWord_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves",
        "theorem NativeExprPreservesWord_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves",
        "theorem NativeExprPreservesWord_call_user_of_evalArgs_call_preserves",
        "theorem NativeExprPreservesWord_call_user_of_nativeEvalArgs_call_preserves",
        "theorem NativeExprPreservesWord_lowerExprNative_call_userFunction_of_evalArgs_call_preserves",
        "theorem NativeExprPreservesWord_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_prim_of_evalArgs_primCall_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_user_of_evalArgs_call_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_user_of_nativeEvalArgs_call_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_userFunction_of_evalArgs_call_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_mstore_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_mstore_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_mstore8_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_mstore8_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore8_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore8_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_sstore_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_sstore_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_sstore_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_sstore_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_tstore_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_tstore_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_tstore_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_tstore_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_calldatacopy_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_calldatacopy_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_calldatacopy_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_calldatacopy_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_returndatacopy_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_returndatacopy_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_returndatacopy_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_returndatacopy_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_log0_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_log0_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log0_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log0_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_log1_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_log1_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log1_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log1_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_log2_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_log2_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log2_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log2_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_log3_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_log3_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log3_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log3_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_log4_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_log4_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log4_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log4_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_return_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_return_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_return_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_return_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_revert_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_revert_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_revert_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_revert_of_nativeEvalArgs_and_evalArgs_shape_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_stop",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_stop",
        "theorem nativeStmtWriteNames_not_mem_of_nativeStmtsWriteNames_not_mem",
        "theorem collectNativeStmtWriteNames_append",
        "theorem nativeStmtsWriteNames_append",
        "theorem nativeStmtsWriteNames_cons",
        "theorem nativeStmtsWriteNames_cons_not_mem_iff",
        "theorem nativeStmtsWriteNames_head_not_mem_of_cons_not_mem",
        "theorem nativeStmtsWriteNames_tail_not_mem_of_cons_not_mem",
        "theorem nativeStmtsWriteNames_left_not_mem_of_append_not_mem",
        "theorem nativeStmtsWriteNames_right_not_mem_of_append_not_mem",
        "theorem nativeStmtsWriteNames_append_not_mem_iff",
        "theorem NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem",
        "theorem NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem",
        "theorem NativeBlockPreservesWord_append_of_forall_stmt",
        "theorem NativeBlockPreservesWord_append_of_nativeStmtsWriteNames_not_mem",
        "theorem NativeBlockPreservesWord_append_of_nativeStmtsWriteNames_append_not_mem",
        "theorem NativeStmtPreservesWord_block_of_nativeStmtsWriteNames_not_mem",
        "theorem NativeStmtPreservesWord_if_of_eval_preserves_and_nativeStmtsWriteNames_not_mem",
        "theorem NativeStmtPreservesWord_if_of_cond_preserves_and_nativeStmtsWriteNames_not_mem",
        "theorem NativeBlockPreservesWord_of_nativeSwitchFresh_find_hit_matched",
        "theorem NativeBlockPreservesWord_of_nativeSwitchFresh_find_hit_discr",
        "theorem NativeBlockPreservesWord_of_nativeSwitchFresh_default_matched",
        "theorem NativeBlockPreservesWord_of_nativeSwitchFresh_default_discr",
        "theorem nativeSwitchTempsFreshForNativeBodies_case_discr_not_mem",
        "theorem nativeSwitchTempsFreshForNativeBodies_find_hit_discr_not_mem",
        "theorem nativeSwitchTempsFreshForNativeBodies_default_discr_not_mem",
        "theorem exec_nativeSwitchTail_find_hit_fresh_fuel",
        "theorem exec_lowerNativeSwitchBlock_selector_find_hit_fresh_fuel",
        "theorem exec_lowerNativeSwitchBlock_storePrefix_tail_ok_fuel",
        "theorem exec_lowerNativeSwitchBlock_selector_find_hit_preserved_store_fuel",
        "theorem exec_lowerNativeSwitchBlock_selector_find_hit_fresh_store_fuel",
        "theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_fresh",
    ):
        if required_native_entrypoint not in normalized_native_harness:
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/"
                "EvmYulLeanNativeHarness.lean is missing native harness surface "
                f"`{required_native_entrypoint}`"
            )

    return errors


def check_native_switch_lowering_boundary(native_adapter_text: str, native_smoke_text: str) -> list[str]:
    """Keep native switch lowering fresh and regression-tested."""

    errors: list[str] = []
    normalized_adapter = normalize_ws(native_adapter_text)
    normalized_smoke = normalize_ws(native_smoke_text)

    for required_boundary in (
        "freshNativeSwitchId",
        "nativeSwitchDiscrTempName",
        "nativeSwitchMatchedTempName",
        "yulStmtsIdentifierNames",
    ):
        if required_boundary not in normalized_adapter:
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/"
                "EvmYulLeanAdapter.lean must keep native switch temporary "
                f"freshness explicit with `{required_boundary}`"
            )

    for required_smoke in (
        "nativeSwitchTempNamesAvoidUserNames = true",
        "nativeFunctionSwitchTempNamesAvoidLocalUserNames = true",
        "nativeSwitchExecutesOnlyFirstMatchingNonHaltingCase = true",
        "emittedRuntimeSatisfiesGeneratedNativeFragment = true",
        "duplicateHelpersRejectedByGeneratedNativeFragment = true",
        "nestedDispatcherFuncDefRejectedByGeneratedNativeFragment = true",
        "nestedHelperFuncDefRejectedByGeneratedNativeFragment = true",
        "nativeRuntimeFragmentGateRejectsDuplicateHelper = true",
        "nativeIRRuntimeFragmentGateRejectsDuplicateHelper = true",
    ):
        if required_smoke not in normalized_smoke:
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/"
                "EvmYulLeanNativeSmokeTest.lean must pin native switch "
                f"lowering behavior with `{required_smoke}`"
            )

    return errors


def check_default_builtin_backend(builtins_text: str) -> list[str]:
    """Pin the public default backend to EVMYulLean.

    The legacy Verity backend remains available through `legacyBuiltinBackend`
    for reference-oracle comparisons, but unqualified builtin evaluation must
    not silently drift back to that backend.
    """

    errors: list[str] = []
    normalized = normalize_ws(builtins_text)
    required = (
        "abbrev defaultBuiltinBackend : BuiltinBackend := .evmYulLean",
        "theorem defaultBuiltinBackend_eq_evmYulLean",
    )
    for snippet in required:
        if normalize_ws(snippet) not in normalized:
            errors.append(
                "Compiler/Proofs/YulGeneration/ReferenceOracle/Builtins.lean "
                f"must pin the public default builtin backend with `{snippet}`"
            )
    return errors


def check_reference_oracle_names(
    end_to_end_text: str, retarget_text: str, preservation_text: str
) -> list[str]:
    """Keep legacy Layer-3 reference-oracle entry points explicitly named."""

    errors: list[str] = []
    normalized_end_to_end = normalize_ws(end_to_end_text)
    normalized_retarget = normalize_ws(retarget_text)
    normalized_preservation = normalize_ws(preservation_text)

    if re.search(r"\btheorem\s+yulCodegen_preserves_semantics(?!_)", preservation_text):
        errors.append(
            "Compiler/Proofs/YulGeneration/Preservation.lean must not expose the "
            "legacy reference-oracle theorem as bare `yulCodegen_preserves_semantics`; "
            "use `yulCodegen_preserves_semantics_via_reference_oracle`"
        )

    if "theorem yulCodegen_preserves_semantics_via_reference_oracle" not in normalized_preservation:
        errors.append(
            "Compiler/Proofs/YulGeneration/Preservation.lean must keep the legacy "
            "Layer-3 oracle theorem explicitly named "
            "`yulCodegen_preserves_semantics_via_reference_oracle`"
        )

    if "yulCodegen_preserves_semantics_via_reference_oracle" not in normalized_retarget:
        errors.append(
            "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanRetarget.lean must "
            "make the temporary legacy Layer-3 dependency explicit by invoking "
            "`yulCodegen_preserves_semantics_via_reference_oracle`"
        )

    if "theorem yulCodegen_preserves_semantics_evmYulLeanBackend" not in normalized_retarget:
        errors.append(
            "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanRetarget.lean must "
            "name the current EVMYulLean Layer-3 retarget as "
            "`yulCodegen_preserves_semantics_evmYulLeanBackend`"
        )

    if "theorem yulCodegen_preserves_semantics_evmYulLeanBackend_via_reference_oracle" not in normalized_retarget:
        errors.append(
            "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanRetarget.lean must "
            "keep the legacy compatibility alias explicitly named "
            "`yulCodegen_preserves_semantics_evmYulLeanBackend_via_reference_oracle`"
        )

    if "theorem yulCodegen_preserves_semantics_evmYulLean " in normalized_retarget:
        errors.append(
            "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanRetarget.lean must "
            "not reintroduce the hidden reference-oracle compatibility alias "
            "`yulCodegen_preserves_semantics_evmYulLean`; use the explicit "
            "`yulCodegen_preserves_semantics_evmYulLeanBackend_via_reference_oracle` name"
        )

    if "theorem yulCodegen_preserves_semantics_evmYulLean_via_reference_oracle " in normalized_retarget:
        errors.append(
            "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanRetarget.lean must "
            "not reintroduce the hidden default-fuel compatibility alias "
            "`yulCodegen_preserves_semantics_evmYulLean_via_reference_oracle`; "
            "use the explicit "
            "`yulCodegen_preserves_semantics_evmYulLeanBackend_via_reference_oracle` name"
        )

    if "yulCodegen_preserves_semantics_evmYulLeanBackend_via_reference_oracle" in normalized_end_to_end:
        errors.append(
            "Compiler/Proofs/EndToEnd.lean must not mention the legacy "
            "compatibility alias "
            "`yulCodegen_preserves_semantics_evmYulLeanBackend_via_reference_oracle`"
        )

    for removed_native_reference_alias in (
        "theorem layer3_contract_preserves_semantics_native_via_reference_oracle_of_evmYulLean_bridge",
        "theorem layers2_3_ir_matches_native_evmYulLean_via_reference_oracle_of_evmYulLean_bridge",
    ):
        if removed_native_reference_alias in normalized_end_to_end:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must not reintroduce the removed "
                "generic native reference-oracle/fuel-wrapper seam "
                f"`{removed_native_reference_alias.removeprefix('theorem ')}`"
            )

    return errors


def check_native_alias_signatures(end_to_end_text: str) -> list[str]:
    """Reject hidden native dispatcher fuel-wrapper aliases in theorem signatures."""

    errors: list[str] = []
    theorem_pattern = re.compile(
        r"^\s*theorem\s+([A-Za-z0-9_']+)\b(.*?)(?=\s:=)",
        re.DOTALL | re.MULTILINE,
    )
    hidden_dispatcher_alias = re.compile(
        r"\bnative(?:CallDispatcher|DispatcherBlock|DispatcherExec)"
        r"AgreesWithEvmYulLean(?:Positive)?\b"
    )

    for match in theorem_pattern.finditer(end_to_end_text):
        name = match.group(1)
        signature = match.group(2)
        hidden_matches = sorted(set(hidden_dispatcher_alias.findall(signature)))
        if hidden_matches:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean theorem "
                f"`{name}` must expose explicit fuel-wrapper predicates instead "
                "of hidden native dispatcher aliases: "
                + ", ".join(f"`{hidden}`" for hidden in hidden_matches)
            )

    return errors


def check_unbridged_environment_boundary(native_harness_text: str, native_smoke_text: str) -> list[str]:
    """Keep the native environment-read limitation explicit and tested.

    EVMYulLean currently evaluates `CHAINID` from its own global constant, and
    `BLOBBASEFEE` from the block-header blob gas price formula. The native
    harness does not yet derive those fields from Verity's `YulTransaction`.
    Until that bridge is widened, the transition must keep both the named lemma
    and executable smoke expectations for the current default behavior.
    """

    errors: list[str] = []
    normalized_native_harness = normalize_ws(native_harness_text)
    normalized_native_smoke = normalize_ws(native_smoke_text)

    for required_boundary in (
        "validateNativeRuntimeEnvironment",
        "nativeRuntimePathUsesBuiltin",
        "yulStmtsUseBuiltinOnNativeRuntimePath",
        "selectedSwitchBody",
        "nativeChainIdRepresentable",
        "nativeBlobBaseFeeRepresentable",
        "unsupportedNativeHeaderBuiltinNames",
        "nativeRuntimePathUsesUnsupportedHeaderBuiltin",
        "unsupportedNativeHeaderBuiltinError",
        "initialState_unbridgedEnvironmentDefaults",
        "EvmYul.State.chainId",
        "EvmYul.chainId",
        "header.blobGasUsed",
        "header.excessBlobGas",
    ):
        if required_boundary not in normalized_native_harness:
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/"
                "EvmYulLeanNativeHarness.lean must keep the unbridged "
                f"environment boundary explicit with `{required_boundary}`"
            )

    for pinned_default in (
        'nativeRejectsUnsupportedChainId = true',
        'nativeStoresBuiltinWithTx "chainid" 15 EvmYul.chainId',
        'nativeRejectsUnsupportedBlobBaseFee = true',
        'nativeStoresBuiltinWithTx "blobbasefee" 16 EvmYul.MIN_BASE_FEE_PER_BLOB_GAS',
        'nativeRejectsUnsupportedHeaderBuiltin "coinbase" = true',
        'nativeRejectsUnsupportedHeaderBuiltin "gaslimit" = true',
        'nativeAllowsUnselectedUnsupportedEnvironmentBuiltin = true',
    ):
        if pinned_default not in normalized_native_smoke:
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/"
                "EvmYulLeanNativeSmokeTest.lean must pin the current native "
                f"environment behavior with `{pinned_default}` until "
                "the blobbasefee bridge is widened"
            )

    return errors


def main() -> int:
    if not DOC.exists():
        print(f"Missing: {DOC.relative_to(ROOT)}", file=sys.stderr)
        return 1
    if not DOD_DOC.exists():
        print(f"Missing: {DOD_DOC.relative_to(ROOT)}", file=sys.stderr)
        return 1
    for path in (
        END_TO_END,
        NATIVE_HARNESS,
        RETARGET,
        BUILTINS,
        PRESERVATION,
        NATIVE_ADAPTER,
        NATIVE_SMOKE_TEST,
    ):
        if not path.exists():
            print(f"Missing: {path.relative_to(ROOT)}", file=sys.stderr)
            return 1

    native_harness_text = NATIVE_HARNESS.read_text(encoding="utf-8")
    native_smoke_text = NATIVE_SMOKE_TEST.read_text(encoding="utf-8")
    errors = check_doc(DOC.read_text(encoding="utf-8"))
    errors.extend(
        check_definition_of_done_doc(DOD_DOC.read_text(encoding="utf-8"))
    )
    errors.extend(
        check_public_theorem_target(
            END_TO_END.read_text(encoding="utf-8"),
            native_harness_text,
            RETARGET.read_text(encoding="utf-8"),
        )
    )
    errors.extend(
        check_default_builtin_backend(BUILTINS.read_text(encoding="utf-8"))
    )
    errors.extend(
        check_reference_oracle_names(
            END_TO_END.read_text(encoding="utf-8"),
            RETARGET.read_text(encoding="utf-8"),
            PRESERVATION.read_text(encoding="utf-8"),
        )
    )
    errors.extend(
        check_native_alias_signatures(END_TO_END.read_text(encoding="utf-8"))
    )
    errors.extend(
        check_unbridged_environment_boundary(
            native_harness_text,
            native_smoke_text,
        )
    )
    errors.extend(
        check_native_switch_lowering_boundary(
            NATIVE_ADAPTER.read_text(encoding="utf-8"),
            native_smoke_text,
        )
    )
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    print("native EVMYulLean transition doc check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
