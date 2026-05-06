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
ROOT_COMPILER = ROOT / "Compiler.lean"
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
BRIDGE_PREDICATES = (
    ROOT
    / "Compiler"
    / "Proofs"
    / "YulGeneration"
    / "Backends"
    / "EvmYulLeanBridgePredicates.lean"
)
BRIDGE_LEMMAS = (
    ROOT
    / "Compiler"
    / "Proofs"
    / "YulGeneration"
    / "Backends"
    / "EvmYulLeanBridgeLemmas.lean"
)
ADAPTER_CORRECTNESS = (
    ROOT
    / "Compiler"
    / "Proofs"
    / "YulGeneration"
    / "Backends"
    / "EvmYulLeanAdapterCorrectness.lean"
)
BODY_CLOSURE = (
    ROOT
    / "Compiler"
    / "Proofs"
    / "YulGeneration"
    / "Backends"
    / "EvmYulLeanBodyClosure.lean"
)
SOURCE_EXPR_CLOSURE = (
    ROOT
    / "Compiler"
    / "Proofs"
    / "YulGeneration"
    / "Backends"
    / "EvmYulLeanSourceExprClosure.lean"
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
RUNTIME_TYPES = ROOT / "Compiler" / "Proofs" / "YulGeneration" / "RuntimeTypes.lean"
LEGACY_PROOF_MODULES = (
    "Compiler.Proofs.YulGeneration.Codegen",
    "Compiler.Proofs.YulGeneration.Equivalence",
    "Compiler.Proofs.YulGeneration.StatementEquivalence",
    "Compiler.Proofs.YulGeneration.Preservation",
    "Compiler.Proofs.YulGeneration.Lemmas",
)
TRANSITION_ONLY_PUBLIC_FORBIDDEN_MODULES = LEGACY_PROOF_MODULES + (
    "Compiler.Proofs.YulGeneration.Backends.EvmYulLeanRetarget",
    "Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas",
)
BRIDGE_LEMMAS_IMPORT_ALLOWLIST = (
    "PrintAxioms.lean",
    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeTest.lean",
    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanRetarget.lean",
)
REFERENCE_ORACLE_IMPORT_ALLOWLIST = (
    "PrintAxioms.lean",
    "Compiler/Proofs/YulGeneration/ReferenceOracle/Semantics.lean",
    "Compiler/Proofs/YulGeneration/Codegen.lean",
    "Compiler/Proofs/YulGeneration/Equivalence.lean",
    "Compiler/Proofs/YulGeneration/Lemmas.lean",
    "Compiler/Proofs/YulGeneration/Preservation.lean",
    "Compiler/Proofs/YulGeneration/StatementEquivalence.lean",
    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanAdapterCorrectness.lean",
    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean",
    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeTest.lean",
    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeDispatchOracleTest.lean",
    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeSmokeTest.lean",
    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanRetarget.lean",
    "Contracts/MacroTranslateInvariantTest.lean",
    "Contracts/MacroTranslateRoundTripFuzz.lean",
)
LEGACY_PROOF_FILES = (
    ROOT / "Compiler" / "Proofs" / "YulGeneration" / "Codegen.lean",
    ROOT / "Compiler" / "Proofs" / "YulGeneration" / "Equivalence.lean",
    ROOT / "Compiler" / "Proofs" / "YulGeneration" / "StatementEquivalence.lean",
    ROOT / "Compiler" / "Proofs" / "YulGeneration" / "Preservation.lean",
    ROOT / "Compiler" / "Proofs" / "YulGeneration" / "Lemmas.lean",
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
    "nativeGeneratedCallDispatcherResultOf",
    "nativeGeneratedCallDispatcherMatchesIROn",
    "compile_preserves_native_evmYulLean_callDispatcher_of_generated_callDispatcher_match",
    "compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_noMapping",
    "compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_mapping",
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


def theorem_signature(text: str, theorem_name: str) -> str:
    """Return the theorem statement through its `:= by` proof delimiter."""

    match = re.search(
        r"^\s*theorem\s+" + re.escape(theorem_name) + r"\b",
        text,
        re.MULTILINE,
    )
    if match is None:
        return ""
    proof_start = text.find(":= by", match.start())
    if proof_start < 0:
        return text[match.start() :]
    return text[match.start() : proof_start]


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

    if "evalBuiltinCall" in end_to_end_text:
        errors.append(
            "Compiler/Proofs/EndToEnd.lean must not directly mention legacy "
            "builtin-dispatch wrapper `evalBuiltinCall`; keep those notes and "
            "dependencies below the public EndToEnd surface"
        )

    for required_native_surface in (
        "def nativeResultsMatch",
        "def nativeResultsMatchOn",
        "theorem validateNativeRuntimeEnvironment_ofIR_representableEnvironment",
        "theorem validateNativeRuntimeEnvironment_ofIR_globalDefaults",
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

    for required_end_to_end_native_surface in (
        "def nativeIRRuntimeMatchesIR",
        "def nativeDispatcherExecMatchesIRPositive",
        "theorem nativeIRRuntimeMatchesIR_of_generated_lowered_dispatcherExec_positive_match",
        "theorem nativeDispatcherExecMatchesIRPositive_of_project_eq_match",
        "theorem nativeIRRuntimeMatchesIR_of_generated_lowered_dispatcherExec_project_eq_match",
        "theorem nativeDispatcherExecMatchesIRPositive_of_exec_yulHalt_project_eq_match",
        "theorem nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match",
    ):
        if required_end_to_end_native_surface not in normalized_end_to_end:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must own the native-vs-IR "
                "comparison surface "
                f"`{required_end_to_end_native_surface}` after the native "
                "harness was split away from the full IR interpreter"
            )

    for required_native_seam in (
        "def nativeGeneratedCallDispatcherResultOf",
        "def nativeGeneratedCallDispatcherMatchesIROn",
        "theorem compile_preserves_native_evmYulLean_callDispatcher_of_generated_callDispatcher_match",
        "theorem compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_noMapping",
        "theorem compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_mapping",
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
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_globalDefaults",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_globalDefaults_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_environment",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_environment_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_globalDefaults",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_globalDefaults_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_mapping_reserved",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_mapping_reserved_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_environment",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_environment_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_globalDefaults_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_mapping_reserved",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_mapping_reserved_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_environment",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_environment_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_globalDefaults_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_project_body_closure_noMapping",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_project_body_closure_noMapping_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_mapping_reserved",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_mapping_reserved_canonicalFuel",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_project_body_closure_mapping_reserved",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_project_body_closure_mapping_reserved_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_generated_dispatcherExec_positive_match",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_positive_external_bodies_match",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_positive_body_closure",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_positive_body_closure_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_project_external_bodies_match",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_project_body_closure",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_project_body_closure_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_globalDefaults",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_globalDefaults_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_environment",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_environment_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_globalDefaults",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_globalDefaults_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_environment",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_environment_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_globalDefaults_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_environment",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_environment_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_globalDefaults_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_project_body_closure_noMapping",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_project_body_closure_noMapping_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_mapping_reserved",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_mapping_reserved_canonicalFuel",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_project_body_closure_mapping_reserved",
        "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_project_body_closure_mapping_reserved_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_external_bodies_match",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_match",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure_ofIR_environment_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure_ofIR_globalDefaults_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_globalDefaults_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_external_bodies_match",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_match",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_ofIR_environment_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_ofIR_globalDefaults_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_environment_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_project_body_closure_noMapping_ofIR_globalDefaults_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_environment_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_globalDefaults_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_environment_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_globalDefaults_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_noMapping",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_noMapping_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_mapping_reserved",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_mapping_reserved_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_mapping_reserved",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_mapping_reserved_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_ofIR_globalDefaults_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_noMapping_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_noMapping_ofIR_environment_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_noMapping_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_noMapping_ofIR_globalDefaults_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_environment_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_globalDefaults_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_environment",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_environment_canonicalFuel",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_globalDefaults",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_project_body_closure_mapping_reserved_ofIR_globalDefaults_canonicalFuel",
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

    for public_call_dispatcher_theorem in (
        "compile_preserves_native_evmYulLean_callDispatcher_of_generated_callDispatcher_match",
        "compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_noMapping",
        "compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_mapping",
    ):
        signature = theorem_signature(end_to_end_text, public_call_dispatcher_theorem)
        if "nativeGeneratedCallDispatcherResultOf" not in signature:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean public generated "
                f"`{public_call_dispatcher_theorem}` theorem must conclude "
                "the direct projected `EvmYul.Yul.callDispatcher` result via "
                "`nativeGeneratedCallDispatcherResultOf`, not the thin runtime adapter"
            )
        if "interpretIRRuntimeNative" in signature:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean public generated "
                f"`{public_call_dispatcher_theorem}` theorem must not expose "
                "`interpretIRRuntimeNative` as its public result target"
            )

    if re.search(
        r"^\s*theorem\s+compile_preserves_native_evmYulLean_of_nativeResultsMatchOn\b",
        end_to_end_text,
        re.MULTILINE,
    ):
        errors.append(
            "Compiler/Proofs/EndToEnd.lean must keep the generic "
            "`compile_preserves_native_evmYulLean_of_nativeResultsMatchOn` "
            "adapter theorem file-local; public compiler correctness should "
            "target explicit native result values"
        )

    for dispatcher_exec_public_seam in (
        "def nativeGeneratedDispatcherExecMatchesIROn",
        "theorem compile_preserves_native_evmYulLean_of_generated_dispatcherExec_match",
        "theorem compile_preserves_native_evmYulLean_of_lowered_generated_dispatcher_noMapping",
        "theorem compile_preserves_native_evmYulLean_of_lowered_generated_dispatcher_mapping",
    ):
        if re.search(
            r"^\s*" + re.escape(dispatcher_exec_public_seam) + r"\b",
            end_to_end_text,
            re.MULTILINE,
        ):
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must keep dispatcher-exec "
                "compatibility seams private; public generated correctness "
                "must expose `EvmYul.Yul.callDispatcher` rather than "
                f"`{dispatcher_exec_public_seam}`"
            )

    for removed_transition_seam in (
        "layer3_contract_preserves_semantics_evmYulLeanBackend_with_function_bridge",
        "layer3_contract_preserves_semantics_evmYulLeanBackend",
        "layer3_contract_preserves_semantics_native_of_evmYulLean_bridge",
        "layers2_3_ir_matches_yul_evmYulLeanBackend_with_function_bridge",
        "layers2_3_ir_matches_yul_evmYulLeanBackend",
        "layers2_3_ir_matches_native_evmYulLean_of_evmYulLean_bridge",
        "compile_preserves_native_evmYulLean_of_generated_dispatcherExec_match",
        "compile_preserves_native_evmYulLean_of_generated_callDispatcher_match",
        "compile_preserves_native_evmYulLean_of_lowered_generated_dispatcher_noMapping",
        "compile_preserves_native_evmYulLean_of_lowered_generated_dispatcher_mapping",
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

    for private_simple_storage_scaffold in (
        "simpleStorageNativeDispatcherStmts",
        "simpleStorageNativeDispatcherInnerStmts",
        "simpleStorageNativeDispatcher_letValue",
        "simpleStorageNativeDispatcher_if1Cond",
        "simpleStorageNativeDispatcher_if1Body",
        "simpleStorageNativeDispatcher_if2Cond",
        "simpleStorageNativeDispatcher_if2Body",
        "simpleStorageNativeDispatcherFuel",
    ):
        if re.search(
            r"^\s*(?:noncomputable\s+)?def\s+"
            + re.escape(private_simple_storage_scaffold)
            + r"\b",
            end_to_end_text,
            re.MULTILINE,
        ):
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must keep SimpleStorage native "
                "dispatcher proof scaffolding file-local; do not export "
                f"`{private_simple_storage_scaffold}`"
            )

    if re.search(
        r"^\s*def\s+SourceBodyNativeClosure\b",
        end_to_end_text,
        re.MULTILINE,
    ):
        errors.append(
            "Compiler/Proofs/EndToEnd.lean must keep "
            "`SourceBodyNativeClosure` file-local; public callDispatcher "
            "theorems should not export body-closure proof scaffolding"
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

    simple_storage_native_name = "simpleStorage_endToEnd_native_evmYulLean"
    simple_storage_native_signature = theorem_signature(
        end_to_end_text,
        simple_storage_native_name,
    )
    simple_storage_native_marker = f"theorem {simple_storage_native_name} "
    simple_storage_native_start = normalized_end_to_end.find(simple_storage_native_marker)
    if simple_storage_native_start < 0 or not simple_storage_native_signature:
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
            "nativeGeneratedCallDispatcherResultOf",
            "simpleStorageNativeCallDispatcherMatchBridge_of_per_case",
        ):
            if required_direct_target not in simple_storage_native_span:
                errors.append(
                    "Compiler/Proofs/EndToEnd.lean public native SimpleStorage "
                    "theorem must consume the direct native callDispatcher "
                    f"target `{required_direct_target}`"
                )
        if "nativeGeneratedCallDispatcherResultOf" not in simple_storage_native_signature:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean public native SimpleStorage "
                "theorem signature must target direct projected "
                "`nativeGeneratedCallDispatcherResultOf` execution"
            )
        for forbidden_compat_target in (
            "interpretIRRuntimeNative",
            "simpleStorage_endToEnd_native_evmYulLean_interpretIRRuntimeNative",
            "simpleStorage_endToEnd_native_evmYulLean_of_lowered_runtime_dispatcherStmts_match",
            "simpleStorage_endToEnd_native_evmYulLean_of_positive_dispatcherExec_bridge",
            "simpleStorageNativeCallDispatcherBridge_of_per_case",
        ):
            if (
                forbidden_compat_target in simple_storage_native_span
                or forbidden_compat_target in simple_storage_native_signature
            ):
                errors.append(
                    "Compiler/Proofs/EndToEnd.lean public native SimpleStorage "
                    "theorem must not consume the compatibility dispatcher "
                    f"bridge `{forbidden_compat_target}`"
                )

    for required_fuel_surface in (
        "private def execYulFuelWithBackend",
        "private noncomputable def interpretYulRuntimeWithBackend",
    ):
        if required_fuel_surface not in normalized_retarget:
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/"
                "EvmYulLeanRetarget.lean must keep the backend-parameterized "
                f"EVMYulLean interpreter surface `{required_fuel_surface}` "
                "explicit but private"
            )

    for public_fuel_surface in (
        "backends_agree_on_bridged_builtins",
        "evalYulExprWithBackend_eq_on_bridged",
        "evalYulExpr_evmYulLean_eq_on_bridged",
        "bridgedExpr_selectorExpr",
        "evalYulExprWithBackend_evmYulLean_selectorExpr_semantics",
        "execYulFuelWithBackend",
        "execYulFuelWithBackend_verity_eq",
        "execYulFuelWithBackend_let_eq_on_bridged",
        "execYulFuelWithBackend_assign_eq_on_bridged",
        "execYulFuelWithBackend_eq_on_bridged_straight_stmts",
        "execYulFuelWithBackend_block_eq_on_bridged_straight_stmts",
        "execYulFuelWithBackend_if_eq_on_bridged_body",
        "execYulFuelWithBackend_switch_eq_on_bridged_cases",
        "execYulFuelWithBackend_for_eq_on_bridged_parts",
        "execYulFuelWithBackend_eq_on_bridged_target",
        "execYulFuelWithBackend_eq_on_bridged_stmt",
        "execYulFuelWithBackend_eq_on_bridged_stmts",
        "emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies",
        "execYulStmtsWithBackend",
        "interpretYulRuntimeWithBackend",
        "interpretYulRuntimeWithBackend_verity_eq",
        "interpretYulFromIR_evmYulLean_eq_on_bridged_bodies",
    ):
        if re.search(
            r"^\s*(?:noncomputable\s+)?(?:def|theorem)\s+"
            + re.escape(public_fuel_surface)
            + r"\b",
            retarget_text,
            re.MULTILINE,
        ):
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanRetarget.lean "
                "must keep backend-interpreter transition surface "
                f"`{public_fuel_surface}` private"
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
    """Pin the file-local default backend to EVMYulLean.

    The backend aliases are transition/reference-oracle helpers, not public
    proof authority. Keep them private while ensuring unqualified builtin
    evaluation does not silently drift back to the Verity backend.
    """

    errors: list[str] = []
    normalized = normalize_ws(builtins_text)
    required = (
        "private abbrev legacyBuiltinBackend : BuiltinBackend := .verity",
        "private abbrev defaultBuiltinBackend : BuiltinBackend := .evmYulLean",
        "private def evalBuiltinCall",
        "theorem defaultBuiltinBackend_eq_evmYulLean",
    )
    for snippet in required:
        if normalize_ws(snippet) not in normalized:
            errors.append(
                "Compiler/Proofs/YulGeneration/ReferenceOracle/Builtins.lean "
                "must pin private reference-oracle/default builtin backend "
                f"aliases with `{snippet}`"
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

    if "private theorem yulCodegen_preserves_semantics_via_reference_oracle" not in normalized_preservation:
        errors.append(
            "Compiler/Proofs/YulGeneration/Preservation.lean must keep the legacy "
            "Layer-3 oracle theorem explicitly named but private "
            "`yulCodegen_preserves_semantics_via_reference_oracle`"
        )

    if re.search(
        r"^\s*theorem\s+yulCodegen_preserves_semantics_via_reference_oracle\b",
        preservation_text,
        re.MULTILINE,
    ):
        errors.append(
            "Compiler/Proofs/YulGeneration/Preservation.lean must not expose "
            "`yulCodegen_preserves_semantics_via_reference_oracle` as public "
            "proof authority"
        )

    if "yulCodegen_preserves_semantics_via_reference_oracle" in normalized_retarget:
        errors.append(
            "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanRetarget.lean must "
            "not invoke the private legacy Layer-3 oracle theorem "
            "`yulCodegen_preserves_semantics_via_reference_oracle`"
        )

    for public_legacy_retarget in (
        "yulCodegen_preserves_semantics_evmYulLeanBackend",
        "yulCodegen_preserves_semantics_evmYulLeanBackend_via_reference_oracle",
    ):
        if re.search(
            r"^\s*(?:private\s+)?theorem\s+"
            + re.escape(public_legacy_retarget)
            + r"\b",
            retarget_text,
            re.MULTILINE,
        ):
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanRetarget.lean "
                "must not retain transition-only legacy Layer-3 retarget theorem "
                f"`{public_legacy_retarget}`"
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

    for forbidden_end_to_end_legacy_term in (
        "evalBuiltinCall",
        "legacyEvalBuiltinCallWithContext",
        "legacyBuiltinBackend",
        "Compiler.Proofs.YulGeneration.ReferenceOracle",
        "interpretYulRuntimeWithBackend",
        "execYulFuelWithBackend",
        "defaultBuiltinBackend",
        "BuiltinBackend",
    ):
        if forbidden_end_to_end_legacy_term in end_to_end_text:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must not directly mention "
                "legacy oracle/backend term "
                f"`{forbidden_end_to_end_legacy_term}`; keep those dependencies "
                "isolated below the public EndToEnd surface"
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


def check_legacy_proof_boundary(
    public_boundary_files: list[tuple[str, str]],
    legacy_proof_files: list[tuple[str, str]],
) -> list[str]:
    """Keep transition-only legacy proof modules below the native public path."""

    errors: list[str] = []

    for label, text in public_boundary_files:
        for module in TRANSITION_ONLY_PUBLIC_FORBIDDEN_MODULES:
            import_line = f"import {module}"
            if import_line in text:
                errors.append(
                    f"{label} must not import transition-only legacy proof "
                    f"module `{module}`"
                )
        if "import Compiler.Proofs.YulGeneration.ReferenceOracle" in text:
            errors.append(
                f"{label} must not import legacy ReferenceOracle modules; "
                "keep the custom Yul interpreter below the native public path"
            )

    public_decl_pattern = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)*"
        r"(?!(?:private|namespace|end|open|section|variable|include|omit|attribute)\b)"
        r"(def|theorem|lemma|abbrev|inductive|structure)\s+([A-Za-z0-9_'.]+)\b",
        re.MULTILINE,
    )
    for label, text in legacy_proof_files:
        for match in public_decl_pattern.finditer(text):
            errors.append(
                f"{label} must not expose transition-only legacy declaration "
                f"`{match.group(2)}` as public proof authority"
            )

    return errors


def lean_module_to_path(module: str) -> Path | None:
    path = ROOT / (module.replace(".", "/") + ".lean")
    if path.exists():
        return path
    return None


def lean_imports(text: str) -> list[str]:
    imports: list[str] = []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("import "):
            parts = stripped.split()
            if len(parts) >= 2:
                imports.append(parts[1])
    return imports


def check_transition_only_import_allowlist(
    lean_files: list[tuple[str, str]],
) -> list[str]:
    """Keep transition-only ReferenceOracle imports out of new proof modules."""

    errors: list[str] = []
    forbidden_bridge_import = (
        "Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas"
    )
    bridge_allowlist = set(BRIDGE_LEMMAS_IMPORT_ALLOWLIST)
    reference_oracle_import_prefix = (
        "Compiler.Proofs.YulGeneration.ReferenceOracle"
    )
    reference_oracle_allowlist = set(REFERENCE_ORACLE_IMPORT_ALLOWLIST)
    for label, text in lean_files:
        imports = lean_imports(text)
        if label not in bridge_allowlist and forbidden_bridge_import in imports:
            errors.append(
                f"{label} must not import transition-only bridge lemma module "
                f"`{forbidden_bridge_import}`; keep ReferenceOracle bridge evidence "
                "confined to EvmYulLeanRetarget and bridge regression tests"
            )
        if label not in reference_oracle_allowlist:
            for imported in imports:
                if imported == reference_oracle_import_prefix or imported.startswith(
                    reference_oracle_import_prefix + "."
                ):
                    errors.append(
                        f"{label} must not import legacy ReferenceOracle module "
                        f"`{imported}`; keep the custom interpreter confined "
                        "to the known transition and regression-test modules"
                    )
    return errors


def transition_import_scan_files() -> list[Path]:
    files = [ROOT / "PrintAxioms.lean"]
    for directory in (ROOT / "Compiler", ROOT / "Contracts"):
        if directory.exists():
            files.extend(sorted(directory.rglob("*.lean")))
    return files


def check_public_transitive_import_boundary(
    public_boundary_files: list[tuple[str, str]],
) -> list[str]:
    """Reject transitive legacy imports from native public boundary modules."""

    errors: list[str] = []
    forbidden_modules = TRANSITION_ONLY_PUBLIC_FORBIDDEN_MODULES + (
        "Compiler.Proofs.YulGeneration.ReferenceOracle",
    )
    text_overrides = {
        label: text
        for label, text in public_boundary_files
    }

    for label, text in public_boundary_files:
        queue: list[tuple[str, str, list[str]]] = [(label, text, [label])]
        seen_modules: set[str] = set()
        while queue:
            current_label, current_text, chain = queue.pop(0)
            for imported in lean_imports(current_text):
                if any(
                    imported == forbidden or imported.startswith(forbidden + ".")
                    for forbidden in forbidden_modules
                ):
                    errors.append(
                        f"{label} must not transitively import transition-only "
                        f"legacy proof module `{imported}` via "
                        + " -> ".join(chain + [imported])
                    )
                    continue

                if imported in seen_modules:
                    continue
                seen_modules.add(imported)

                imported_path = lean_module_to_path(imported)
                if imported_path is None:
                    continue
                try:
                    imported_relative = imported_path.relative_to(ROOT).as_posix()
                except ValueError:
                    continue
                if not imported_relative.startswith("Compiler/"):
                    continue
                imported_text = text_overrides.get(
                    imported_relative,
                    imported_path.read_text(encoding="utf-8"),
                )
                queue.append((imported_relative, imported_text, chain + [imported]))

    return errors


def check_public_transitive_forbidden_terms(
    public_boundary_files: list[tuple[str, str]],
) -> list[str]:
    """Reject legacy proof-interpreter/backend names in public reachable files."""

    errors: list[str] = []
    forbidden_terms = (
        "ReferenceOracle",
        "execYulFuel",
        "interpretYulRuntimeWithBackend",
        ".verity",
        "defaultBuiltinBackend",
        "legacyBuiltinBackend",
        "evalBuiltinCallWithContext",
        "nativeIRRuntimeAgreesWithInterpreter",
    )
    text_overrides = {
        label: text
        for label, text in public_boundary_files
    }

    for label, text in public_boundary_files:
        queue: list[tuple[str, str, list[str]]] = [(label, text, [label])]
        seen_labels: set[str] = set()
        while queue:
            current_label, current_text, chain = queue.pop(0)
            if current_label in seen_labels:
                continue
            seen_labels.add(current_label)

            for forbidden in forbidden_terms:
                if forbidden in current_text:
                    errors.append(
                        f"{label} must not transitively expose legacy "
                        f"proof-interpreter/backend term `{forbidden}` via "
                        + " -> ".join(chain)
                    )

            for imported in lean_imports(current_text):
                imported_path = lean_module_to_path(imported)
                if imported_path is None:
                    continue
                try:
                    imported_relative = imported_path.relative_to(ROOT).as_posix()
                except ValueError:
                    continue
                if not imported_relative.startswith("Compiler/"):
                    continue
                imported_text = text_overrides.get(
                    imported_relative,
                    imported_path.read_text(encoding="utf-8"),
                )
                queue.append((imported_relative, imported_text, chain + [imported]))

    return errors


def check_bridge_lemmas_transition_surface(bridge_lemmas_text: str) -> list[str]:
    """Keep transition-helper bridge rewrites out of the public theorem surface."""

    errors: list[str] = []
    if re.search(
        r"^\s*theorem\s+evalBuiltinCallWithBackendContext_evmYulLean_pure_bridge\b",
        bridge_lemmas_text,
        re.MULTILINE,
    ):
        errors.append(
            "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean "
            "must keep transition-only routing helper "
            "`evalBuiltinCallWithBackendContext_evmYulLean_pure_bridge` private"
        )
    return errors


def check_adapter_correctness_transition_surface(adapter_correctness_text: str) -> list[str]:
    """Keep legacy adapter-correctness rewrites out of the public theorem surface."""

    errors: list[str] = []
    for helper in (
        "assign_equiv_let",
        "assign_equiv_let'",
        "legacyExecYulFuel_stmts_nil",
        "for_init_hoist",
        "for_init_hoist_revert",
        "for_init_hoist_return",
        "for_init_hoist_stop",
    ):
        if re.search(
            r"^\s*(?:@\[[^\]]*\]\s*)*theorem\s+"
            + re.escape(helper)
            + r"\b",
            adapter_correctness_text,
            re.MULTILINE,
        ):
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/"
                "EvmYulLeanAdapterCorrectness.lean must keep transition-only "
                f"adapter correctness helper `{helper}` private"
            )
    return errors


def check_native_closure_import_boundary(
    bridge_predicates_text: str,
    body_closure_text: str,
    source_expr_closure_text: str,
) -> list[str]:
    """Keep native closure predicates isolated from legacy retarget proofs."""

    errors: list[str] = []

    if "import Compiler.Proofs.YulGeneration.ReferenceOracle" in bridge_predicates_text:
        errors.append(
            "Compiler/Proofs/YulGeneration/Backends/"
            "EvmYulLeanBridgePredicates.lean must not import ReferenceOracle; "
            "native closure predicates should remain syntactic"
        )

    if "import Compiler.Proofs.YulGeneration.LogNames" not in bridge_predicates_text:
        errors.append(
            "Compiler/Proofs/YulGeneration/Backends/"
            "EvmYulLeanBridgePredicates.lean must import the neutral "
            "Yul log-name helper"
        )

    if "import Compiler.Proofs.IRGeneration.IRInterpreter" in bridge_predicates_text:
        errors.append(
            "Compiler/Proofs/YulGeneration/Backends/"
            "EvmYulLeanBridgePredicates.lean must not import the full IR "
            "interpreter for log-name predicates"
        )

    for forbidden_predicate_surface in (
        "legacy Yul reference oracle",
        "legacy retarget executor",
        "legacy context evaluator",
        "native and transition backends",
        ".verity",
    ):
        if forbidden_predicate_surface in bridge_predicates_text:
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/"
                "EvmYulLeanBridgePredicates.lean must describe the generated "
                "fragment in native-closure terms, not legacy transition "
                f"authority language `{forbidden_predicate_surface}`"
            )

    for label, text in (
        ("EvmYulLeanBodyClosure.lean", body_closure_text),
        ("EvmYulLeanSourceExprClosure.lean", source_expr_closure_text),
    ):
        if "import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgePredicates" not in text:
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/"
                f"{label} must import the neutral EVMYulLean bridge predicates"
            )
        for forbidden_import in (
            "import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanRetarget",
            "import Compiler.Proofs.YulGeneration.Preservation",
            "import Compiler.Proofs.YulGeneration.ReferenceOracle",
        ):
            if forbidden_import in text:
                errors.append(
                    "Compiler/Proofs/YulGeneration/Backends/"
                    f"{label} must not import legacy transition proof authority "
                    f"`{forbidden_import.removeprefix('import ')}`"
                )

    return errors


def check_runtime_types_import_boundary(runtime_types_text: str) -> list[str]:
    """Keep shared Yul runtime plumbing from importing IR execution semantics."""

    errors: list[str] = []
    if "import Compiler.Proofs.IRGeneration.IRInterpreter" in runtime_types_text:
        errors.append(
            "Compiler/Proofs/YulGeneration/RuntimeTypes.lean must import "
            "IRRuntimeTypes rather than the full IR interpreter"
        )
    if "import Compiler.Proofs.IRGeneration.IRRuntimeTypes" not in runtime_types_text:
        errors.append(
            "Compiler/Proofs/YulGeneration/RuntimeTypes.lean must import the "
            "neutral IR runtime record module"
        )
    return errors


def check_native_harness_import_boundary(native_harness_text: str) -> list[str]:
    """Keep the native harness independent of the full IR interpreter."""

    errors: list[str] = []
    if "import Compiler.Proofs.IRGeneration.IRInterpreter" in native_harness_text:
        errors.append(
            "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean "
            "must consume IRRuntimeTypes records without importing the full IR "
            "interpreter"
        )
    return errors


def check_root_compiler_import_boundary(root_compiler_text: str) -> list[str]:
    """Keep the root aggregate from directly re-exporting broad interpreters."""

    errors: list[str] = []
    if "import Compiler.Proofs.IRGeneration.IRInterpreter" in root_compiler_text:
        errors.append(
            "Compiler.lean must not directly import the full IR interpreter; "
            "import proof modules that own their semantic dependencies instead"
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


def check_public_end_to_end_theorem_signatures(end_to_end_text: str) -> list[str]:
    """Reject legacy oracle/interpreter terms in public EndToEnd theorem APIs."""

    errors: list[str] = []
    theorem_pattern = re.compile(
        r"^\s*theorem\s+([A-Za-z0-9_']+)\b(.*?)(?=\s:=)",
        re.DOTALL | re.MULTILINE,
    )
    forbidden_signature_terms = (
        "ReferenceOracle",
        "execYulFuel",
        "execYulFuelWithBackend",
        "interpretYulRuntimeWithBackend",
        ".verity",
        "defaultBuiltinBackend",
        "legacyBuiltinBackend",
        "evalBuiltinCallWithContext",
        "nativeIRRuntimeAgreesWithInterpreter",
    )
    public_call_dispatcher_theorems = (
        "compile_preserves_native_evmYulLean_callDispatcher_of_generated_callDispatcher_match",
        "compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_noMapping",
        "compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_mapping",
    )
    forbidden_public_call_dispatcher_terms = (
        "SourceBodyNativeClosure",
        "lowerRuntimeContractNative",
        "nativeChainIdRepresentable",
        "nativeBlobBaseFeeRepresentable",
        "nativeRuntimePathUsesUnsupportedHeaderBuiltin",
    )

    for match in theorem_pattern.finditer(end_to_end_text):
        name = match.group(1)
        signature = match.group(2)
        leaked_terms = sorted(
            term for term in forbidden_signature_terms if term in signature
        )
        if leaked_terms:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean theorem "
                f"`{name}` must expose native EVMYulLean theorem parameters "
                "rather than legacy oracle/interpreter terms: "
                + ", ".join(f"`{term}`" for term in leaked_terms)
            )
        if re.search(r"\(\s*fuel'?\s*:\s*Nat\s*\)", signature):
            errors.append(
                "Compiler/Proofs/EndToEnd.lean theorem "
                f"`{name}` must use canonical native generated-runtime fuel "
                "instead of exposing arbitrary theorem-facing fuel"
            )
        if name in public_call_dispatcher_theorems:
            leaked_call_dispatcher_terms = sorted(
                term
                for term in forbidden_public_call_dispatcher_terms
                if term in signature
            )
            if leaked_call_dispatcher_terms:
                errors.append(
                    "Compiler/Proofs/EndToEnd.lean public callDispatcher theorem "
                    f"`{name}` must keep body, full-runtime lowering, and "
                    "native environment-validation obligations below the "
                    "public direct callDispatcher signature: "
                    + ", ".join(
                        f"`{term}`" for term in leaked_call_dispatcher_terms
                    )
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
        ROOT_COMPILER,
        END_TO_END,
        NATIVE_HARNESS,
        RETARGET,
        BRIDGE_PREDICATES,
        BRIDGE_LEMMAS,
        ADAPTER_CORRECTNESS,
        BODY_CLOSURE,
        SOURCE_EXPR_CLOSURE,
        BUILTINS,
        PRESERVATION,
        NATIVE_ADAPTER,
        NATIVE_SMOKE_TEST,
        RUNTIME_TYPES,
        *LEGACY_PROOF_FILES,
    ):
        if not path.exists():
            print(f"Missing: {path.relative_to(ROOT)}", file=sys.stderr)
            return 1

    native_harness_text = NATIVE_HARNESS.read_text(encoding="utf-8")
    native_smoke_text = NATIVE_SMOKE_TEST.read_text(encoding="utf-8")
    runtime_types_text = RUNTIME_TYPES.read_text(encoding="utf-8")
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
        check_native_closure_import_boundary(
            BRIDGE_PREDICATES.read_text(encoding="utf-8"),
            BODY_CLOSURE.read_text(encoding="utf-8"),
            SOURCE_EXPR_CLOSURE.read_text(encoding="utf-8"),
        )
    )
    errors.extend(check_runtime_types_import_boundary(runtime_types_text))
    errors.extend(check_native_harness_import_boundary(native_harness_text))
    errors.extend(
        check_root_compiler_import_boundary(
            ROOT_COMPILER.read_text(encoding="utf-8")
        )
    )
    errors.extend(
        check_legacy_proof_boundary(
            [
                ("Compiler.lean", ROOT_COMPILER.read_text(encoding="utf-8")),
                ("Compiler/Proofs/EndToEnd.lean", END_TO_END.read_text(encoding="utf-8")),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean",
                    native_harness_text,
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanAdapter.lean",
                    NATIVE_ADAPTER.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgePredicates.lean",
                    BRIDGE_PREDICATES.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBodyClosure.lean",
                    BODY_CLOSURE.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanSourceExprClosure.lean",
                    SOURCE_EXPR_CLOSURE.read_text(encoding="utf-8"),
                ),
            ],
            [
                (path.relative_to(ROOT).as_posix(), path.read_text(encoding="utf-8"))
                for path in LEGACY_PROOF_FILES
            ],
        )
    )
    errors.extend(
        check_public_transitive_import_boundary(
            [
                ("Compiler.lean", ROOT_COMPILER.read_text(encoding="utf-8")),
                ("Compiler/Proofs/EndToEnd.lean", END_TO_END.read_text(encoding="utf-8")),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean",
                    native_harness_text,
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanAdapter.lean",
                    NATIVE_ADAPTER.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgePredicates.lean",
                    BRIDGE_PREDICATES.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBodyClosure.lean",
                    BODY_CLOSURE.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanSourceExprClosure.lean",
                    SOURCE_EXPR_CLOSURE.read_text(encoding="utf-8"),
                ),
            ]
        )
    )
    errors.extend(
        check_public_transitive_forbidden_terms(
            [
                ("Compiler.lean", ROOT_COMPILER.read_text(encoding="utf-8")),
                ("Compiler/Proofs/EndToEnd.lean", END_TO_END.read_text(encoding="utf-8")),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean",
                    native_harness_text,
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanAdapter.lean",
                    NATIVE_ADAPTER.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgePredicates.lean",
                    BRIDGE_PREDICATES.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBodyClosure.lean",
                    BODY_CLOSURE.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanSourceExprClosure.lean",
                    SOURCE_EXPR_CLOSURE.read_text(encoding="utf-8"),
                ),
            ]
        )
    )
    errors.extend(
        check_transition_only_import_allowlist(
            [
                (path.relative_to(ROOT).as_posix(), path.read_text(encoding="utf-8"))
                for path in transition_import_scan_files()
            ]
        )
    )
    errors.extend(
        check_bridge_lemmas_transition_surface(
            BRIDGE_LEMMAS.read_text(encoding="utf-8")
        )
    )
    errors.extend(
        check_adapter_correctness_transition_surface(
            ADAPTER_CORRECTNESS.read_text(encoding="utf-8")
        )
    )
    errors.extend(
        check_native_alias_signatures(END_TO_END.read_text(encoding="utf-8"))
    )
    errors.extend(
        check_public_end_to_end_theorem_signatures(
            END_TO_END.read_text(encoding="utf-8")
        )
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
