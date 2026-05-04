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
    "interpretYulRuntimeEvmYulLean",
    "Verity's custom fuel-based Yul statement interpreter",
    "not the final architecture",
    "Native.interpretRuntimeNative",
    "Native.interpretIRRuntimeNative",
    "EvmYul.Yul.callDispatcher",
    "observable storage slot set explicitly",
    "only materializes pre-state storage for those slots",
    "layers2_3_ir_matches_native_evmYulLean_via_reference_oracle_of_evmYulLean_bridge",
    "interpretYulRuntimeEvmYulLeanFuelWrapper",
    "interpretYulRuntimeEvmYulLeanFuelWrapperDefaultFuel",
    "interpretYulRuntimeWithBackendFuel",
    "nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper",
    "nativeIRRuntimeAgreesWithEvmYulLean",
    "nativeResultsMatchOn",
    "nativeCallDispatcherAgreesWithEvmYulLeanFuelWrapper",
    "nativeCallDispatcherAgreesWithEvmYulLean",
    "nativeDispatcherBlockAgreesWithEvmYulLeanFuelWrapper",
    "nativeDispatcherBlockAgreesWithEvmYulLean",
    "nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper",
    "nativeDispatcherExecAgreesWithEvmYulLean",
    "nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapperPositive",
    "nativeDispatcherExecAgreesWithEvmYulLeanPositive",
    "layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_callDispatcher_bridge",
    "explicitly observable final-storage slots",
    "full-storage-projection",
    "same explicit fuel",
    "default runtime fuel",
    "native public theorem pending",
    "not yet proved",
    "`yulCodegen_preserves_semantics_evmYulLean_via_reference_oracle`",
    "`yulCodegen_preserves_semantics_evmYulLeanFuelWrapperDefaultFuel_via_reference_oracle`",
    "compatibility theorem",
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


def check_public_theorem_target(
    end_to_end_text: str, native_harness_text: str, retarget_text: str
) -> list[str]:
    """Pin the current transition boundary until the native theorem flips.

    This guard should be updated in the same PR that proves the native
    preservation theorem and retargets the public EndToEnd path. Until then,
    the public theorem must still visibly target the backend-parameterized
    interpreter, while the native harness remains an executable side path.
    """

    errors: list[str] = []
    normalized_end_to_end = normalize_ws(end_to_end_text)
    normalized_native_harness = normalize_ws(native_harness_text)
    normalized_retarget = normalize_ws(retarget_text)

    if "interpretYulRuntimeEvmYulLeanFuelWrapperDefaultFuel" not in normalized_end_to_end:
        errors.append(
            "Compiler/Proofs/EndToEnd.lean must still expose the current "
            "`interpretYulRuntimeEvmYulLeanFuelWrapperDefaultFuel` public theorem target "
            "until the native preservation theorem is proved and this guard is updated"
        )

    for required_native_seam in (
        "def nativeResultsMatch",
        "def yulResultsAgreeOn",
        "def nativeResultsMatchOn",
        "def nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper",
        "def nativeIRRuntimeAgreesWithEvmYulLean",
        "def nativeCallDispatcherAgreesWithEvmYulLeanFuelWrapper",
        "def nativeCallDispatcherAgreesWithEvmYulLean",
        "def nativeDispatcherBlockAgreesWithEvmYulLeanFuelWrapper",
        "def nativeDispatcherBlockAgreesWithEvmYulLean",
        "def nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper",
        "def nativeDispatcherExecAgreesWithEvmYulLean",
        "def nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapperPositive",
        "def nativeDispatcherExecAgreesWithEvmYulLeanPositive",
        "def nativeDispatcherExecMatchesIRPositive",
        "theorem nativeIRRuntimeMatchesIR_of_lowered_dispatcherExec_positive_match",
        "theorem nativeIRRuntimeMatchesIR_of_generated_lowered_dispatcherExec_positive_match",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_match",
        "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapperPositive_of_exec_ok_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanPositive_of_exec_ok_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapperPositive_of_exec_yulHalt_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanPositive_of_exec_yulHalt_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapperPositive_of_exec_yulHalt_project_eq_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanPositive_of_exec_yulHalt_project_eq_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapperPositive_of_exec_error_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanPositive_of_exec_error_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapperPositive_of_exec_error_project_eq_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanPositive_of_exec_error_project_eq_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper_of_positive",
        "theorem nativeDispatcherExecAgreesWithEvmYulLean_of_positive",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper_of_exec_ok_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLean_of_exec_ok_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper_of_exec_yulHalt_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLean_of_exec_yulHalt_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper_of_exec_error_agree",
        "theorem nativeDispatcherExecAgreesWithEvmYulLean_of_exec_error_agree",
        "theorem nativeDispatcherBlockAgreesWithEvmYulLeanFuelWrapper_of_exec_agree",
        "theorem nativeDispatcherBlockAgreesWithEvmYulLean_of_exec_agree",
        "theorem nativeCallDispatcherAgreesWithEvmYulLeanFuelWrapper_of_dispatcherBlock_agree",
        "theorem nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper_of_lowered_callDispatcher_agree",
        "theorem nativeIRRuntimeAgreesWithEvmYulLean_of_lowered_callDispatcher_agree",
        "def nativeIRRuntimeMatchesIR",
        "theorem nativeIRRuntimeAgreesWithEvmYulLean_of_nativeIRRuntimeMatchesIR",
        "theorem nativeIRRuntimeAgreesWithEvmYulLean_of_ok_nativeResultsMatchOn",
        "theorem nativeDispatcherExecMatchesIRPositive_of_exec_ok_match",
        "theorem nativeDispatcherExecMatchesIRPositive_of_exec_yulHalt_project_eq_match",
        "theorem nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match",
        "interpretYulRuntimeEvmYulLeanFuelWrapper fuel",
        "hFuel : fuel = sizeOf (Compiler.emitYul contract).runtimeCode + 1",
        "theorem layer3_contract_preserves_semantics_native_via_reference_oracle_of_evmYulLean_bridge",
        "theorem layer3_contract_preserves_semantics_native_of_evmYulLean_bridge",
        "theorem layer3_contract_preserves_semantics_native_of_generated_lowered_callDispatcher_bridge",
        "theorem layer3_contract_preserves_semantics_native_of_generated_dispatcherExec_positive_match",
        "theorem layers2_3_ir_matches_native_evmYulLean_via_reference_oracle_of_evmYulLean_bridge",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_evmYulLean_bridge",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_callDispatcher_bridge",
        "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_match",
        "theorem layer3_contract_preserves_semantics ",
        "theorem simpleStorage_endToEnd_native_evmYulLean_of_positive_dispatcherExec_match",
        "theorem simpleStorageNativeCallDispatcherMatchBridge_of_per_case",
        "theorem simpleStorageNativeRetrieveHitMatchBridge_proved",
        "theorem simpleStorageNativeStoreHitMatchBridge_proved",
        "theorem simpleStorageNativeSelectorMissMatchBridge_proved",
        "theorem simpleStorage_endToEnd ",
    ):
        if required_native_seam not in normalized_end_to_end:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must keep the native theorem seam "
                f"`{required_native_seam}` explicit until the generated-fragment "
                "native bridge is discharged"
            )

    direct_native_wrappers = (
        "layer3_contract_preserves_semantics_native_of_evmYulLean_bridge",
        "layers2_3_ir_matches_native_evmYulLean_of_evmYulLean_bridge",
    )
    theorem_pattern = re.compile(
        r"^\s*theorem\s+([A-Za-z0-9_']+)\b(.*?)(?=\s:=)",
        re.DOTALL | re.MULTILINE,
    )
    theorem_signatures = {
        match.group(1): normalize_ws(match.group(2))
        for match in theorem_pattern.finditer(end_to_end_text)
    }
    for wrapper in direct_native_wrappers:
        signature = theorem_signatures.get(wrapper, "")
        if "nativeIRRuntimeMatchesIR" not in signature:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean non-reference native wrapper "
                f"`{wrapper}` must consume `nativeIRRuntimeMatchesIR` directly"
            )
        if "nativeIRRuntimeAgreesWithEvmYulLean " in signature:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean non-reference native wrapper "
                f"`{wrapper}` must not consume the fuel-wrapper compatibility "
                "`nativeIRRuntimeAgreesWithEvmYulLean` obligation"
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
                "use the explicit `_positive_bridge` theorem name"
            )

    for required_reference_oracle_seam in (
        "theorem layer3_contract_preserves_semantics_via_reference_oracle ",
        "theorem simpleStorage_endToEnd_via_reference_oracle ",
    ):
        if required_reference_oracle_seam not in normalized_end_to_end:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean must keep legacy Verity-backed "
                f"entry points explicitly named `{required_reference_oracle_seam.strip()}`"
            )

    public_targets = (
        (
            "theorem layer3_contract_preserves_semantics ",
            "interpretYulRuntimeEvmYulLeanFuelWrapperDefaultFuel",
        ),
        (
            "theorem simpleStorage_endToEnd ",
            "interpretYulRuntimeEvmYulLeanFuelWrapperDefaultFuel",
        ),
    )
    for theorem_marker, target_marker in public_targets:
        start = normalized_end_to_end.find(theorem_marker)
        if start < 0:
            continue
        next_theorem = normalized_end_to_end.find(" theorem ", start + len(theorem_marker))
        theorem_span = (
            normalized_end_to_end[start:]
            if next_theorem < 0
            else normalized_end_to_end[start:next_theorem]
        )
        if target_marker not in theorem_span:
            errors.append(
                f"Compiler/Proofs/EndToEnd.lean public theorem `{theorem_marker.strip()}` "
                f"must target `{target_marker}`, not the legacy reference oracle"
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
            "simpleStorage_endToEnd_native_evmYulLean_of_positive_dispatcherExec_match",
            "simpleStorageNativeCallDispatcherMatchBridge_of_per_case",
        ):
            if required_direct_target not in simple_storage_native_span:
                errors.append(
                    "Compiler/Proofs/EndToEnd.lean public native SimpleStorage "
                    "theorem must consume the direct native-vs-IR dispatcher "
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
        "def interpretYulRuntimeWithBackendFuel",
        "def interpretYulRuntimeEvmYulLeanFuelWrapper",
        "def interpretYulRuntimeEvmYulLeanFuelWrapperDefaultFuel",
        "def interpretYulRuntimeEvmYulLeanFuel",
        "def interpretYulRuntimeEvmYulLean",
        "theorem interpretYulRuntimeWithBackend_eq_fuel",
    ):
        if required_fuel_surface not in normalized_retarget:
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/"
                "EvmYulLeanRetarget.lean must keep the fuel-aligned "
                f"EVMYulLean fuel wrapper surface `{required_fuel_surface}` explicit"
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
        "theorem NativeBlockPreservesWord_singleton",
        "theorem NativeBlockPreservesWord_of_forall_stmt",
        "theorem NativeBlockPreservesWord_of_forall_stmt_write_not_mem",
        "theorem NativeStmtPreservesWord_block",
        "theorem NativeStmtPreservesWord_if_of_eval_self",
        "theorem NativeStmtPreservesWord_if_of_eval_preserves",
        "theorem NativeStmtPreservesWord_if_of_cond_preserves",
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
        "theorem NativeExprPreservesWord_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves",
        "theorem NativeExprPreservesWord_call_user_of_evalArgs_call_preserves",
        "theorem NativeExprPreservesWord_lowerExprNative_call_userFunction_of_evalArgs_call_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_prim_of_evalArgs_primCall_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_user_of_evalArgs_call_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_userFunction_of_evalArgs_call_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_mstore_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_mstore8_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore8_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_sstore_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_sstore_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_tstore_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_tstore_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_calldatacopy_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_calldatacopy_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_returndatacopy_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_returndatacopy_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_log0_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log0_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_log1_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log1_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_log2_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log2_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_log3_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log3_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_log4_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log4_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_return_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_return_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_revert_of_evalArgs_preserves",
        "theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_revert_of_evalArgs_preserves",
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

    if "yulCodegen_preserves_semantics_via_reference_oracle" not in normalized_end_to_end:
        errors.append(
            "Compiler/Proofs/EndToEnd.lean must call the legacy Layer-3 oracle "
            "through `yulCodegen_preserves_semantics_via_reference_oracle`"
        )

    if "yulCodegen_preserves_semantics_via_reference_oracle" not in normalized_retarget:
        errors.append(
            "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanRetarget.lean must "
            "make the temporary legacy Layer-3 dependency explicit by invoking "
            "`yulCodegen_preserves_semantics_via_reference_oracle`"
        )

    if "theorem yulCodegen_preserves_semantics_evmYulLeanFuelWrapperDefaultFuel_via_reference_oracle" not in normalized_retarget:
        errors.append(
            "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanRetarget.lean must "
            "name the current EVMYulLean Layer-3 retarget as "
            "`yulCodegen_preserves_semantics_evmYulLeanFuelWrapperDefaultFuel_via_reference_oracle`"
        )

    if "theorem yulCodegen_preserves_semantics_evmYulLean_via_reference_oracle" not in normalized_retarget:
        errors.append(
            "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanRetarget.lean must "
            "keep the compatibility Layer-3 retarget named "
            "`yulCodegen_preserves_semantics_evmYulLean_via_reference_oracle`"
        )

    if "yulCodegen_preserves_semantics_evmYulLeanFuelWrapperDefaultFuel_via_reference_oracle" not in normalized_end_to_end:
        errors.append(
            "Compiler/Proofs/EndToEnd.lean must call the current EVMYulLean "
            "Layer-3 retarget through "
            "`yulCodegen_preserves_semantics_evmYulLeanFuelWrapperDefaultFuel_via_reference_oracle`"
        )

    if "theorem layer3_contract_preserves_semantics_native_via_reference_oracle_of_evmYulLean_bridge" not in normalized_end_to_end:
        errors.append(
            "Compiler/Proofs/EndToEnd.lean must name the current generic native "
            "Layer-3 seam as "
            "`layer3_contract_preserves_semantics_native_via_reference_oracle_of_evmYulLean_bridge`"
        )

    if "theorem layers2_3_ir_matches_native_evmYulLean_via_reference_oracle_of_evmYulLean_bridge" not in normalized_end_to_end:
        errors.append(
            "Compiler/Proofs/EndToEnd.lean must name the current supported "
            "native EndToEnd seam as "
            "`layers2_3_ir_matches_native_evmYulLean_via_reference_oracle_of_evmYulLean_bridge`"
        )

    return errors


def check_native_alias_signatures(end_to_end_text: str) -> list[str]:
    """Keep public native compatibility wrappers on the public alias surface.

    The explicitly named `...FuelWrapper...` declarations are allowed to expose
    the current fuel-wrapper bridge obligation. The compatibility declarations
    whose theorem names omit `FuelWrapper` should consume and return the
    corresponding public aliases instead of reintroducing raw
    `native...FuelWrapper...` proposition names in their signatures.
    """

    errors: list[str] = []
    theorem_pattern = re.compile(
        r"^\s*theorem\s+([A-Za-z0-9_']+)\b(.*?)(?=\s:=)",
        re.DOTALL | re.MULTILINE,
    )
    raw_native_fuel_wrapper = re.compile(
        r"\bnative[A-Za-z0-9_']*FuelWrapper[A-Za-z0-9_']*\b"
    )

    for match in theorem_pattern.finditer(end_to_end_text):
        name = match.group(1)
        signature = match.group(2)
        if not re.search(r"evmYulLean", name, re.IGNORECASE) or "FuelWrapper" in name:
            continue
        raw_matches = sorted(set(raw_native_fuel_wrapper.findall(signature)))
        if raw_matches:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean compatibility theorem "
                f"`{name}` must expose public native aliases in its signature, "
                "not raw fuel-wrapper bridge predicates: "
                + ", ".join(f"`{raw}`" for raw in raw_matches)
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
