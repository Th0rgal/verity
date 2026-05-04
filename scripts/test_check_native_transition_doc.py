#!/usr/bin/env python3

from __future__ import annotations

import re
import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_native_transition_doc as check


class NativeTransitionDocCheckTests(unittest.TestCase):
    def test_current_doc_passes(self) -> None:
        text = check.DOC.read_text(encoding="utf-8")
        self.assertEqual(check.check_doc(text), [])

    def test_rejects_missing_blocker_issue(self) -> None:
        text = check.DOC.read_text(encoding="utf-8").replace("#1738", "#0000")
        errors = check.check_doc(text)
        self.assertTrue(any("#1738" in error for error in errors), errors)

    def test_rejects_missing_observable_slot_caveat(self) -> None:
        text = check.DOC.read_text(encoding="utf-8").replace(
            "observable storage slot set explicitly",
            "observable storage slot set",
        )
        errors = check.check_doc(text)
        self.assertTrue(any("observable storage slot set explicitly" in error for error in errors), errors)

    def test_rejects_missing_chainid_validation_caveat(self) -> None:
        text = check.DOC.read_text(encoding="utf-8").replace(
            "`YulTransaction.chainId` must match",
            "`YulTransaction.chainIdStatus`",
        )
        errors = check.check_doc(text)
        self.assertTrue(
            any("YulTransaction.chainId" in error for error in errors),
            errors,
        )

    def test_rejects_missing_blobbasefee_validation_caveat(self) -> None:
        text = check.DOC.read_text(encoding="utf-8").replace(
            "`chainid()` and `blobbasefee()` now fail closed on the selected native runtime",
            "`YulTransaction.blobBaseFeeStatus`",
        )
        errors = check.check_doc(text)
        self.assertTrue(
            any("blobbasefee" in error for error in errors),
            errors,
        )

    def test_rejects_authoritative_native_claim(self) -> None:
        text = (
            check.DOC.read_text(encoding="utf-8")
            + "\nNative EVMYulLean is now the authoritative semantic target.\n"
        )
        errors = check.check_doc(text)
        self.assertTrue(any("overstates" in error for error in errors), errors)

    def test_rejects_missing_reference_oracle_retarget_caveat(self) -> None:
        text = check.DOC.read_text(encoding="utf-8").replace(
            "`yulCodegen_preserves_semantics_via_reference_oracle`",
            "`native_yulCodegen_preserves_semantics`",
        )
        errors = check.check_doc(text)
        self.assertTrue(
            any("yulCodegen_preserves_semantics_via_reference_oracle" in error for error in errors),
            errors,
        )

    def test_rejects_missing_explicit_evmyullean_reference_oracle_name(self) -> None:
        text = check.DOC.read_text(encoding="utf-8").replace(
            "`yulCodegen_preserves_semantics_evmYulLean_via_reference_oracle`",
            "`yulCodegen_preserves_semantics_evmYulLean`",
        )
        errors = check.check_doc(text)
        self.assertTrue(
            any(
                "yulCodegen_preserves_semantics_evmYulLean_via_reference_oracle" in error
                for error in errors
            ),
            errors,
        )

    def test_public_theorem_target_guard_accepts_current_transition_shape(self) -> None:
        errors = check.check_public_theorem_target(
            check.END_TO_END.read_text(encoding="utf-8"),
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertEqual(errors, [])

    def test_public_theorem_target_guard_rejects_missing_current_target(self) -> None:
        end_to_end_text = re.sub(
            r"interpretYulRuntimeEvmYulLean",
            "interpretYulRuntimeWithBackend .verity",
            check.END_TO_END.read_text(encoding="utf-8"),
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("interpretYulRuntimeEvmYulLean" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_accepts_native_theorem_seam(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\n-- theorem target: interpretIRRuntimeNative\n"
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertEqual(errors, [])

    def test_public_theorem_target_guard_rejects_missing_native_bridge_obligation(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "nativeIRRuntimeAgreesWithEvmYulLean",
            "nativeRuntimeBridgeObligation",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("nativeIRRuntimeAgreesWithEvmYulLean" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_explicit_fuel_wrapper_obligation(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper",
            "nativeIRRuntimeAgreesWithHiddenFuelWrapper",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_explicit_call_dispatcher_fuel_wrapper(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "nativeCallDispatcherAgreesWithEvmYulLeanFuelWrapper",
            "nativeCallDispatcherAgreesWithHiddenFuelWrapper",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("nativeCallDispatcherAgreesWithEvmYulLeanFuelWrapper" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_explicit_dispatcher_block_fuel_wrapper(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "nativeDispatcherBlockAgreesWithEvmYulLeanFuelWrapper",
            "nativeDispatcherBlockAgreesWithHiddenFuelWrapper",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("nativeDispatcherBlockAgreesWithEvmYulLeanFuelWrapper" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_explicit_dispatcher_exec_fuel_wrapper(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper",
            "nativeDispatcherExecAgreesWithHiddenFuelWrapper",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_low_level_native_target(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\n-- theorem target: EvmYul.Yul.callDispatcher\n"
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(any("callDispatcher" in error for error in errors), errors)

    def test_public_theorem_target_guard_rejects_missing_fuel_aligned_oracle(self) -> None:
        retarget_text = check.RETARGET.read_text(encoding="utf-8").replace(
            "interpretYulRuntimeWithBackendFuel",
            "interpretYulRuntimeWithBackendDefaultFuel",
        )
        errors = check.check_public_theorem_target(
            check.END_TO_END.read_text(encoding="utf-8"),
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            retarget_text,
        )
        self.assertTrue(
            any("interpretYulRuntimeWithBackendFuel" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_explicit_evmyullean_fuel_wrapper(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "interpretYulRuntimeEvmYulLeanFuelWrapper",
            "interpretYulRuntimeEvmYulLeanHiddenFuel",
        )
        retarget_text = check.RETARGET.read_text(encoding="utf-8").replace(
            "interpretYulRuntimeEvmYulLeanFuelWrapper",
            "interpretYulRuntimeEvmYulLeanHiddenFuel",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            retarget_text,
        )
        self.assertTrue(
            any("interpretYulRuntimeEvmYulLeanFuelWrapper" in error for error in errors),
            errors,
        )

    def test_reference_oracle_names_guard_accepts_current_shape(self) -> None:
        errors = check.check_reference_oracle_names(
            check.END_TO_END.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
            check.PRESERVATION.read_text(encoding="utf-8"),
        )
        self.assertEqual(errors, [])

    def test_reference_oracle_names_guard_rejects_bare_legacy_theorem_name(self) -> None:
        preservation_text = check.PRESERVATION.read_text(encoding="utf-8").replace(
            "theorem yulCodegen_preserves_semantics_via_reference_oracle",
            "theorem yulCodegen_preserves_semantics",
        )
        errors = check.check_reference_oracle_names(
            check.END_TO_END.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
            preservation_text,
        )
        self.assertTrue(
            any("bare `yulCodegen_preserves_semantics`" in error for error in errors),
            errors,
        )

    def test_reference_oracle_names_guard_rejects_missing_explicit_evmyullean_retarget(self) -> None:
        retarget_text = check.RETARGET.read_text(encoding="utf-8").replace(
            "theorem yulCodegen_preserves_semantics_evmYulLean_via_reference_oracle",
            "theorem yulCodegen_preserves_semantics_evmYulLean_reference_hidden",
        )
        errors = check.check_reference_oracle_names(
            check.END_TO_END.read_text(encoding="utf-8"),
            retarget_text,
            check.PRESERVATION.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("yulCodegen_preserves_semantics_evmYulLean_via_reference_oracle" in error for error in errors),
            errors,
        )

    def test_reference_oracle_names_guard_rejects_missing_explicit_evmyullean_fuel_wrapper_retarget(self) -> None:
        retarget_text = check.RETARGET.read_text(encoding="utf-8").replace(
            "theorem yulCodegen_preserves_semantics_evmYulLeanFuelWrapperDefaultFuel_via_reference_oracle",
            "theorem yulCodegen_preserves_semantics_evmYulLeanFuelWrapper_reference_hidden",
        )
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "yulCodegen_preserves_semantics_evmYulLeanFuelWrapperDefaultFuel_via_reference_oracle",
            "yulCodegen_preserves_semantics_evmYulLeanFuelWrapper_reference_hidden",
        )
        errors = check.check_reference_oracle_names(
            end_to_end_text,
            retarget_text,
            check.PRESERVATION.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("yulCodegen_preserves_semantics_evmYulLeanFuelWrapperDefaultFuel_via_reference_oracle" in error for error in errors),
            errors,
        )

    def test_reference_oracle_names_guard_rejects_missing_explicit_native_layer3_seam(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "theorem layer3_contract_preserves_semantics_native_via_reference_oracle_of_evmYulLean_bridge",
            "theorem layer3_contract_preserves_semantics_native_reference_hidden",
        )
        errors = check.check_reference_oracle_names(
            end_to_end_text,
            check.RETARGET.read_text(encoding="utf-8"),
            check.PRESERVATION.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("layer3_contract_preserves_semantics_native_via_reference_oracle_of_evmYulLean_bridge" in error for error in errors),
            errors,
        )

    def test_reference_oracle_names_guard_rejects_missing_explicit_native_end_to_end_seam(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "theorem layers2_3_ir_matches_native_evmYulLean_via_reference_oracle_of_evmYulLean_bridge",
            "theorem layers2_3_ir_matches_native_evmYulLean_reference_hidden",
        )
        errors = check.check_reference_oracle_names(
            end_to_end_text,
            check.RETARGET.read_text(encoding="utf-8"),
            check.PRESERVATION.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("layers2_3_ir_matches_native_evmYulLean_via_reference_oracle_of_evmYulLean_bridge" in error for error in errors),
            errors,
        )

    def test_unbridged_environment_boundary_accepts_current_shape(self) -> None:
        errors = check.check_unbridged_environment_boundary(
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.NATIVE_SMOKE_TEST.read_text(encoding="utf-8"),
        )
        self.assertEqual(errors, [])

    def test_unbridged_environment_boundary_rejects_missing_chainid_rejection_pin(self) -> None:
        smoke_text = check.NATIVE_SMOKE_TEST.read_text(encoding="utf-8").replace(
            'nativeRejectsUnsupportedChainId = true',
            'nativeAcceptsUnsupportedChainId = true',
        )
        errors = check.check_unbridged_environment_boundary(
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            smoke_text,
        )
        self.assertTrue(any("chainid" in error.lower() for error in errors), errors)

    def test_unbridged_environment_boundary_rejects_missing_blobbasefee_rejection_pin(self) -> None:
        smoke_text = check.NATIVE_SMOKE_TEST.read_text(encoding="utf-8").replace(
            'nativeRejectsUnsupportedBlobBaseFee = true',
            'nativeAcceptsUnsupportedBlobBaseFee = true',
        )
        errors = check.check_unbridged_environment_boundary(
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            smoke_text,
        )
        self.assertTrue(any("blobbasefee" in error for error in errors), errors)

    def test_native_switch_lowering_boundary_accepts_current_shape(self) -> None:
        errors = check.check_native_switch_lowering_boundary(
            check.NATIVE_ADAPTER.read_text(encoding="utf-8"),
            check.NATIVE_SMOKE_TEST.read_text(encoding="utf-8"),
        )
        self.assertEqual(errors, [])

    def test_native_switch_lowering_boundary_rejects_missing_freshness_helper(self) -> None:
        adapter_text = check.NATIVE_ADAPTER.read_text(encoding="utf-8").replace(
            "freshNativeSwitchId",
            "staleNativeSwitchId",
        )
        errors = check.check_native_switch_lowering_boundary(
            adapter_text,
            check.NATIVE_SMOKE_TEST.read_text(encoding="utf-8"),
        )
        self.assertTrue(any("freshNativeSwitchId" in error for error in errors), errors)

    def test_native_switch_lowering_boundary_rejects_missing_collision_smoke(self) -> None:
        smoke_text = check.NATIVE_SMOKE_TEST.read_text(encoding="utf-8").replace(
            "nativeSwitchTempNamesAvoidUserNames = true",
            "nativeSwitchTempNamesCollideWithUserNames = true",
        )
        errors = check.check_native_switch_lowering_boundary(
            check.NATIVE_ADAPTER.read_text(encoding="utf-8"),
            smoke_text,
        )
        self.assertTrue(any("nativeSwitchTempNamesAvoidUserNames" in error for error in errors), errors)

    def test_native_switch_lowering_boundary_rejects_missing_function_collision_smoke(self) -> None:
        smoke_text = check.NATIVE_SMOKE_TEST.read_text(encoding="utf-8").replace(
            "nativeFunctionSwitchTempNamesAvoidLocalUserNames = true",
            "nativeFunctionSwitchTempNamesCollideWithLocalUserNames = true",
        )
        errors = check.check_native_switch_lowering_boundary(
            check.NATIVE_ADAPTER.read_text(encoding="utf-8"),
            smoke_text,
        )
        self.assertTrue(
            any("nativeFunctionSwitchTempNamesAvoidLocalUserNames" in error for error in errors),
            errors,
        )


if __name__ == "__main__":
    unittest.main()
