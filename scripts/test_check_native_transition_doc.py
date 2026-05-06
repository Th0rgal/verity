#!/usr/bin/env python3

from __future__ import annotations

import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_native_transition_doc as check


class NativeTransitionDocCheckTests(unittest.TestCase):
    def test_current_doc_passes(self) -> None:
        text = check.DOC.read_text(encoding="utf-8")
        self.assertEqual(check.check_doc(text), [])

    def test_current_definition_of_done_doc_passes(self) -> None:
        text = check.DOD_DOC.read_text(encoding="utf-8")
        self.assertEqual(check.check_definition_of_done_doc(text), [])

    def test_definition_of_done_doc_rejects_removed_fuel_wrapper_target(self) -> None:
        text = check.DOD_DOC.read_text(encoding="utf-8").replace(
            "interpretYulRuntimeWithBackend .evmYulLean",
            "interpretYulRuntimeEvmYulLeanFuelWrapperDefaultFuel",
            1,
        )
        errors = check.check_definition_of_done_doc(text)
        self.assertTrue(
            any("FuelWrapperDefaultFuel" in error for error in errors),
            errors,
        )

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

    def test_rejects_missing_explicit_evmyullean_backend_name(self) -> None:
        text = check.DOC.read_text(encoding="utf-8").replace(
            "`yulCodegen_preserves_semantics_evmYulLeanBackend`",
            "`yulCodegen_preserves_semantics_evmYulLean`",
        )
        errors = check.check_doc(text)
        self.assertTrue(
            any(
                "yulCodegen_preserves_semantics_evmYulLeanBackend" in error
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

    def test_public_theorem_target_guard_rejects_missing_canonical_native_fuel_seam(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure_canonicalFuel",
            "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure_hiddenCanonicalFuel",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("positive_body_closure_canonicalFuel" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_project_canonical_native_fuel_seam(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_canonicalFuel",
            "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_hiddenCanonicalFuel",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("project_body_closure_canonicalFuel" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_layer3_canonical_native_fuel_seam(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_positive_body_closure_canonicalFuel",
            "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_positive_body_closure_hiddenCanonicalFuel",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("positive_body_closure_canonicalFuel" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_layer3_dispatcher_stmts_canonical_native_fuel_seam(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment_canonicalFuel",
            "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment_hiddenCanonicalFuel",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("dispatcherStmts_positive_body_closure_noMapping_ofIR_environment_canonicalFuel" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_layer3_lowered_dispatcher_stmts_canonical_native_fuel_seam(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_canonicalFuel",
            "theorem layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_hiddenCanonicalFuel",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_canonicalFuel" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_runtime_canonical_native_fuel_seam(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure_canonicalFuel",
            "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure_hiddenCanonicalFuel",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("positive_body_closure_canonicalFuel" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_dispatcher_exec_match_canonical_native_fuel_seam(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_match_canonicalFuel",
            "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_match_hiddenCanonicalFuel",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("dispatcherExec_positive_match_canonicalFuel" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_call_dispatcher_match_surface(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "def nativeGeneratedCallDispatcherMatchesIROn",
            "def nativeGeneratedHiddenCallDispatcherMatchesIROn",
            1,
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("nativeGeneratedCallDispatcherMatchesIROn" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_public_dispatcher_exec_surface(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            .replace(
                "private def nativeGeneratedDispatcherExecMatchesIROn",
                "def nativeGeneratedDispatcherExecMatchesIROn",
                1,
            )
            .replace(
                "private theorem compile_preserves_native_evmYulLean_of_generated_dispatcherExec_match",
                "theorem compile_preserves_native_evmYulLean_of_generated_dispatcherExec_match",
                1,
            )
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("dispatcher-exec compatibility seams private" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_generated_call_dispatcher_wrapper(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "theorem compile_preserves_native_evmYulLean_of_generated_callDispatcher_match",
            "theorem compile_preserves_native_evmYulLean_of_generated_hiddenCallDispatcher_match",
            1,
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("generated_callDispatcher_match" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_lowered_call_dispatcher_wrappers(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8")
        end_to_end_text = end_to_end_text.replace(
            "theorem compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_noMapping",
            "theorem compile_preserves_native_evmYulLean_of_lowered_generated_hiddenCallDispatcher_noMapping",
            1,
        ).replace(
            "theorem compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_mapping",
            "theorem compile_preserves_native_evmYulLean_of_lowered_generated_hiddenCallDispatcher_mapping",
            1,
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("lowered_generated_callDispatcher_noMapping" in error for error in errors),
            errors,
        )
        self.assertTrue(
            any("lowered_generated_callDispatcher_mapping" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_runtime_dispatcher_stmts_canonical_native_fuel_seam(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment_canonicalFuel",
            "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment_hiddenCanonicalFuel",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("dispatcherStmts_positive_body_closure_noMapping_ofIR_environment_canonicalFuel" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_runtime_lowered_dispatcher_stmts_canonical_native_fuel_seam(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_canonicalFuel",
            "theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_hiddenCanonicalFuel",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_canonicalFuel" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_layers2_3_lowered_dispatcher_stmts_canonical_native_fuel_seam(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_canonicalFuel",
            "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_hiddenCanonicalFuel",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("lowered_runtime_dispatcherStmts_positive_body_closure_noMapping_canonicalFuel" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_dispatcher_stmts_canonical_native_fuel_seam(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment_canonicalFuel",
            "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_noMapping_ofIR_environment_hiddenCanonicalFuel",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("dispatcherStmts_positive_body_closure_noMapping_ofIR_environment_canonicalFuel" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_missing_mapping_reserved_dispatcher_stmts_canonical_native_fuel_seam(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_environment_canonicalFuel",
            "theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_environment_hiddenCanonicalFuel",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("dispatcherStmts_positive_body_closure_mapping_reserved_ofIR_environment_canonicalFuel" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_legacy_backend_target(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\n-- stale target: interpretYulRuntimeWithBackend .evmYulLean\n"
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("interpretYulRuntimeWithBackend .evmYulLean" in error for error in errors),
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

    def test_public_theorem_target_guard_rejects_reintroduced_native_fuel_wrapper_obligation(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\ndef nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper : Prop := True\n"
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

    def test_public_theorem_target_guard_rejects_reintroduced_yul_result_agreement(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\ndef yulResultsAgreeOn : Prop := True\n"
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("yulResultsAgreeOn" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_direct_wrapper_fuel_bridge_obligation(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\ndef nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper : Prop := True\n"
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

    def test_public_theorem_target_guard_rejects_hidden_ir_runtime_alias(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\ndef nativeIRRuntimeAgreesWithEvmYulLean : Prop := True\n"
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("hidden native IR-runtime fuel-wrapper alias" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_simple_storage_native_compat_wrapper(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "simpleStorage_endToEnd_native_evmYulLean_of_lowered_runtime_dispatcherStmts_match\n"
            "    tx initialState observableSlots",
            "simpleStorage_endToEnd_native_evmYulLean_of_positive_dispatcherExec_bridge\n"
            "    tx initialState observableSlots",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("lowered_runtime_dispatcherStmts_match" in error for error in errors),
            errors,
        )
        self.assertTrue(
            any("positive_dispatcherExec_bridge" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_simple_storage_native_compat_splitter(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "simpleStorageNativeCallDispatcherMatchBridge_of_per_case\n"
            "          tx initialState observableSlots",
            "simpleStorageNativeCallDispatcherBridge_of_per_case\n"
            "          tx initialState observableSlots",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("CallDispatcherMatchBridge" in error for error in errors),
            errors,
        )
        self.assertTrue(
            any("CallDispatcherBridge" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_misleading_positive_layer3_alias(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\ntheorem layer3_contract_preserves_semantics_native_of_generated_dispatcherExec_positive "
            + ": True := by trivial\n"
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("positive_match" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_misleading_positive_layers23_alias(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\ntheorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive "
            + ": True := by trivial\n"
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("positive_match" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_removed_simple_storage_bridge_surface(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\ndef simpleStorageNativeRetrieveHitBridge : Prop := True\n"
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("obsolete SimpleStorage fuel-wrapper bridge" in error for error in errors),
            errors,
        )

    def test_rejects_verity_default_builtin_backend(self) -> None:
        builtins_text = check.BUILTINS.read_text(encoding="utf-8").replace(
            "private abbrev defaultBuiltinBackend : BuiltinBackend := .evmYulLean",
            "private abbrev defaultBuiltinBackend : BuiltinBackend := .verity",
        )
        errors = check.check_default_builtin_backend(builtins_text)
        self.assertTrue(
            any("default builtin backend" in error for error in errors),
            errors,
        )

    def test_rejects_public_default_builtin_backend_alias(self) -> None:
        builtins_text = check.BUILTINS.read_text(encoding="utf-8").replace(
            "private abbrev defaultBuiltinBackend : BuiltinBackend := .evmYulLean",
            "abbrev defaultBuiltinBackend : BuiltinBackend := .evmYulLean",
        )
        errors = check.check_default_builtin_backend(builtins_text)
        self.assertTrue(
            any("defaultBuiltinBackend" in error for error in errors),
            errors,
        )

    def test_rejects_public_eval_builtin_call_wrapper(self) -> None:
        builtins_text = check.BUILTINS.read_text(encoding="utf-8").replace(
            "private def evalBuiltinCall",
            "def evalBuiltinCall",
            1,
        )
        errors = check.check_default_builtin_backend(builtins_text)
        self.assertTrue(
            any("evalBuiltinCall" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_reintroduced_call_dispatcher_fuel_wrapper(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\ndef nativeCallDispatcherAgreesWithEvmYulLeanFuelWrapper : Prop := True\n"
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

    def test_public_theorem_target_guard_rejects_eval_builtin_call_mention(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\n-- stale proof note: evalBuiltinCall\n"
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("evalBuiltinCall" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_reintroduced_dispatcher_block_fuel_wrapper(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\ndef nativeDispatcherBlockAgreesWithEvmYulLeanFuelWrapper : Prop := True\n"
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

    def test_public_theorem_target_guard_rejects_reintroduced_dispatcher_exec_fuel_wrapper(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\ndef nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper : Prop := True\n"
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

    def test_public_theorem_target_guard_rejects_removed_backend_wrapper(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\nprivate theorem layers2_3_ir_matches_yul_evmYulLeanBackend : True := by trivial\n"
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("layers2_3_ir_matches_yul_evmYulLeanBackend" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_public_native_identity_seam(self) -> None:
        end_to_end_text = check.END_TO_END.read_text(encoding="utf-8").replace(
            "private theorem layers2_3_ir_matches_native_evmYulLean",
            "theorem layers2_3_ir_matches_native_evmYulLean",
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("arbitrary-fuel native identity seam" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_hidden_evmyullean_fuel_alias(self) -> None:
        retarget_text = (
            check.RETARGET.read_text(encoding="utf-8")
            + "\ndef interpretYulRuntimeEvmYulLean runtimeCode tx storage events := True\n"
        )
        errors = check.check_public_theorem_target(
            check.END_TO_END.read_text(encoding="utf-8"),
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            retarget_text,
        )
        self.assertTrue(
            any("interpretYulRuntimeEvmYulLean" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_public_backend_interpreter_surface(self) -> None:
        retarget_text = check.RETARGET.read_text(encoding="utf-8").replace(
            "private noncomputable def interpretYulRuntimeWithBackend",
            "noncomputable def interpretYulRuntimeWithBackend",
        )
        errors = check.check_public_theorem_target(
            check.END_TO_END.read_text(encoding="utf-8"),
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            retarget_text,
        )
        self.assertTrue(
            any("backend-interpreter transition surface" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_public_backend_fuel_surface(self) -> None:
        retarget_text = check.RETARGET.read_text(encoding="utf-8").replace(
            "private theorem execYulFuelWithBackend_eq_on_bridged_target",
            "theorem execYulFuelWithBackend_eq_on_bridged_target",
        )
        errors = check.check_public_theorem_target(
            check.END_TO_END.read_text(encoding="utf-8"),
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            retarget_text,
        )
        self.assertTrue(
            any("backend-interpreter transition surface" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_public_expression_bridge_surface(self) -> None:
        retarget_text = check.RETARGET.read_text(encoding="utf-8").replace(
            "private theorem evalYulExpr_evmYulLean_eq_on_bridged",
            "theorem evalYulExpr_evmYulLean_eq_on_bridged",
        )
        errors = check.check_public_theorem_target(
            check.END_TO_END.read_text(encoding="utf-8"),
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            retarget_text,
        )
        self.assertTrue(
            any("backend-interpreter transition surface" in error for error in errors),
            errors,
        )

    def test_reference_oracle_names_guard_accepts_current_shape(self) -> None:
        errors = check.check_reference_oracle_names(
            check.END_TO_END.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
            check.PRESERVATION.read_text(encoding="utf-8"),
        )
        self.assertEqual(errors, [])

    def test_public_surface_guard_rejects_legacy_reference_oracle_end_to_end_wrapper(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\ntheorem layer3_contract_preserves_semantics_via_reference_oracle : True := by trivial\n"
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.RETARGET.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("layer3_contract_preserves_semantics_via_reference_oracle" in error for error in errors),
            errors,
        )

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

    def test_reference_oracle_names_guard_rejects_reintroduced_evmyullean_retarget(self) -> None:
        retarget_text = (
            check.RETARGET.read_text(encoding="utf-8")
            + "\nprivate theorem yulCodegen_preserves_semantics_evmYulLeanBackend "
            + ": True := by trivial\n"
        )
        errors = check.check_reference_oracle_names(
            check.END_TO_END.read_text(encoding="utf-8"),
            retarget_text,
            check.PRESERVATION.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("transition-only legacy Layer-3 retarget theorem" in error for error in errors),
            errors,
        )

    def test_reference_oracle_names_guard_rejects_public_evmyullean_retarget(self) -> None:
        retarget_text = (
            check.RETARGET.read_text(encoding="utf-8")
            + "\ntheorem yulCodegen_preserves_semantics_evmYulLeanBackend "
            + ": True := by trivial\n"
        )
        errors = check.check_reference_oracle_names(
            check.END_TO_END.read_text(encoding="utf-8"),
            retarget_text,
            check.PRESERVATION.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("transition-only legacy Layer-3 retarget theorem" in error for error in errors),
            errors,
        )

    def test_reference_oracle_names_guard_rejects_hidden_evmyullean_alias(self) -> None:
        retarget_text = (
            check.RETARGET.read_text(encoding="utf-8")
            + "\ntheorem yulCodegen_preserves_semantics_evmYulLean : True := by trivial\n"
        )
        errors = check.check_reference_oracle_names(
            check.END_TO_END.read_text(encoding="utf-8"),
            retarget_text,
            check.PRESERVATION.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("hidden reference-oracle compatibility alias" in error for error in errors),
            errors,
        )

    def test_reference_oracle_names_guard_rejects_hidden_evmyullean_via_reference_alias(self) -> None:
        retarget_text = (
            check.RETARGET.read_text(encoding="utf-8")
            + "\ntheorem yulCodegen_preserves_semantics_evmYulLean_via_reference_oracle : True := by trivial\n"
        )
        errors = check.check_reference_oracle_names(
            check.END_TO_END.read_text(encoding="utf-8"),
            retarget_text,
            check.PRESERVATION.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("hidden default-fuel compatibility alias" in error for error in errors),
            errors,
        )

    def test_reference_oracle_names_guard_rejects_reintroduced_evmyullean_via_reference_retarget(self) -> None:
        retarget_text = (
            check.RETARGET.read_text(encoding="utf-8")
            + "\nprivate theorem yulCodegen_preserves_semantics_evmYulLeanBackend_via_reference_oracle "
            + ": True := by trivial\n"
        )
        errors = check.check_reference_oracle_names(
            check.END_TO_END.read_text(encoding="utf-8"),
            retarget_text,
            check.PRESERVATION.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("transition-only legacy Layer-3 retarget theorem" in error for error in errors),
            errors,
        )

    def test_reference_oracle_names_guard_rejects_end_to_end_compat_alias_call(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\n-- yulCodegen_preserves_semantics_evmYulLeanBackend_via_reference_oracle\n"
        )
        errors = check.check_reference_oracle_names(
            end_to_end_text,
            check.RETARGET.read_text(encoding="utf-8"),
            check.PRESERVATION.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("legacy compatibility alias" in error for error in errors),
            errors,
        )

    def test_reference_oracle_names_guard_rejects_reintroduced_native_layer3_oracle_seam(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\ntheorem layer3_contract_preserves_semantics_native_via_reference_oracle_of_evmYulLean_bridge "
            + ": True := by trivial\n"
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

    def test_reference_oracle_names_guard_rejects_reintroduced_native_end_to_end_oracle_seam(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\ntheorem layers2_3_ir_matches_native_evmYulLean_via_reference_oracle_of_evmYulLean_bridge "
            + ": True := by trivial\n"
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

    def test_legacy_proof_boundary_accepts_current_shape(self) -> None:
        errors = check.check_legacy_proof_boundary(
            [
                ("Compiler/Proofs/EndToEnd.lean", check.END_TO_END.read_text(encoding="utf-8")),
                ("Compiler.lean", check.ROOT_COMPILER.read_text(encoding="utf-8")),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean",
                    check.NATIVE_HARNESS.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanAdapter.lean",
                    check.NATIVE_ADAPTER.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgePredicates.lean",
                    check.BRIDGE_PREDICATES.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBodyClosure.lean",
                    check.BODY_CLOSURE.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanSourceExprClosure.lean",
                    check.SOURCE_EXPR_CLOSURE.read_text(encoding="utf-8"),
                ),
            ],
            [
                (path.relative_to(check.ROOT).as_posix(), path.read_text(encoding="utf-8"))
                for path in check.LEGACY_PROOF_FILES
            ],
        )
        self.assertEqual(errors, [])

    def test_public_transitive_import_boundary_accepts_current_shape(self) -> None:
        errors = check.check_public_transitive_import_boundary(
            [
                ("Compiler/Proofs/EndToEnd.lean", check.END_TO_END.read_text(encoding="utf-8")),
                ("Compiler.lean", check.ROOT_COMPILER.read_text(encoding="utf-8")),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean",
                    check.NATIVE_HARNESS.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanAdapter.lean",
                    check.NATIVE_ADAPTER.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgePredicates.lean",
                    check.BRIDGE_PREDICATES.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBodyClosure.lean",
                    check.BODY_CLOSURE.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanSourceExprClosure.lean",
                    check.SOURCE_EXPR_CLOSURE.read_text(encoding="utf-8"),
                ),
            ]
        )
        self.assertEqual(errors, [])

    def test_public_transitive_import_boundary_rejects_helper_reaching_bridge_lemmas(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\nimport Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeTest\n"
        )
        errors = check.check_public_transitive_import_boundary(
            [("Compiler/Proofs/EndToEnd.lean", end_to_end_text)]
        )
        self.assertTrue(
            any("EvmYulLeanBridgeLemmas" in error for error in errors),
            errors,
        )

    def test_public_transitive_import_boundary_rejects_helper_reaching_reference_oracle(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\nimport Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeTest\n"
        )
        errors = check.check_public_transitive_import_boundary(
            [("Compiler/Proofs/EndToEnd.lean", end_to_end_text)]
        )
        self.assertTrue(
            any("ReferenceOracle.Builtins" in error for error in errors),
            errors,
        )

    def test_public_transitive_forbidden_terms_accepts_current_shape(self) -> None:
        errors = check.check_public_transitive_forbidden_terms(
            [
                ("Compiler/Proofs/EndToEnd.lean", check.END_TO_END.read_text(encoding="utf-8")),
                ("Compiler.lean", check.ROOT_COMPILER.read_text(encoding="utf-8")),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean",
                    check.NATIVE_HARNESS.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanAdapter.lean",
                    check.NATIVE_ADAPTER.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgePredicates.lean",
                    check.BRIDGE_PREDICATES.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBodyClosure.lean",
                    check.BODY_CLOSURE.read_text(encoding="utf-8"),
                ),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanSourceExprClosure.lean",
                    check.SOURCE_EXPR_CLOSURE.read_text(encoding="utf-8"),
                ),
            ]
        )
        self.assertEqual(errors, [])

    def test_public_transitive_forbidden_terms_rejects_adapter_legacy_term(self) -> None:
        adapter_text = (
            check.NATIVE_ADAPTER.read_text(encoding="utf-8")
            + "\n-- stale proof dependency: interpretYulRuntimeWithBackend .evmYulLean\n"
        )
        errors = check.check_public_transitive_forbidden_terms(
            [
                ("Compiler.lean", check.ROOT_COMPILER.read_text(encoding="utf-8")),
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanAdapter.lean",
                    adapter_text,
                ),
            ]
        )
        self.assertTrue(
            any("interpretYulRuntimeWithBackend" in error for error in errors),
            errors,
        )

    def test_public_transitive_forbidden_terms_rejects_native_harness_legacy_term(self) -> None:
        native_harness_text = (
            check.NATIVE_HARNESS.read_text(encoding="utf-8")
            + "\n-- stale proof dependency: evalBuiltinCallWithContext\n"
        )
        errors = check.check_public_transitive_forbidden_terms(
            [
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean",
                    native_harness_text,
                )
            ]
        )
        self.assertTrue(
            any("evalBuiltinCallWithContext" in error for error in errors),
            errors,
        )

    def test_bridge_lemmas_transition_surface_accepts_current_shape(self) -> None:
        errors = check.check_bridge_lemmas_transition_surface(
            check.BRIDGE_LEMMAS.read_text(encoding="utf-8")
        )
        self.assertEqual(errors, [])

    def test_bridge_lemmas_transition_surface_rejects_public_pure_bridge(self) -> None:
        bridge_lemmas_text = check.BRIDGE_LEMMAS.read_text(encoding="utf-8").replace(
            "private theorem evalBuiltinCallWithBackendContext_evmYulLean_pure_bridge",
            "theorem evalBuiltinCallWithBackendContext_evmYulLean_pure_bridge",
            1,
        )
        errors = check.check_bridge_lemmas_transition_surface(bridge_lemmas_text)
        self.assertTrue(
            any("pure_bridge" in error for error in errors),
            errors,
        )

    def test_native_closure_import_boundary_accepts_current_shape(self) -> None:
        errors = check.check_native_closure_import_boundary(
            check.BRIDGE_PREDICATES.read_text(encoding="utf-8"),
            check.BODY_CLOSURE.read_text(encoding="utf-8"),
            check.SOURCE_EXPR_CLOSURE.read_text(encoding="utf-8"),
        )
        self.assertEqual(errors, [])

    def test_native_closure_import_boundary_rejects_legacy_predicate_language(self) -> None:
        bridge_text = (
            check.BRIDGE_PREDICATES.read_text(encoding="utf-8")
            + "\n/- native and transition backends agree through .verity -/\n"
        )
        errors = check.check_native_closure_import_boundary(
            bridge_text,
            check.BODY_CLOSURE.read_text(encoding="utf-8"),
            check.SOURCE_EXPR_CLOSURE.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("legacy transition authority language" in error for error in errors),
            errors,
        )

    def test_native_closure_import_boundary_rejects_bridge_predicates_ir_interpreter_import(self) -> None:
        bridge_text = (
            check.BRIDGE_PREDICATES.read_text(encoding="utf-8").replace(
                "import Compiler.Proofs.YulGeneration.LogNames",
                "import Compiler.Proofs.IRGeneration.IRInterpreter",
                1,
            )
        )
        errors = check.check_native_closure_import_boundary(
            bridge_text,
            check.BODY_CLOSURE.read_text(encoding="utf-8"),
            check.SOURCE_EXPR_CLOSURE.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("full IR interpreter" in error for error in errors),
            errors,
        )

    def test_runtime_types_import_boundary_accepts_current_shape(self) -> None:
        errors = check.check_runtime_types_import_boundary(
            check.RUNTIME_TYPES.read_text(encoding="utf-8")
        )
        self.assertEqual(errors, [])

    def test_runtime_types_import_boundary_rejects_ir_interpreter_import(self) -> None:
        runtime_types_text = check.RUNTIME_TYPES.read_text(encoding="utf-8").replace(
            "import Compiler.Proofs.IRGeneration.IRRuntimeTypes",
            "import Compiler.Proofs.IRGeneration.IRInterpreter",
            1,
        )
        errors = check.check_runtime_types_import_boundary(runtime_types_text)
        self.assertTrue(
            any("full IR interpreter" in error for error in errors),
            errors,
        )

    def test_native_harness_import_boundary_accepts_current_shape(self) -> None:
        errors = check.check_native_harness_import_boundary(
            check.NATIVE_HARNESS.read_text(encoding="utf-8")
        )
        self.assertEqual(errors, [])

    def test_native_harness_import_boundary_rejects_ir_interpreter_import(self) -> None:
        native_harness_text = (
            check.NATIVE_HARNESS.read_text(encoding="utf-8")
            + "\nimport Compiler.Proofs.IRGeneration.IRInterpreter\n"
        )
        errors = check.check_native_harness_import_boundary(native_harness_text)
        self.assertTrue(
            any("full IR interpreter" in error for error in errors),
            errors,
        )

    def test_root_compiler_import_boundary_accepts_current_shape(self) -> None:
        errors = check.check_root_compiler_import_boundary(
            check.ROOT_COMPILER.read_text(encoding="utf-8")
        )
        self.assertEqual(errors, [])

    def test_root_compiler_import_boundary_rejects_direct_ir_interpreter_import(self) -> None:
        root_text = (
            check.ROOT_COMPILER.read_text(encoding="utf-8")
            + "\nimport Compiler.Proofs.IRGeneration.IRInterpreter\n"
        )
        errors = check.check_root_compiler_import_boundary(root_text)
        self.assertTrue(
            any("full IR interpreter" in error for error in errors),
            errors,
        )

    def test_legacy_proof_boundary_rejects_public_boundary_import(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\nimport Compiler.Proofs.YulGeneration.Equivalence\n"
        )
        errors = check.check_legacy_proof_boundary(
            [("Compiler/Proofs/EndToEnd.lean", end_to_end_text)],
            [
                (path.relative_to(check.ROOT).as_posix(), path.read_text(encoding="utf-8"))
                for path in check.LEGACY_PROOF_FILES
            ],
        )
        self.assertTrue(
            any("transition-only legacy proof module" in error for error in errors),
            errors,
        )

    def test_legacy_proof_boundary_rejects_end_to_end_retarget_import(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\nimport Compiler.Proofs.YulGeneration.Backends.EvmYulLeanRetarget\n"
        )
        errors = check.check_legacy_proof_boundary(
            [("Compiler/Proofs/EndToEnd.lean", end_to_end_text)],
            [
                (path.relative_to(check.ROOT).as_posix(), path.read_text(encoding="utf-8"))
                for path in check.LEGACY_PROOF_FILES
            ],
        )
        self.assertTrue(
            any("EvmYulLeanRetarget" in error for error in errors),
            errors,
        )

    def test_legacy_proof_boundary_rejects_root_retarget_import(self) -> None:
        root_compiler_text = (
            check.ROOT_COMPILER.read_text(encoding="utf-8")
            + "\nimport Compiler.Proofs.YulGeneration.Backends.EvmYulLeanRetarget\n"
        )
        errors = check.check_legacy_proof_boundary(
            [("Compiler.lean", root_compiler_text)],
            [
                (path.relative_to(check.ROOT).as_posix(), path.read_text(encoding="utf-8"))
                for path in check.LEGACY_PROOF_FILES
            ],
        )
        self.assertTrue(
            any("EvmYulLeanRetarget" in error for error in errors),
            errors,
        )

    def test_legacy_proof_boundary_rejects_root_bridge_lemmas_import(self) -> None:
        root_compiler_text = (
            check.ROOT_COMPILER.read_text(encoding="utf-8")
            + "\nimport Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas\n"
        )
        errors = check.check_legacy_proof_boundary(
            [("Compiler.lean", root_compiler_text)],
            [
                (path.relative_to(check.ROOT).as_posix(), path.read_text(encoding="utf-8"))
                for path in check.LEGACY_PROOF_FILES
            ],
        )
        self.assertTrue(
            any("EvmYulLeanBridgeLemmas" in error for error in errors),
            errors,
        )

    def test_legacy_proof_boundary_rejects_adapter_reference_oracle_import(self) -> None:
        adapter_text = (
            check.NATIVE_ADAPTER.read_text(encoding="utf-8")
            + "\nimport Compiler.Proofs.YulGeneration.ReferenceOracle.Builtins\n"
        )
        errors = check.check_legacy_proof_boundary(
            [
                (
                    "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanAdapter.lean",
                    adapter_text,
                )
            ],
            [
                (path.relative_to(check.ROOT).as_posix(), path.read_text(encoding="utf-8"))
                for path in check.LEGACY_PROOF_FILES
            ],
        )
        self.assertTrue(
            any("legacy ReferenceOracle modules" in error for error in errors),
            errors,
        )

    def test_legacy_proof_boundary_rejects_root_reference_oracle_import(self) -> None:
        root_compiler_text = (
            check.ROOT_COMPILER.read_text(encoding="utf-8")
            + "\nimport Compiler.Proofs.YulGeneration.ReferenceOracle.Semantics\n"
        )
        errors = check.check_legacy_proof_boundary(
            [("Compiler.lean", root_compiler_text)],
            [
                (path.relative_to(check.ROOT).as_posix(), path.read_text(encoding="utf-8"))
                for path in check.LEGACY_PROOF_FILES
            ],
        )
        self.assertTrue(
            any("legacy ReferenceOracle modules" in error for error in errors),
            errors,
        )

    def test_legacy_proof_boundary_rejects_public_legacy_declaration(self) -> None:
        legacy_text = (
            check.LEGACY_PROOF_FILES[1].read_text(encoding="utf-8")
            + "\ntheorem leakedLegacyTransitionAuthority : True := by trivial\n"
        )
        errors = check.check_legacy_proof_boundary(
            [],
            [("Compiler/Proofs/YulGeneration/Equivalence.lean", legacy_text)],
        )
        self.assertTrue(
            any("leakedLegacyTransitionAuthority" in error for error in errors),
            errors,
        )

    def test_legacy_proof_boundary_rejects_public_attributed_legacy_declaration(self) -> None:
        legacy_text = (
            check.LEGACY_PROOF_FILES[0].read_text(encoding="utf-8")
            + "\n@[simp] theorem leakedLegacyFuelSimp : True := by trivial\n"
        )
        errors = check.check_legacy_proof_boundary(
            [],
            [("Compiler/Proofs/YulGeneration/Codegen.lean", legacy_text)],
        )
        self.assertTrue(
            any("leakedLegacyFuelSimp" in error for error in errors),
            errors,
        )

    def test_native_alias_signature_guard_accepts_current_shape(self) -> None:
        errors = check.check_native_alias_signatures(
            check.END_TO_END.read_text(encoding="utf-8"),
        )
        self.assertEqual(errors, [])

    def test_native_alias_signature_guard_rejects_hidden_dispatcher_alias(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + """
theorem nativeAliasSurfaceForTestEvmYulLean
    (h :
      nativeDispatcherExecAgreesWithEvmYulLean fuel contract tx state
        observableSlots nativeContract) :
    True := by
  trivial
"""
        )
        errors = check.check_native_alias_signatures(end_to_end_text)
        self.assertTrue(
            any("nativeDispatcherExecAgreesWithEvmYulLean" in error for error in errors),
            errors,
        )

    def test_native_alias_signature_guard_rejects_lowercase_evmYulLean_name(self) -> None:
        end_to_end_text = """
theorem nativeAliasSurfaceForTest_evmYulLean
    (h :
      nativeDispatcherExecAgreesWithEvmYulLean fuel contract tx state
        observableSlots nativeContract) :
    True := by
  trivial
"""
        errors = check.check_native_alias_signatures(end_to_end_text)
        self.assertTrue(
            any("nativeDispatcherExecAgreesWithEvmYulLean" in error for error in errors),
            errors,
        )

    def test_native_alias_signature_guard_allows_direct_match_theorem(self) -> None:
        end_to_end_text = """
theorem nativeAliasSurfaceForTestEvmYulLeanMatch
    (h :
      nativeDispatcherExecMatchesIRPositive fuel contract tx state
        observableSlots nativeContract) :
    True := by
  trivial
"""
        errors = check.check_native_alias_signatures(end_to_end_text)
        self.assertEqual(errors, [])

    def test_public_end_to_end_theorem_signature_guard_accepts_current_shape(self) -> None:
        errors = check.check_public_end_to_end_theorem_signatures(
            check.END_TO_END.read_text(encoding="utf-8"),
        )
        self.assertEqual(errors, [])

    def test_public_end_to_end_theorem_signature_guard_rejects_legacy_terms(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + """
theorem legacySignatureSurfaceForTest
    (h :
      Compiler.Proofs.YulGeneration.ReferenceOracle.Semantics.execYulFuelWithBackend
        .verity fuel stmts tx state = .ok result) :
    True := by
  trivial
"""
        )
        errors = check.check_public_end_to_end_theorem_signatures(end_to_end_text)
        self.assertTrue(
            any(".verity" in error and "execYulFuel" in error for error in errors),
            errors,
        )

    def test_public_end_to_end_theorem_signature_guard_rejects_arbitrary_fuel(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + """
theorem arbitraryFuelSurfaceForTest
    (fuel : Nat)
    (hNative : nativeResultsMatchOn observableSlots ir native) :
    True := by
  trivial
"""
        )
        errors = check.check_public_end_to_end_theorem_signatures(end_to_end_text)
        self.assertTrue(
            any("arbitrary theorem-facing fuel" in error for error in errors),
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
