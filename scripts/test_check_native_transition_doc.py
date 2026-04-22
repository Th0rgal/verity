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

    def test_rejects_missing_unbridged_chainid_caveat(self) -> None:
        text = check.DOC.read_text(encoding="utf-8").replace(
            "`YulTransaction.chainId`",
            "`YulTransaction.chainIdStatus`",
        )
        errors = check.check_doc(text)
        self.assertTrue(
            any("YulTransaction.chainId" in error for error in errors),
            errors,
        )

    def test_rejects_missing_unbridged_blobbasefee_caveat(self) -> None:
        text = check.DOC.read_text(encoding="utf-8").replace(
            "`YulTransaction.blobBaseFee`",
            "`YulTransaction.blobBaseFeeStatus`",
        )
        errors = check.check_doc(text)
        self.assertTrue(
            any("YulTransaction.blobBaseFee" in error for error in errors),
            errors,
        )

    def test_rejects_authoritative_native_claim(self) -> None:
        text = (
            check.DOC.read_text(encoding="utf-8")
            + "\nNative EVMYulLean is now the authoritative semantic target.\n"
        )
        errors = check.check_doc(text)
        self.assertTrue(any("overstates" in error for error in errors), errors)

    def test_public_theorem_target_guard_accepts_current_transition_shape(self) -> None:
        errors = check.check_public_theorem_target(
            check.END_TO_END.read_text(encoding="utf-8"),
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
        )
        self.assertEqual(errors, [])

    def test_public_theorem_target_guard_rejects_missing_current_target(self) -> None:
        end_to_end_text = re.sub(
            r"interpretYulRuntimeWithBackend\s+\.evmYulLean",
            "interpretYulRuntimeWithBackend .verity",
            check.END_TO_END.read_text(encoding="utf-8"),
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
        )
        self.assertTrue(
            any("interpretYulRuntimeWithBackend .evmYulLean" in error for error in errors),
            errors,
        )

    def test_public_theorem_target_guard_rejects_premature_native_target(self) -> None:
        end_to_end_text = (
            check.END_TO_END.read_text(encoding="utf-8")
            + "\n-- theorem target: interpretIRRuntimeNative\n"
        )
        errors = check.check_public_theorem_target(
            end_to_end_text,
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
        )
        self.assertTrue(any("interpretIRRuntimeNative" in error for error in errors), errors)

    def test_unbridged_environment_boundary_accepts_current_shape(self) -> None:
        errors = check.check_unbridged_environment_boundary(
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            check.NATIVE_SMOKE_TEST.read_text(encoding="utf-8"),
        )
        self.assertEqual(errors, [])

    def test_unbridged_environment_boundary_rejects_missing_chainid_pin(self) -> None:
        smoke_text = check.NATIVE_SMOKE_TEST.read_text(encoding="utf-8").replace(
            'nativeStoresBuiltin "chainid" 15 1 = true',
            'nativeStoresBuiltin "chainid" 15 sampleTx.chainId = true',
        )
        errors = check.check_unbridged_environment_boundary(
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            smoke_text,
        )
        self.assertTrue(any("chainid" in error for error in errors), errors)

    def test_unbridged_environment_boundary_rejects_missing_blobbasefee_pin(self) -> None:
        smoke_text = check.NATIVE_SMOKE_TEST.read_text(encoding="utf-8").replace(
            'nativeStoresBuiltin "blobbasefee" 16 1 = true',
            'nativeStoresBuiltin "blobbasefee" 16 sampleTx.blobBaseFee = true',
        )
        errors = check.check_unbridged_environment_boundary(
            check.NATIVE_HARNESS.read_text(encoding="utf-8"),
            smoke_text,
        )
        self.assertTrue(any("blobbasefee" in error for error in errors), errors)


if __name__ == "__main__":
    unittest.main()
