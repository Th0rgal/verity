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

    def test_rejects_missing_blocker_issue(self) -> None:
        text = check.DOC.read_text(encoding="utf-8").replace("#1738", "#0000")
        errors = check.check_doc(text)
        self.assertTrue(any("#1738" in error for error in errors), errors)

    def test_rejects_authoritative_native_claim(self) -> None:
        text = (
            check.DOC.read_text(encoding="utf-8")
            + "\nNative EVMYulLean is now the authoritative semantic target.\n"
        )
        errors = check.check_doc(text)
        self.assertTrue(any("overstates" in error for error in errors), errors)


if __name__ == "__main__":
    unittest.main()
