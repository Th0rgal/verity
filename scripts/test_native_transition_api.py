#!/usr/bin/env python3

from __future__ import annotations

import re
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
HARNESS = (
    ROOT
    / "Compiler"
    / "Proofs"
    / "YulGeneration"
    / "Backends"
    / "EvmYulLeanNativeHarness.lean"
)


def declaration_block(text: str, name: str) -> str:
    match = re.search(rf"(?m)^def {re.escape(name)}\b", text)
    if match is None:
        raise AssertionError(f"missing definition: {name}")

    next_decl = re.search(
        r"(?m)^(?:def|theorem|lemma|@[^\n]+\s+theorem)\b",
        text[match.end() :],
    )
    end = match.end() + next_decl.start() if next_decl is not None else len(text)
    return text[match.start() : end]


class NativeTransitionApiTests(unittest.TestCase):
    def test_native_runtime_entrypoints_require_explicit_observable_slots(self) -> None:
        text = HARNESS.read_text(encoding="utf-8")

        for name in ["interpretRuntimeNative", "interpretIRRuntimeNative"]:
            with self.subTest(name=name):
                block = declaration_block(text, name)
                self.assertIn("(observableSlots : List Nat)", block)
                self.assertNotIn("(observableSlots : List Nat := []", block)
                self.assertNotIn("observableSlots : List Nat := []", block)


if __name__ == "__main__":
    unittest.main()
