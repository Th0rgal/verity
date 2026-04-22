#!/usr/bin/env python3
"""Keep the native EVMYulLean transition document honest.

PR #1743 deliberately introduces an executable native harness without moving the
public theorem target. This checker prevents the transition note from losing the
explicit blocker list or overstating native EVMYulLean as the current public
semantic target.
"""

from __future__ import annotations

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
    "native public theorem pending",
    "not yet proved",
    "#1741",
    "#1738",
    "#1742",
    "`blockTimestamp`",
    "mapping-struct",
    "signature-based identity model",
    "not yet bridged from `YulTransaction.chainId`",
    "not yet bridged from `YulTransaction.blobBaseFee`",
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


def check_public_theorem_target(end_to_end_text: str, native_harness_text: str) -> list[str]:
    """Pin the current transition boundary until the native theorem flips.

    This guard should be updated in the same PR that proves the native
    preservation theorem and retargets the public EndToEnd path. Until then,
    the public theorem must still visibly target the backend-parameterized
    interpreter, while the native harness remains an executable side path.
    """

    errors: list[str] = []
    normalized_end_to_end = normalize_ws(end_to_end_text)
    normalized_native_harness = normalize_ws(native_harness_text)

    if "interpretYulRuntimeWithBackend .evmYulLean" not in normalized_end_to_end:
        errors.append(
            "Compiler/Proofs/EndToEnd.lean must still expose the current "
            "`interpretYulRuntimeWithBackend .evmYulLean` public theorem target "
            "until the native preservation theorem is proved and this guard is updated"
        )

    for native_target in (
        "interpretIRRuntimeNative",
        "interpretRuntimeNative",
        "EvmYul.Yul.callDispatcher",
    ):
        if native_target in normalized_end_to_end:
            errors.append(
                "Compiler/Proofs/EndToEnd.lean mentions native runtime target "
                f"`{native_target}` before the public theorem flip is documented"
            )

    for required_native_entrypoint in (
        "def interpretRuntimeNative",
        "def interpretIRRuntimeNative",
        "EvmYul.Yul.callDispatcher",
    ):
        if required_native_entrypoint not in normalized_native_harness:
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/"
                "EvmYulLeanNativeHarness.lean is missing native harness surface "
                f"`{required_native_entrypoint}`"
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
        'nativeStoresBuiltin "chainid" 15 1 = true',
        'nativeStoresBuiltin "blobbasefee" 16 1 = true',
    ):
        if pinned_default not in normalized_native_smoke:
            errors.append(
                "Compiler/Proofs/YulGeneration/Backends/"
                "EvmYulLeanNativeSmokeTest.lean must pin the current native "
                f"default environment behavior with `{pinned_default}` until "
                "YulTransaction bridging is implemented"
            )

    return errors


def main() -> int:
    if not DOC.exists():
        print(f"Missing: {DOC.relative_to(ROOT)}", file=sys.stderr)
        return 1
    for path in (END_TO_END, NATIVE_HARNESS, NATIVE_SMOKE_TEST):
        if not path.exists():
            print(f"Missing: {path.relative_to(ROOT)}", file=sys.stderr)
            return 1

    native_harness_text = NATIVE_HARNESS.read_text(encoding="utf-8")
    errors = check_doc(DOC.read_text(encoding="utf-8"))
    errors.extend(
        check_public_theorem_target(
            END_TO_END.read_text(encoding="utf-8"),
            native_harness_text,
        )
    )
    errors.extend(
        check_unbridged_environment_boundary(
            native_harness_text,
            NATIVE_SMOKE_TEST.read_text(encoding="utf-8"),
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
