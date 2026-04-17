#!/usr/bin/env python3
"""Generate/check deterministic EVMYulLean fork-audit artifact.

Records the exact divergence between ``lfglabs-dev/EVMYulLean`` (the fork
Verity depends on) and its upstream ``NethermindEth/EVMYulLean``. The
artifact answers the audit question: "What code in Verity's pinned
EVMYulLean dependency is NOT identical to the upstream reference?"

The fork audit is a required trust-surface document under Issue #1722:
every fork-side divergence must be minimal, visibility-preserving, and
documented here so that downstream auditors can review exactly what
Verity is trusting beyond upstream EVMYulLean's Ethereum conformance
test suite.

This script does NOT fetch from GitHub at build time (CI may run
offline). Instead, the audit contents are hand-maintained as a
constant below, and this script simply serializes them into a
deterministic JSON artifact and checks that the on-disk artifact
matches. The on-disk SHA in ``lake-manifest.json`` is cross-checked
against the ``pinned_commit`` field to catch silent drift: if Verity
bumps the pinned EVMYulLean commit, this script fails, forcing the
developer to regenerate the audit manifest.

Usage:
    python3 scripts/generate_evmyullean_fork_audit.py
    python3 scripts/generate_evmyullean_fork_audit.py --check
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from property_utils import ROOT

LAKE_MANIFEST = ROOT / "lake-manifest.json"
PACKAGE_MANIFESTS = sorted((ROOT / "packages").glob("*/lake-manifest.json"))
LAKE_MANIFESTS = [LAKE_MANIFEST, *PACKAGE_MANIFESTS]
DEFAULT_OUTPUT = ROOT / "artifacts" / "evmyullean_fork_audit.json"

# Hand-maintained record of the fork's divergence from upstream.
# When the pinned commit changes, update this dict and re-run the
# generator. The script's check mode will refuse to pass if the pinned
# commit in lake-manifest.json disagrees with ``pinned_commit`` here.
FORK_AUDIT = {
    "schema_version": 1,
    "fork_url": "https://github.com/lfglabs-dev/EVMYulLean",
    "upstream_url": "https://github.com/NethermindEth/EVMYulLean",
    "pinned_commit": "7b54b8f38bb68ee930d00d39c1b11dd60fb123c8",
    "upstream_base": "047f63070309f436b66c61e276ab3b6d1169265a",
    "fork_ahead_by": 2,
    "fork_behind_by": 0,
    "divergence_summary": (
        "Fork is exactly 2 commits ahead of upstream/main. Both commits are "
        "non-semantic: one visibility change (private -> default) on an "
        "internal exponentiation accumulator, and one Lean 4.22.0 "
        "deprecation fix (nativeLibDir -> staticLibDir) in the lakefile. "
        "Neither commit changes EVM/Yul execution semantics, so upstream "
        "Ethereum conformance test coverage continues to apply transitively."
    ),
    "commits": [
        {
            "sha": "ed9215e9ba8e3fa73128f3b67131793a01db332f",
            "title": "feat: expose powAux for downstream formal verification",
            "file": "EvmYul/UInt256.lean",
            "category": "visibility",
            "semantic_change": False,
            "rationale": (
                "Remove `private` modifier from `EvmYul.UInt256.powAux` "
                "(binary-exponentiation accumulator for `UInt256.exp`). "
                "In Lean 4.22.0 private declarations cannot be unfolded "
                "across module boundaries (`simp only`, `unfold`, and "
                "`delta` all fail) because their equational theorems are "
                "also private (Lean 4 PR #8519). Exposing the function "
                "unblocks Verity's inductive bridge proof for the `exp` "
                "builtin in `EvmYulLeanBridgeLemmas.lean`."
            ),
            "diff_summary": (
                "1 file changed, 2 insertions(+), 1 deletion(-): strip "
                "`private` from one `def`, add a doc comment. No behavior "
                "change."
            ),
            "trust_impact": (
                "Zero. Visibility is a module-system concept with no "
                "runtime or logical effect on term evaluation."
            ),
        },
        {
            "sha": "7b54b8f38bb68ee930d00d39c1b11dd60fb123c8",
            "title": "fix: replace deprecated nativeLibDir with staticLibDir",
            "file": "lakefile.lean",
            "category": "toolchain",
            "semantic_change": False,
            "rationale": (
                "`Lake.Package.nativeLibDir` was deprecated in Lean "
                "4.22.0 in favor of `staticLibDir`. The fork pins to "
                "Lean 4.22.0 to match Verity's toolchain, so the fix "
                "silences a build-time warning that Verity's build "
                "would otherwise promote to an error under its "
                "`-Dwarnings.toErrors=true` CI policy."
            ),
            "diff_summary": (
                "1 file changed, 1 insertion(+), 1 deletion(-): rename "
                "one field reference in the FFI extern-lib build step. "
                "No behavior change."
            ),
            "trust_impact": (
                "Zero. Lake build metadata only; compiled output is "
                "byte-identical up to path naming."
            ),
        },
    ],
    "audit_methodology": [
        "1. Clone lfglabs-dev/EVMYulLean at pinned commit into a local worktree.",
        "2. Add NethermindEth/EVMYulLean as `upstream` remote and fetch.",
        "3. Compute `git merge-base upstream/main origin/main` to find the divergence point.",
        "4. For each commit in `upstream/main..origin/main`, record SHA, title, touched files, and categorize as {visibility, toolchain, lemma-addition, builtin-addition, semantic-change}.",
        "5. Reject `semantic-change` category without explicit Issue #1722 scope expansion (would break upstream conformance test coverage).",
        "6. Commit this artifact alongside Verity's lake-manifest.json pin bump.",
    ],
    "reproduction": {
        "script": "scripts/generate_evmyullean_fork_audit.py",
        "steps": [
            "git clone https://github.com/lfglabs-dev/EVMYulLean",
            "cd EVMYulLean",
            "git remote add upstream https://github.com/NethermindEth/EVMYulLean.git",
            "git fetch upstream",
            "git log --oneline upstream/main..origin/main",
            "git diff --stat upstream/main..origin/main",
        ],
    },
    "trust_boundary": (
        "Verity's effective trust boundary for Yul/EVM semantics is "
        "(upstream NethermindEth/EVMYulLean at commit "
        "047f63070309f436b66c61e276ab3b6d1169265a) plus the 2 "
        "visibility/toolchain fork commits enumerated above. Neither "
        "fork commit touches EVM/Yul execution semantics, so upstream "
        "Ethereum conformance test coverage applies transitively."
    ),
}


def _read_evmyul_package(manifest_path: Path) -> dict[str, object]:
    """Extract the ``evmyul`` package entry from a Lake manifest."""
    with manifest_path.open("r", encoding="utf-8") as f:
        manifest = json.load(f)
    for pkg in manifest.get("packages", []):
        if pkg.get("name") == "evmyul":
            return pkg
    raise RuntimeError(f"evmyul package not found in {manifest_path.relative_to(ROOT)}")


def _validate_audit() -> None:
    """Validate internal invariants of the audit record."""
    if FORK_AUDIT["fork_ahead_by"] != len(FORK_AUDIT["commits"]):
        raise RuntimeError(
            f"fork_ahead_by ({FORK_AUDIT['fork_ahead_by']}) does not match "
            f"number of enumerated commits ({len(FORK_AUDIT['commits'])})"
        )
    if FORK_AUDIT["fork_behind_by"] != 0:
        raise RuntimeError(
            "fork_behind_by must be 0 to guarantee upstream conformance "
            "coverage applies transitively"
        )
    for commit in FORK_AUDIT["commits"]:
        if commit.get("semantic_change") is not False:
            raise RuntimeError(
                f"commit {commit['sha'][:10]} must be non-semantic; "
                f"semantic changes require Issue #1722 scope expansion"
            )
        if not re.match(r"^[0-9a-f]{40}$", commit["sha"]):
            raise RuntimeError(
                f"invalid SHA format: {commit['sha']}"
            )
    pinned = FORK_AUDIT["pinned_commit"]
    expected_tip = (
        FORK_AUDIT["commits"][-1]["sha"]
        if FORK_AUDIT["commits"]
        else FORK_AUDIT["upstream_base"]
    )
    if pinned != expected_tip:
        raise RuntimeError(
            f"pinned_commit {pinned} must match the audited fork tip "
            f"{expected_tip}"
        )


def _cross_check_manifest_pin() -> None:
    """Verify every tracked Lake manifest pins the audited fork commit."""
    expected_url = FORK_AUDIT["fork_url"] + ".git"
    for manifest_path in LAKE_MANIFESTS:
        pkg = _read_evmyul_package(manifest_path)
        pinned = pkg.get("rev", "")
        input_rev = pkg.get("inputRev", "")
        label = str(manifest_path.relative_to(ROOT))
        if pinned != FORK_AUDIT["pinned_commit"]:
            raise RuntimeError(
                f"{label} pins evmyul at {pinned} but the fork "
                f"audit records pinned_commit={FORK_AUDIT['pinned_commit']}. "
                f"The audit must be regenerated whenever the pin moves."
            )
        if input_rev != FORK_AUDIT["pinned_commit"]:
            raise RuntimeError(
                f"{label} records evmyul inputRev={input_rev} but the fork "
                f"audit records pinned_commit={FORK_AUDIT['pinned_commit']}."
            )
        if pkg.get("url") != expected_url:
            raise RuntimeError(
                f"{label} points evmyul at {pkg.get('url')} "
                f"but audit records fork_url={expected_url}"
            )


def _serialize() -> str:
    """Render the audit as stable, sorted JSON."""
    return json.dumps(FORK_AUDIT, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="Verify the on-disk artifact matches what would be generated.",
    )
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Output path for the artifact.",
    )
    args = parser.parse_args()

    _validate_audit()
    _cross_check_manifest_pin()
    payload = _serialize()

    if args.check:
        if not args.output.exists():
            print(
                f"fork audit artifact missing: {args.output}",
                file=sys.stderr,
            )
            return 1
        on_disk = args.output.read_text(encoding="utf-8")
        if on_disk != payload:
            print(
                f"fork audit artifact drift: regenerate with\n"
                f"  python3 {Path(__file__).relative_to(ROOT)}",
                file=sys.stderr,
            )
            return 1
        return 0

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(payload, encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
