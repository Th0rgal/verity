#!/usr/bin/env python3
"""Validate selector hashing against solc fixtures.

Runs `solc --hashes` on a small Solidity fixture and compares the
reported selectors to the keccak implementation used by our tools.
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path

from keccak256 import selector as compute_selector
from property_utils import die, report_errors

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "scripts" / "fixtures" / "SelectorFixtures.sol"

SIG_RE = re.compile(r"^([A-Za-z0-9_]+\([^\)]*\))\s*:\s*(0x)?([0-9a-fA-F]{8})$")
HASH_RE = re.compile(r"^(0x)?([0-9a-fA-F]{8})\s*:\s*([A-Za-z0-9_]+\([^\)]*\))$")


def _strip_param_names(params: str) -> str:
    if not params.strip():
        return ""
    cleaned: list[str] = []
    skip = {"memory", "calldata", "storage", "payable"}
    for raw in params.split(","):
        tokens = [token for token in raw.strip().split() if token and token not in skip]
        if not tokens:
            continue
        cleaned.append(tokens[0])
    return ",".join(cleaned)


def load_fixture_signatures() -> list[str]:
    if not FIXTURE.exists():
        die(f"Missing fixture file: {FIXTURE}")
    text = FIXTURE.read_text(encoding="utf-8")
    sigs: list[str] = []
    for line in text.splitlines():
        line = line.strip()
        if not line.startswith("function "):
            continue
        line = line[len("function ") :]
        name = line.split("(", 1)[0].strip()
        params = line.split("(", 1)[1].split(")", 1)[0].strip()
        params = _strip_param_names(params)
        sigs.append(f"{name}({params})")
    if not sigs:
        die("No function signatures found in fixture")
    return sigs


def run_solc_hashes() -> dict[str, str]:
    result = subprocess.run(
        ["solc", "--hashes", str(FIXTURE)],
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        die(f"solc --hashes failed: {result.stderr.strip()}")
    hashes: dict[str, str] = {}
    for line in result.stdout.splitlines():
        line = line.strip()
        if not line or line.endswith(":"):
            continue
        match = SIG_RE.match(line)
        if match:
            signature = match.group(1)
            selector = match.group(3).lower()
            hashes[signature] = selector
            continue
        match = HASH_RE.match(line)
        if match:
            selector = match.group(2).lower()
            signature = match.group(3)
            hashes[signature] = selector
            continue
    if not hashes:
        die("No selector hashes parsed from solc output")
    return hashes


def run_keccak(signatures: list[str]) -> dict[str, str]:
    return {sig: compute_selector(sig).replace("0x", "") for sig in signatures}


def main() -> None:
    signatures = load_fixture_signatures()
    solc_hashes = run_solc_hashes()
    keccak_hashes = run_keccak(signatures)

    errors: list[str] = []
    for signature in signatures:
        solc_selector = solc_hashes.get(signature)
        if solc_selector is None:
            errors.append(f"Missing solc selector for {signature}")
            continue
        keccak_selector = keccak_hashes[signature]
        if solc_selector != keccak_selector:
            errors.append(
                f"Selector mismatch for {signature}: solc={solc_selector} keccak={keccak_selector}"
            )

    report_errors(errors, "Selector fixture check failed")

    print("Selector fixture check passed.")


if __name__ == "__main__":
    main()
