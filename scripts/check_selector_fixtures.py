#!/usr/bin/env python3
"""Validate selector hashing against solc fixtures.

Runs `solc --hashes` on a small Solidity fixture and compares the
reported selectors to the keccak implementation used by our tools.
"""

from __future__ import annotations

import re
import subprocess

from keccak256 import selector as compute_selector
from property_utils import ROOT, die, report_errors
FIXTURE = ROOT / "scripts" / "fixtures" / "SelectorFixtures.sol"

SIG_RE = re.compile(r"^([A-Za-z0-9_]+\([^\)]*\))\s*:\s*(0x)?([0-9a-fA-F]{8})$")
HASH_RE = re.compile(r"^(0x)?([0-9a-fA-F]{8})\s*:\s*([A-Za-z0-9_]+\([^\)]*\))$")
FUNCTION_RE = re.compile(
    r"\bfunction\s+([A-Za-z_][A-Za-z0-9_]*)\s*\((.*?)\)\s*(?:external|public|internal|private)\b",
    re.DOTALL,
)


def _split_top_level_commas(params: str) -> list[str]:
    items: list[str] = []
    depth = 0
    start = 0
    for i, ch in enumerate(params):
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth = max(0, depth - 1)
        elif ch == "," and depth == 0:
            items.append(params[start:i].strip())
            start = i + 1
    tail = params[start:].strip()
    if tail:
        items.append(tail)
    return items


def _canonical_param_type(raw: str) -> str:
    # Remove data location and mutability keywords from declarations.
    text = re.sub(r"\b(memory|calldata|storage|payable)\b", " ", raw)
    text = re.sub(r"\s+", " ", text).strip()
    if not text:
        return ""

    parts = text.split(" ")
    if len(parts) > 1:
        # Drop trailing parameter name.
        text = " ".join(parts[:-1])

    # Normalize spaces around tuple/array punctuation.
    text = re.sub(r"\s*([\[\]\(\),])\s*", r"\1", text)
    return text


def _strip_param_names(params: str) -> str:
    if not params.strip():
        return ""
    cleaned: list[str] = []
    for raw in _split_top_level_commas(params):
        canonical = _canonical_param_type(raw)
        if canonical:
            cleaned.append(canonical)
    return ",".join(cleaned)


def load_fixture_signatures() -> list[str]:
    if not FIXTURE.exists():
        die(f"Missing fixture file: {FIXTURE}")
    text = FIXTURE.read_text(encoding="utf-8")
    sigs: list[str] = []
    for match in FUNCTION_RE.finditer(text):
        name = match.group(1)
        params = match.group(2).strip()
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
