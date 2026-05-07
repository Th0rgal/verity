#!/usr/bin/env python3
"""Enforce pinned solc version consistency across CI, tooling, and docs.

Issue #76 depends on stable Yul->bytecode semantics. This script prevents
silent compiler-version drift by requiring one canonical solc version across:
  - GitHub Actions verify workflow env vars
  - foundry.toml profile config
  - trust assumptions documentation
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"
SETUP_SOLC_ACTION = ROOT / ".github" / "actions" / "setup-solc" / "action.yml"
FOUNDRY_TOML = ROOT / "foundry.toml"
TRUST_ASSUMPTIONS = ROOT / "TRUST_ASSUMPTIONS.md"

SOLC_VERSION_RE = re.compile(r'^\s*SOLC_VERSION:\s*"([^"]+)"\s*$', re.MULTILINE)
SOLC_URL_RE = re.compile(r'^\s*SOLC_URL:\s*"([^"]+)"\s*$', re.MULTILINE)
SOLC_SHA256_RE = re.compile(r'^\s*SOLC_SHA256:\s*"([0-9a-fA-F]{64})"\s*$', re.MULTILINE)

URL_VERSION_RE = re.compile(r"solc-linux-amd64-v(\d+\.\d+\.\d+)\+commit\.([0-9a-fA-F]{8})$")
FOUNDRY_SOLC_RE = re.compile(r'^\s*solc_version\s*=\s*"([^"]+)"\s*$', re.MULTILINE)
TRUST_PIN_RE = re.compile(r"\*\*Version\*\*:\s*([0-9]+\.[0-9]+\.[0-9]+\+commit\.[0-9a-fA-F]{8})\s+\(pinned\)")
SOLC_DOWNLOAD_RE = re.compile(r"curl\b[^\n]*\s\"\$SOLC_URL\"\s+-o\s+solc")


def _read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"missing file: {path.relative_to(ROOT)}")
    return path.read_text(encoding="utf-8")


def _collect(pattern: re.Pattern[str], text: str, label: str) -> list[str]:
    values = [m.group(1) for m in pattern.finditer(text)]
    if not values:
        raise ValueError(f"could not parse {label}")
    return values


def _extract_canonical(
    pattern: re.Pattern[str], text: str, label: str, errors: list[str]
) -> str:
    values = _collect(pattern, text, label)
    canonical = values[0]
    for idx, value in enumerate(values[1:], start=2):
        if value != canonical:
            errors.append(
                f".github/workflows/verify.yml: {label} occurrence {idx} "
                f"('{value}') conflicts with canonical '{canonical}'"
            )
    return canonical


def main() -> int:
    errors: list[str] = []

    try:
        verify_text = _read(VERIFY_YML)
        action_text = _read(SETUP_SOLC_ACTION)
        foundry_text = _read(FOUNDRY_TOML)
        trust_text = _read(TRUST_ASSUMPTIONS)
    except (FileNotFoundError, OSError) as err:
        print(f"solc pin check failed: {err}", file=sys.stderr)
        return 1

    try:
        solc_version = _extract_canonical(SOLC_VERSION_RE, verify_text, "SOLC_VERSION", errors)
        solc_url = _extract_canonical(SOLC_URL_RE, verify_text, "SOLC_URL", errors)
        _extract_canonical(SOLC_SHA256_RE, verify_text, "SOLC_SHA256", errors)
    except ValueError as err:
        print(f"solc pin check failed: {err}", file=sys.stderr)
        return 1

    url_match = URL_VERSION_RE.search(solc_url)
    if url_match is None:
        errors.append(
            ".github/workflows/verify.yml: SOLC_URL does not match expected solidity binary form"
        )
        url_version = None
        url_commit = None
    else:
        url_version, url_commit = url_match.group(1), url_match.group(2)
        if url_version != solc_version:
            errors.append(
                ".github/workflows/verify.yml: SOLC_VERSION does not match SOLC_URL embedded version"
            )

    foundry_solc = FOUNDRY_SOLC_RE.search(foundry_text)
    if foundry_solc is None:
        errors.append("foundry.toml: missing solc_version")
    elif foundry_solc.group(1) != solc_version:
        errors.append("foundry.toml: solc_version must match verify.yml SOLC_VERSION")

    trust_pin = TRUST_PIN_RE.search(trust_text)
    if trust_pin is None:
        errors.append(
            "TRUST_ASSUMPTIONS.md: missing pinned solc version line ('**Version**: <semver+commit> (pinned)')"
        )
    elif url_commit is not None and trust_pin.group(1) != f"{solc_version}+commit.{url_commit}":
        errors.append(
            "TRUST_ASSUMPTIONS.md: pinned solc version must match verify.yml SOLC_VERSION/SOLC_URL"
        )

    if SOLC_DOWNLOAD_RE.search(action_text) is None:
        errors.append(".github/actions/setup-solc/action.yml: install step must download from $SOLC_URL")
    if 'echo "${SOLC_SHA256}  solc" | sha256sum -c -' not in action_text:
        errors.append(".github/actions/setup-solc/action.yml: install step must verify $SOLC_SHA256")
    if "/usr/local/bin/solc" in action_text:
        errors.append(".github/actions/setup-solc/action.yml: solc cache/install path must be workspace-local")
    if re.search(r"\bsudo\b", action_text):
        errors.append(".github/actions/setup-solc/action.yml: solc install step must not require sudo")

    if errors:
        print("solc pin check failed:", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        return 1

    print(
        "✓ solc pin is consistent "
        f"({solc_version}{'' if url_commit is None else f'+commit.{url_commit}'})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
