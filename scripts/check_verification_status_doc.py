#!/usr/bin/env python3
"""Validate docs/VERIFICATION_STATUS.md against the verification artifact."""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT, collect_covered, load_exclusions
from verification_metrics import load_metrics_from_artifact

ARTIFACT = ROOT / "artifacts" / "verification_status.json"
STATUS_DOC = ROOT / "docs" / "VERIFICATION_STATUS.md"

LAYER1_ROW_RE = re.compile(r"^\| ([A-Za-z0-9]+) \| (\d+) \| [^|]+ \| `[^`]+` \|$", re.MULTILINE)
TOTAL_ROW_RE = re.compile(r"^\| \*\*Total\*\* \| \*\*(\d+)\*\* \|", re.MULTILINE)
NOTE_TOTAL_RE = re.compile(r"overall coverage statistics \((\d+) total properties\)\.")
COVERAGE_ROW_RE = re.compile(
    r"^\| ([A-Za-z0-9]+) \| (\d+)% \((\d+)/(\d+)\) \| ([^|]+) \|$",
    re.MULTILINE,
)
STATUS_RE = re.compile(r"^\*\*Status\*\*: (\d+)% coverage \((\d+)/(\d+)\), (\d+) remaining exclusions", re.MULTILINE)
BULLET_TOTAL_RE = re.compile(r"^- \*\*Total Properties\*\*: (\d+)$", re.MULTILINE)
BULLET_COVERED_RE = re.compile(r"^- \*\*Covered\*\*: (\d+)$", re.MULTILINE)
BULLET_EXCLUDED_RE = re.compile(r"^- \*\*Excluded\*\*: (\d+) \(all proof-only\)$", re.MULTILINE)
SORRY_RE = re.compile(r"^(\d+) `sorry` remaining across `Compiler/\*\*/\*\.lean` and `Verity/\*\*/\*\.lean` proof modules\.$", re.MULTILINE)


def _require_match(pattern: re.Pattern[str], text: str, label: str) -> tuple[str, ...]:
    match = pattern.search(text)
    if match is None:
        raise ValueError(f"{STATUS_DOC}: missing {label}")
    return match.groups()


def _check_equal(actual: object, expected: object, label: str) -> None:
    if actual != expected:
        raise ValueError(f"{STATUS_DOC}: {label} says {actual!r}, expected {expected!r}")


def _parse_exclusions(cell: str) -> int:
    value = cell.strip()
    if value == "0":
        return 0
    match = re.fullmatch(r"(\d+) proof-only", value)
    if match is None:
        raise ValueError(f"{STATUS_DOC}: unsupported exclusions cell {value!r}")
    return int(match.group(1))


def main() -> None:
    artifact = load_metrics_from_artifact(ARTIFACT)
    text = STATUS_DOC.read_text(encoding="utf-8")

    expected_layer1 = dict(artifact["theorems"]["per_contract"])
    expected_layer1["CryptoHash"] = 0
    found_layer1 = {name: int(count) for name, count in LAYER1_ROW_RE.findall(text)}
    _check_equal(found_layer1, expected_layer1, "Layer 1 contract table")
    _check_equal(int(_require_match(TOTAL_ROW_RE, text, "Layer 1 total row")[0]), artifact["theorems"]["total"], "Layer 1 total row")
    _check_equal(int(_require_match(NOTE_TOTAL_RE, text, "Layer 1 note total")[0]), artifact["theorems"]["total"], "Layer 1 note total")

    covered = collect_covered()
    exclusions = load_exclusions()
    expected_coverage: dict[str, tuple[int, int, int, int]] = {}
    for name, total in artifact["theorems"]["per_contract"].items():
        covered_count = len(covered.get(name, set()))
        exclusion_count = len(exclusions.get(name, set()))
        percent = round(covered_count * 100 / total) if total else 0
        expected_coverage[name] = (percent, covered_count, total, exclusion_count)
    expected_coverage["Stdlib"] = (0, 0, artifact["theorems"]["stdlib"], 0)
    found_coverage = {
        name: (int(percent), int(covered_count), int(total), _parse_exclusions(excluded))
        for name, percent, covered_count, total, excluded in COVERAGE_ROW_RE.findall(text)
    }
    _check_equal(found_coverage, expected_coverage, "coverage table")

    status_percent, status_covered, status_total, status_excluded = _require_match(STATUS_RE, text, "coverage status summary")
    _check_equal(
        (int(status_percent), int(status_covered), int(status_total), int(status_excluded)),
        (
            artifact["theorems"]["coverage_percent"],
            artifact["theorems"]["covered"],
            artifact["theorems"]["total"],
            artifact["theorems"]["excluded"],
        ),
        "coverage status summary",
    )
    _check_equal(int(_require_match(BULLET_TOTAL_RE, text, "total properties bullet")[0]), artifact["theorems"]["total"], "total properties bullet")
    _check_equal(int(_require_match(BULLET_COVERED_RE, text, "covered bullet")[0]), artifact["theorems"]["covered"], "covered bullet")
    _check_equal(int(_require_match(BULLET_EXCLUDED_RE, text, "excluded bullet")[0]), artifact["theorems"]["excluded"], "excluded bullet")
    _check_equal(int(_require_match(SORRY_RE, text, "sorry summary")[0]), artifact["proofs"]["sorry"], "sorry summary")


if __name__ == "__main__":
    try:
        main()
    except ValueError as exc:
        print(exc, file=sys.stderr)
        raise SystemExit(1) from exc
