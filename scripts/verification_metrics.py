#!/usr/bin/env python3
"""Shared verification metrics helpers for generated status artifacts."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from property_utils import (
    ROOT,
    collect_covered,
    load_exclusions,
    load_manifest,
    scrub_lean_code,
)


def get_manifest_counts() -> tuple[int, int, dict[str, int]]:
    """Return (total_theorems, num_categories, per_contract_counts)."""
    data = load_manifest()
    per_contract = {k: len(v) for k, v in data.items()}
    total = sum(per_contract.values())
    return total, len(data), per_contract


def _count_lean_lines(pattern: str) -> int:
    """Count lines matching *pattern* across all Lean files in Compiler/ and Verity/."""
    matcher = re.compile(pattern)
    count = 0
    for directory in [ROOT / "Compiler", ROOT / "Verity"]:
        if not directory.exists():
            continue
        for lean in directory.rglob("*.lean"):
            text = scrub_lean_code(lean.read_text(encoding="utf-8"))
            for line in text.splitlines():
                if matcher.match(line):
                    count += 1
    return count


def get_axiom_count() -> int:
    """Count axiom declarations in Lean files."""
    return _count_lean_lines(r"^(private |protected )?axiom\s+")


def get_test_counts() -> tuple[int, int]:
    """Count test functions and test suite files (recursive, includes test/yul/)."""
    test_dir = ROOT / "test"
    suite_count = len(list(test_dir.rglob("*.t.sol")))
    test_count = 0
    for sol in test_dir.rglob("*.t.sol"):
        text = sol.read_text(encoding="utf-8")
        test_count += len(re.findall(r"function\s+test", text))
    return test_count, suite_count


def get_property_test_function_count() -> int:
    """Count test functions in Property*.t.sol files only."""
    test_dir = ROOT / "test"
    count = 0
    for sol in sorted(test_dir.glob("Property*.t.sol")):
        text = sol.read_text(encoding="utf-8")
        count += len(re.findall(r"function\s+test", text))
    return count


def get_core_line_count() -> int:
    """Count lines in Verity/Core.lean."""
    core = ROOT / "Verity" / "Core.lean"
    return len(core.read_text(encoding="utf-8").splitlines())


def get_sorry_count() -> int:
    """Count sorry statements in Lean proof files."""
    matcher = re.compile(r"\bsorry\b")
    count = 0
    for directory in [ROOT / "Compiler", ROOT / "Verity"]:
        if not directory.exists():
            continue
        for lean in directory.rglob("*.lean"):
            text = scrub_lean_code(lean.read_text(encoding="utf-8"))
            for line in text.splitlines():
                if matcher.search(line):
                    count += 1
    return count


def get_contract_count() -> int:
    """Count example contracts in Contracts/."""
    contracts_dir = ROOT / "Contracts"
    return len([directory for directory in contracts_dir.iterdir() if directory.is_dir()])


def get_diff_test_total() -> int:
    """Compute total differential tests (10,000 per contract x number of contracts)."""
    test_dir = ROOT / "test"
    diff_count = len(list(test_dir.glob("Differential*.t.sol")))
    return diff_count * 10_000


def get_exclusion_count() -> int:
    """Count total property exclusions from property_exclusions.json."""
    data = load_exclusions()
    return sum(len(v) for v in data.values())


def get_covered_count(total_theorems: int) -> tuple[int, int]:
    """Compute covered property count and coverage percentage."""
    covered = collect_covered()
    covered_count = sum(len(v) for v in covered.values())
    pct = round(covered_count * 100 / total_theorems) if total_theorems else 0
    return covered_count, pct


def get_lean_toolchain() -> str:
    """Return pinned Lean toolchain string."""
    return (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()


def get_solc_version() -> str:
    """Return pinned solc version from foundry.toml."""
    text = (ROOT / "foundry.toml").read_text(encoding="utf-8")
    match = re.search(r'^solc_version\s*=\s*"([^"]+)"', text, re.MULTILINE)
    if not match:
        raise ValueError("foundry.toml: missing solc_version pin")
    return match.group(1)


def collect_metrics() -> dict[str, Any]:
    """Collect verification metrics from source files."""
    total_theorems, num_categories, per_contract = get_manifest_counts()
    axiom_count = get_axiom_count()
    test_count, suite_count = get_test_counts()
    core_lines = get_core_line_count()
    sorry_count = get_sorry_count()
    exclusion_count = get_exclusion_count()
    covered_count, coverage_pct = get_covered_count(total_theorems)
    stdlib_count = per_contract.get("Stdlib", 0)

    return {
        "schema_version": 1,
        "theorems": {
            "total": total_theorems,
            "categories": num_categories,
            "per_contract": per_contract,
            "covered": covered_count,
            "coverage_percent": coverage_pct,
            "excluded": exclusion_count,
            "proven": max(0, total_theorems - sorry_count),
            "stdlib": stdlib_count,
            "non_stdlib_total": total_theorems - stdlib_count,
        },
        "tests": {
            "foundry_functions": test_count,
            "suites": suite_count,
            "property_functions": get_property_test_function_count(),
            "differential_total": get_diff_test_total(),
        },
        "proofs": {
            "axioms": axiom_count,
            "sorry": sorry_count,
        },
        "codebase": {
            "core_lines": core_lines,
            "example_contracts": get_contract_count(),
        },
        "toolchain": {
            "lean": get_lean_toolchain(),
            "solc": get_solc_version(),
        },
    }


def _expect_exact_keys(path: Path, section: str, payload: dict[str, Any], expected: set[str]) -> None:
    unknown = sorted(set(payload.keys()) - expected)
    if unknown:
        raise ValueError(f"{path}: {section}: unknown keys: {', '.join(unknown)}")
    missing = sorted(expected - set(payload.keys()))
    if missing:
        raise ValueError(f"{path}: {section}: missing required keys: {', '.join(missing)}")


def _expect_int(path: Path, field_path: str, value: Any) -> int:
    if type(value) is not int:
        raise ValueError(f"{path}: {field_path} must be an integer, got {type(value).__name__}")
    return value


def _expect_non_negative_int(path: Path, field_path: str, value: Any) -> int:
    parsed = _expect_int(path, field_path, value)
    if parsed < 0:
        raise ValueError(f"{path}: {field_path} must be >= 0")
    return parsed


def _expect_str(path: Path, field_path: str, value: Any) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{path}: {field_path} must be a string, got {type(value).__name__}")
    return value


def load_metrics_from_artifact(path: Path) -> dict[str, Any]:
    """Load and strictly validate verification status artifact JSON."""
    if not path.exists():
        raise FileNotFoundError(f"{path}: verification status artifact not found")
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"{path}: artifact payload must be a JSON object")

    top_keys = {"schema_version", "theorems", "tests", "proofs", "codebase", "toolchain"}
    _expect_exact_keys(path, "root", data, top_keys)
    schema_version = _expect_int(path, "schema_version", data["schema_version"])
    if schema_version != 1:
        raise ValueError(f"{path}: expected schema_version=1, got {schema_version!r}")

    theorems = data["theorems"]
    tests = data["tests"]
    proofs = data["proofs"]
    codebase = data["codebase"]
    toolchain = data["toolchain"]
    for name, section in (
        ("theorems", theorems),
        ("tests", tests),
        ("proofs", proofs),
        ("codebase", codebase),
        ("toolchain", toolchain),
    ):
        if not isinstance(section, dict):
            raise ValueError(f"{path}: {name} must be an object")

    _expect_exact_keys(
        path,
        "theorems",
        theorems,
        {
            "total",
            "categories",
            "per_contract",
            "covered",
            "coverage_percent",
            "excluded",
            "proven",
            "stdlib",
            "non_stdlib_total",
        },
    )
    _expect_non_negative_int(path, "theorems.total", theorems["total"])
    _expect_non_negative_int(path, "theorems.categories", theorems["categories"])
    per_contract = theorems["per_contract"]
    if not isinstance(per_contract, dict):
        raise ValueError(f"{path}: theorems.per_contract must be an object")
    for contract, count in per_contract.items():
        if not isinstance(contract, str):
            raise ValueError(
                f"{path}: theorems.per_contract keys must be strings, got {type(contract).__name__}"
            )
        _expect_non_negative_int(path, f"theorems.per_contract[{contract!r}]", count)
    _expect_non_negative_int(path, "theorems.covered", theorems["covered"])
    _expect_non_negative_int(path, "theorems.coverage_percent", theorems["coverage_percent"])
    _expect_non_negative_int(path, "theorems.excluded", theorems["excluded"])
    _expect_non_negative_int(path, "theorems.proven", theorems["proven"])
    _expect_non_negative_int(path, "theorems.stdlib", theorems["stdlib"])
    _expect_non_negative_int(path, "theorems.non_stdlib_total", theorems["non_stdlib_total"])

    _expect_exact_keys(
        path,
        "tests",
        tests,
        {"foundry_functions", "suites", "property_functions", "differential_total"},
    )
    _expect_non_negative_int(path, "tests.foundry_functions", tests["foundry_functions"])
    _expect_non_negative_int(path, "tests.suites", tests["suites"])
    _expect_non_negative_int(path, "tests.property_functions", tests["property_functions"])
    _expect_non_negative_int(path, "tests.differential_total", tests["differential_total"])

    _expect_exact_keys(path, "proofs", proofs, {"axioms", "sorry"})
    _expect_non_negative_int(path, "proofs.axioms", proofs["axioms"])
    _expect_non_negative_int(path, "proofs.sorry", proofs["sorry"])

    _expect_exact_keys(path, "codebase", codebase, {"core_lines", "example_contracts"})
    _expect_non_negative_int(path, "codebase.core_lines", codebase["core_lines"])
    _expect_non_negative_int(path, "codebase.example_contracts", codebase["example_contracts"])

    _expect_exact_keys(path, "toolchain", toolchain, {"lean", "solc"})
    _expect_str(path, "toolchain.lean", toolchain["lean"])
    _expect_str(path, "toolchain.solc", toolchain["solc"])

    return data
