#!/usr/bin/env python3
"""Enforce Lean warning baseline sync against a checked artifact.

Usage:
    python3 scripts/check_lean_warning_regression.py --log lake-build.log
    python3 scripts/check_lean_warning_regression.py --log lake-build.log --write-baseline artifacts/lean_warning_baseline.json
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path

from property_utils import ROOT

WARNING_RE = re.compile(r"^warning:\s+(.+?\.lean):\d+:\d+:\s+(.*)$")


def parse_warnings(log_path: Path) -> tuple[Counter[str], Counter[str]]:
    by_file: Counter[str] = Counter()
    by_message: Counter[str] = Counter()

    try:
        lines = log_path.read_text(encoding="utf-8").splitlines()
    except UnicodeDecodeError as exc:
        raise ValueError(f"{log_path}: invalid UTF-8 in log input") from exc

    for raw_line in lines:
        match = WARNING_RE.match(raw_line.strip())
        if not match:
            continue
        file_path, message = match.groups()
        # Skip warnings from dependency packages — we only track our own code.
        if "/lake-packages/" in file_path or "/.lake/packages/" in file_path:
            continue
        by_file[file_path] += 1
        by_message[message.strip()] += 1

    return by_file, by_message


def load_baseline(path: Path) -> dict[str, object]:
    if not path.exists():
        raise FileNotFoundError(f"Baseline file not found: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("Baseline payload must be a JSON object")
    return payload


def _validate_counter_field(
    baseline_path: Path,
    field_name: str,
    raw_counter: object,
) -> dict[str, int]:
    if not isinstance(raw_counter, dict):
        raise ValueError(f"{baseline_path}: '{field_name}' must be an object")

    normalized: dict[str, int] = {}
    for key, value in raw_counter.items():
        if not isinstance(key, str):
            raise ValueError(
                f"{baseline_path}: '{field_name}' keys must be strings, got {type(key).__name__}"
            )
        if type(value) is not int:
            raise ValueError(
                f"{baseline_path}: '{field_name}[{key}]' must be an integer, got {type(value).__name__}"
            )
        if value < 0:
            raise ValueError(f"{baseline_path}: '{field_name}[{key}]' must be >= 0")
        normalized[key] = value
    return normalized


def validate_baseline_schema(baseline_path: Path, payload: dict[str, object]) -> dict[str, object]:
    allowed_keys = {"schema_version", "total_warnings", "by_file", "by_message"}
    unknown_keys = sorted(set(payload.keys()) - allowed_keys)
    if unknown_keys:
        raise ValueError(f"{baseline_path}: unknown keys: {', '.join(unknown_keys)}")

    missing_keys = sorted(allowed_keys - set(payload.keys()))
    if missing_keys:
        raise ValueError(f"{baseline_path}: missing required keys: {', '.join(missing_keys)}")

    schema_version = payload["schema_version"]
    if type(schema_version) is not int or schema_version != 1:
        raise ValueError(f"{baseline_path}: expected schema_version=1, got {schema_version!r}")

    total_warnings = payload["total_warnings"]
    if type(total_warnings) is not int:
        raise ValueError(f"{baseline_path}: 'total_warnings' must be an integer")
    if total_warnings < 0:
        raise ValueError(f"{baseline_path}: 'total_warnings' must be >= 0")

    by_file = _validate_counter_field(baseline_path, "by_file", payload["by_file"])
    by_message = _validate_counter_field(baseline_path, "by_message", payload["by_message"])

    by_file_total = sum(by_file.values())
    by_message_total = sum(by_message.values())
    if by_file_total != total_warnings:
        raise ValueError(
            f"{baseline_path}: sum(by_file)={by_file_total} must equal total_warnings={total_warnings}"
        )
    if by_message_total != total_warnings:
        raise ValueError(
            f"{baseline_path}: sum(by_message)={by_message_total} must equal total_warnings={total_warnings}"
        )

    return {
        "schema_version": schema_version,
        "total_warnings": total_warnings,
        "by_file": by_file,
        "by_message": by_message,
    }


def normalize_counter_payload(payload: object | None) -> Counter[str]:
    if payload is None:
        return Counter()
    if not isinstance(payload, dict):
        raise ValueError(f"Expected counter payload object, got {type(payload).__name__}")
    return Counter({str(k): int(v) for k, v in payload.items()})


def render_sorted(counter: Counter[str]) -> dict[str, int]:
    return {k: counter[k] for k in sorted(counter)}


def write_baseline(path: Path, by_file: Counter[str], by_message: Counter[str]) -> None:
    payload = {
        "schema_version": 1,
        "total_warnings": int(sum(by_file.values())),
        "by_file": render_sorted(by_file),
        "by_message": render_sorted(by_message),
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def compare_against_baseline(
    baseline_path: Path,
    observed_by_file: Counter[str],
    observed_by_message: Counter[str],
) -> list[str]:
    errors: list[str] = []
    baseline = validate_baseline_schema(baseline_path, load_baseline(baseline_path))

    baseline_total = int(baseline.get("total_warnings", 0))
    baseline_by_file = normalize_counter_payload(baseline.get("by_file"))
    baseline_by_message = normalize_counter_payload(baseline.get("by_message"))

    observed_total = int(sum(observed_by_file.values()))
    if observed_total != baseline_total:
        errors.append(
            f"Total Lean warnings drifted: observed {observed_total}, baseline {baseline_total}"
        )

    for file_path in sorted(set(observed_by_file) | set(baseline_by_file)):
        observed_count = observed_by_file.get(file_path, 0)
        baseline_count = baseline_by_file.get(file_path, 0)
        if observed_count != baseline_count:
            errors.append(
                f"Warning count drifted in {file_path}: observed {observed_count}, "
                f"baseline {baseline_count}"
            )

    for message in sorted(set(observed_by_message) | set(baseline_by_message)):
        observed_count = observed_by_message.get(message, 0)
        baseline_count = baseline_by_message.get(message, 0)
        if observed_count != baseline_count:
            errors.append(
                f"Warning type drifted ({message}): observed {observed_count}, "
                f"baseline {baseline_count}"
            )

    return errors


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log", required=True, type=Path, help="Path to lake build output log")
    parser.add_argument(
        "--baseline",
        type=Path,
        default=ROOT / "artifacts" / "lean_warning_baseline.json",
        help="Baseline warning artifact to compare against",
    )
    parser.add_argument(
        "--write-baseline",
        type=Path,
        help="Write baseline artifact from current log and exit",
    )
    args = parser.parse_args(argv)

    by_file, by_message = parse_warnings(args.log)

    if args.write_baseline is not None:
        write_baseline(args.write_baseline, by_file, by_message)
        print(f"Wrote Lean warning baseline to {args.write_baseline}")
        return

    errors = compare_against_baseline(args.baseline, by_file, by_message)
    total = int(sum(by_file.values()))
    print(f"Lean warnings observed: {total}")
    if errors:
        print("\nLean warning baseline check failed:", file=sys.stderr)
        for err in errors:
            print(f"- {err}", file=sys.stderr)
        sys.exit(1)

    print(f"Lean warning baseline check passed against {args.baseline}")


if __name__ == "__main__":
    main()
