#!/usr/bin/env python3
"""Validate `lake exe gas-report` output and basic monotonicity invariants."""

from __future__ import annotations

import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent


@dataclass(frozen=True)
class Row:
    contract: str
    deploy: int
    runtime: int
    total: int


def run_gas_report(extra_args: list[str]) -> str:
    cmd = ["lake", "exe", "gas-report", *extra_args]
    proc = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr)
        raise RuntimeError(f"`{' '.join(cmd)}` failed with exit code {proc.returncode}")
    return proc.stdout


def parse_report(stdout: str) -> tuple[str, list[Row], Row]:
    lines = [line.strip() for line in stdout.splitlines() if line.strip()]
    if len(lines) < 4:
        raise ValueError(f"Unexpected report shape, expected >=4 non-empty lines, got {len(lines)}")

    config_line = lines[0]
    if not config_line.startswith("# gas-report "):
        raise ValueError(f"Missing config header line: {config_line}")

    expected_header = "contract\tdeploy_upper_bound\truntime_upper_bound\ttotal_upper_bound"
    if lines[1] != expected_header:
        raise ValueError(f"Unexpected table header: {lines[1]}")

    parsed_rows: list[Row] = []
    for raw in lines[2:]:
        parts = raw.split("\t")
        if len(parts) != 4:
            raise ValueError(f"Malformed report row: {raw}")
        name, deploy_s, runtime_s, total_s = parts
        try:
            deploy = int(deploy_s)
            runtime = int(runtime_s)
            total = int(total_s)
        except ValueError as exc:
            raise ValueError(f"Non-numeric gas values in row: {raw}") from exc
        if total != deploy + runtime:
            raise ValueError(f"Row total mismatch for {name}: {total} != {deploy} + {runtime}")
        parsed_rows.append(Row(name, deploy, runtime, total))

    if parsed_rows[-1].contract != "TOTAL":
        raise ValueError("Last row must be TOTAL")

    return config_line, parsed_rows[:-1], parsed_rows[-1]


def validate_totals(rows: list[Row], total_row: Row) -> None:
    summed_deploy = sum(r.deploy for r in rows)
    summed_runtime = sum(r.runtime for r in rows)
    summed_total = sum(r.total for r in rows)
    if total_row.deploy != summed_deploy:
        raise ValueError(f"TOTAL deploy mismatch: {total_row.deploy} != {summed_deploy}")
    if total_row.runtime != summed_runtime:
        raise ValueError(f"TOTAL runtime mismatch: {total_row.runtime} != {summed_runtime}")
    if total_row.total != summed_total:
        raise ValueError(f"TOTAL combined mismatch: {total_row.total} != {summed_total}")


def validate_monotonicity(default_rows: list[Row], conservative_rows: list[Row]) -> None:
    default_by_name = {r.contract: r for r in default_rows}
    conservative_by_name = {r.contract: r for r in conservative_rows}
    if default_by_name.keys() != conservative_by_name.keys():
        raise ValueError("Contract sets differ across gas-report configurations")
    for name in sorted(default_by_name):
        default_total = default_by_name[name].total
        conservative_total = conservative_by_name[name].total
        if conservative_total < default_total:
            raise ValueError(
                f"Monotonicity violated for {name}: conservative total {conservative_total} < default {default_total}"
            )


def main() -> int:
    try:
        _, default_rows, default_total = parse_report(run_gas_report([]))
        validate_totals(default_rows, default_total)

        conservative_args = ["--loop-iterations", "16", "--unknown-call-cost", "80000", "--fuel", "8192"]
        _, conservative_rows, conservative_total = parse_report(run_gas_report(conservative_args))
        validate_totals(conservative_rows, conservative_total)
        validate_monotonicity(default_rows, conservative_rows)
    except Exception as exc:  # pragma: no cover - CI entrypoint
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    print("OK: gas-report output shape, totals, and monotonicity checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
