#!/usr/bin/env python3
"""Check static gas deltas between baseline and patch-enabled reports."""

from __future__ import annotations

import argparse
import math
import statistics
import sys
from dataclasses import dataclass
from pathlib import Path


STATIC_HEADER = "contract\tdeploy_upper_bound\truntime_upper_bound\ttotal_upper_bound"


@dataclass(frozen=True)
class GasRow:
    deploy: int
    runtime: int
    total: int


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--baseline-report",
        type=Path,
        required=True,
        help="Path to baseline (patch-disabled) static gas report.",
    )
    parser.add_argument(
        "--patched-report",
        type=Path,
        required=True,
        help="Path to patch-enabled static gas report.",
    )
    parser.add_argument(
        "--max-median-regression-pct",
        type=float,
        default=0.0,
        help="Maximum allowed median total-gas percent regression (default: 0.0).",
    )
    parser.add_argument(
        "--max-p90-regression-pct",
        type=float,
        default=0.0,
        help="Maximum allowed p90 total-gas percent regression (default: 0.0).",
    )
    parser.add_argument(
        "--min-improved-contracts",
        type=int,
        default=1,
        help="Require at least this many contracts with strictly lower total gas (default: 1).",
    )
    parser.add_argument(
        "--summary-markdown",
        type=Path,
        default=None,
        help="Optional markdown output path for CI summaries.",
    )
    return parser.parse_args()


def percentile(values: list[float], p: float) -> float:
    if not values:
        raise ValueError("percentile() requires at least one value")
    if len(values) == 1:
        return values[0]
    sorted_vals = sorted(values)
    rank = (len(sorted_vals) - 1) * p
    lo = math.floor(rank)
    hi = math.ceil(rank)
    if lo == hi:
        return sorted_vals[lo]
    weight = rank - lo
    return sorted_vals[lo] * (1.0 - weight) + sorted_vals[hi] * weight


def load_report(path: Path) -> dict[str, GasRow]:
    raw = path.read_text(encoding="utf-8")
    lines = [line.strip() for line in raw.splitlines() if line.strip()]
    if len(lines) < 3:
        raise ValueError(f"{path}: report is too short")
    if lines[1] != STATIC_HEADER:
        raise ValueError(f"{path}: invalid header line: {lines[1]!r}")

    rows: dict[str, GasRow] = {}
    for line in lines[2:]:
        cols = line.split("\t")
        if len(cols) != 4:
            raise ValueError(f"{path}: malformed row: {line!r}")
        name, deploy_raw, runtime_raw, total_raw = cols
        if name == "TOTAL":
            continue
        if name in rows:
            raise ValueError(f"{path}: duplicate contract row: {name}")
        deploy = int(deploy_raw)
        runtime = int(runtime_raw)
        total = int(total_raw)
        if total != deploy + runtime:
            raise ValueError(f"{path}: invalid arithmetic for {name}")
        rows[name] = GasRow(deploy=deploy, runtime=runtime, total=total)

    if not rows:
        raise ValueError(f"{path}: no contract rows found")
    return rows


def format_delta_pct(value: float) -> str:
    if math.isinf(value):
        return "+inf%" if value > 0 else "-inf%"
    return f"{value:+.2f}%"


def percent_delta(baseline: int, patched: int) -> float:
    delta = patched - baseline
    if baseline == 0:
        if patched == 0:
            return 0.0
        if patched > 0:
            return math.inf
        return -math.inf
    return delta / baseline * 100.0


def render_markdown(
    median_total_delta_pct: float,
    p90_total_delta_pct: float,
    median_deploy_delta_pct: float,
    p90_deploy_delta_pct: float,
    median_runtime_delta_pct: float,
    p90_runtime_delta_pct: float,
    improved_count: int,
    unchanged_count: int,
    regressed_count: int,
    best: list[tuple[str, int, float]],
    worst: list[tuple[str, int, float]],
) -> str:
    lines: list[str] = []
    lines.append("### Static Gas Delta (Patched vs Baseline)")
    lines.append("")
    lines.append("| Metric | Value |")
    lines.append("| :-- | --: |")
    lines.append(f"| Median total delta | {format_delta_pct(median_total_delta_pct)} |")
    lines.append(f"| P90 total delta | {format_delta_pct(p90_total_delta_pct)} |")
    lines.append(f"| Median deploy delta | {format_delta_pct(median_deploy_delta_pct)} |")
    lines.append(f"| P90 deploy delta | {format_delta_pct(p90_deploy_delta_pct)} |")
    lines.append(f"| Median runtime delta | {format_delta_pct(median_runtime_delta_pct)} |")
    lines.append(f"| P90 runtime delta | {format_delta_pct(p90_runtime_delta_pct)} |")
    lines.append(f"| Improved contracts | {improved_count} |")
    lines.append(f"| Unchanged contracts | {unchanged_count} |")
    lines.append(f"| Regressed contracts | {regressed_count} |")
    lines.append("")
    if best:
        lines.append("Top improvements:")
        lines.append("| Contract | Delta Gas | Delta % |")
        lines.append("| :-- | --: | --: |")
        for name, delta, pct in best:
            lines.append(f"| `{name}` | {delta} | {format_delta_pct(pct)} |")
        lines.append("")
    if worst:
        lines.append("Top regressions:")
        lines.append("| Contract | Delta Gas | Delta % |")
        lines.append("| :-- | --: | --: |")
        for name, delta, pct in worst:
            lines.append(f"| `{name}` | {delta} | {format_delta_pct(pct)} |")
        lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    try:
        baseline = load_report(args.baseline_report)
        patched = load_report(args.patched_report)
    except ValueError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    baseline_names = set(baseline)
    patched_names = set(patched)
    if baseline_names != patched_names:
        missing_in_patched = sorted(baseline_names - patched_names)
        missing_in_baseline = sorted(patched_names - baseline_names)
        if missing_in_patched:
            print(
                "ERROR: patched report missing contracts present in baseline: "
                + ", ".join(missing_in_patched),
                file=sys.stderr,
            )
        if missing_in_baseline:
            print(
                "ERROR: baseline report missing contracts present in patched report: "
                + ", ".join(missing_in_baseline),
                file=sys.stderr,
            )
        return 1

    total_deltas_pct: list[float] = []
    deploy_deltas_pct: list[float] = []
    runtime_deltas_pct: list[float] = []
    improvements: list[tuple[str, int, float]] = []
    regressions: list[tuple[str, int, float]] = []
    unchanged_count = 0

    for name in sorted(baseline_names):
        base = baseline[name]
        pat = patched[name]
        delta = pat.total - base.total
        pct = percent_delta(base.total, pat.total)
        total_deltas_pct.append(pct)
        deploy_deltas_pct.append(percent_delta(base.deploy, pat.deploy))
        runtime_deltas_pct.append(percent_delta(base.runtime, pat.runtime))
        if delta < 0:
            improvements.append((name, delta, pct))
        elif delta > 0:
            regressions.append((name, delta, pct))
        else:
            unchanged_count += 1

    median_total_delta_pct = statistics.median(total_deltas_pct)
    p90_total_delta_pct = percentile(total_deltas_pct, 0.90)
    median_deploy_delta_pct = statistics.median(deploy_deltas_pct)
    p90_deploy_delta_pct = percentile(deploy_deltas_pct, 0.90)
    median_runtime_delta_pct = statistics.median(runtime_deltas_pct)
    p90_runtime_delta_pct = percentile(runtime_deltas_pct, 0.90)
    improved_count = len(improvements)
    regressed_count = len(regressions)

    best = sorted(improvements, key=lambda row: row[1])[:5]
    worst = sorted(regressions, key=lambda row: row[1], reverse=True)[:5]
    summary = render_markdown(
        median_total_delta_pct=median_total_delta_pct,
        p90_total_delta_pct=p90_total_delta_pct,
        median_deploy_delta_pct=median_deploy_delta_pct,
        p90_deploy_delta_pct=p90_deploy_delta_pct,
        median_runtime_delta_pct=median_runtime_delta_pct,
        p90_runtime_delta_pct=p90_runtime_delta_pct,
        improved_count=improved_count,
        unchanged_count=unchanged_count,
        regressed_count=regressed_count,
        best=best,
        worst=worst,
    )
    print(summary)

    if args.summary_markdown is not None:
        args.summary_markdown.write_text(summary + "\n", encoding="utf-8")

    failures: list[str] = []
    if median_total_delta_pct > args.max_median_regression_pct:
        failures.append(
            f"median regression {median_total_delta_pct:.2f}% exceeds {args.max_median_regression_pct:.2f}%"
        )
    if p90_total_delta_pct > args.max_p90_regression_pct:
        failures.append(
            f"p90 regression {p90_total_delta_pct:.2f}% exceeds {args.max_p90_regression_pct:.2f}%"
        )
    if improved_count < args.min_improved_contracts:
        failures.append(
            f"improved contracts {improved_count} is below required minimum {args.min_improved_contracts}"
        )

    if failures:
        print("ERROR: patch gas delta check failed:", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        return 1

    print(
        "OK: patch gas delta check passed "
        f"(median={median_total_delta_pct:.2f}%, p90={p90_total_delta_pct:.2f}%, improved={improved_count})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
