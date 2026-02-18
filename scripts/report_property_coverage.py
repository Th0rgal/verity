#!/usr/bin/env python3
"""Generate comprehensive property test coverage report with statistics."""

from __future__ import annotations

import argparse
import sys

from property_utils import (
    collect_covered,
    load_exclusions,
    load_manifest,
)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate property test coverage report with statistics."
    )
    parser.add_argument(
        "--format",
        choices=["text", "markdown", "json"],
        default="text",
        help="Output format (default: text)",
    )
    parser.add_argument(
        "--fail-below",
        type=float,
        help="Exit with code 1 if overall coverage is below this percentage",
    )
    args = parser.parse_args()

    manifest = load_manifest()
    exclusions = load_exclusions()
    covered = collect_covered()

    # Calculate statistics per contract
    stats = {}
    total_properties = 0
    total_covered = 0
    total_exclusions = 0

    for contract in sorted(manifest.keys()):
        properties = manifest[contract]
        covered_props = covered.get(contract, set())
        excluded_props = exclusions.get(contract, set())

        count_total = len(properties)
        count_covered = len(covered_props)
        count_excluded = len(excluded_props)
        count_missing = count_total - count_covered - count_excluded
        coverage_pct = (count_covered / count_total * 100) if count_total > 0 else 0

        stats[contract] = {
            "total": count_total,
            "covered": count_covered,
            "excluded": count_excluded,
            "missing": count_missing,
            "coverage": coverage_pct,
        }

        total_properties += count_total
        total_covered += count_covered
        total_exclusions += count_excluded

    overall_coverage = (
        (total_covered / total_properties * 100) if total_properties > 0 else 0
    )

    # Output in requested format
    if args.format == "text":
        print_text_report(stats, total_properties, total_covered, total_exclusions, overall_coverage)
    elif args.format == "markdown":
        print_markdown_report(stats, total_properties, total_covered, total_exclusions, overall_coverage)
    elif args.format == "json":
        import json
        total_missing = total_properties - total_covered - total_exclusions
        report = {
            "overall": {
                "total": total_properties,
                "covered": total_covered,
                "excluded": total_exclusions,
                "missing": total_missing,
                "coverage": round(overall_coverage, 2),
            },
            "contracts": {
                contract: {
                    "total": s["total"],
                    "covered": s["covered"],
                    "excluded": s["excluded"],
                    "missing": s["missing"],
                    "coverage": round(s["coverage"], 2),
                }
                for contract, s in stats.items()
            },
        }
        print(json.dumps(report, indent=2))

    # Check coverage threshold
    if args.fail_below is not None and overall_coverage < args.fail_below:
        print(
            f"\n❌ Coverage {overall_coverage:.1f}% is below threshold {args.fail_below}%",
            file=sys.stderr,
        )
        sys.exit(1)


def print_text_report(stats, total_properties, total_covered, total_exclusions, overall_coverage):
    """Print coverage report in text format."""
    print("=" * 80)
    print("PROPERTY TEST COVERAGE REPORT")
    print("=" * 80)
    print()

    # Contract-by-contract breakdown
    for contract, s in stats.items():
        status_icon = "✅" if s["missing"] == 0 else "⚠️" if s["coverage"] >= 80 else "❌"
        print(f"{status_icon} {contract}")
        print(f"   Total:      {s['total']:3d} properties")
        print(f"   Covered:    {s['covered']:3d} ({s['coverage']:5.1f}%)")
        print(f"   Excluded:   {s['excluded']:3d} (proof-only)")
        if s["missing"] > 0:
            print(f"   Missing:    {s['missing']:3d} ⚠️")
        print()

    # Overall statistics
    print("=" * 80)
    print("OVERALL STATISTICS")
    print("=" * 80)
    print(f"Total Properties:     {total_properties:4d}")
    print(f"Covered Properties:   {total_covered:4d} ({overall_coverage:5.1f}%)")
    print(f"Excluded Properties:  {total_exclusions:4d} (proof-only)")
    print(f"Missing Properties:   {total_properties - total_covered - total_exclusions:4d}")
    print()

    # Summary
    if total_properties - total_covered - total_exclusions == 0:
        print("✅ All addressable properties are covered!")
    else:
        print(f"⚠️  {total_properties - total_covered - total_exclusions} properties still need coverage")


def print_markdown_report(stats, total_properties, total_covered, total_exclusions, overall_coverage):
    """Print coverage report in markdown format."""
    print("# Property Test Coverage Report")
    print()
    print("## Summary")
    print()
    print(f"- **Total Properties**: {total_properties}")
    print(f"- **Covered**: {total_covered} ({overall_coverage:.1f}%)")
    print(f"- **Excluded**: {total_exclusions} (proof-only)")
    print(f"- **Missing**: {total_properties - total_covered - total_exclusions}")
    print()
    print("## Contract Breakdown")
    print()
    print("| Contract | Total | Covered | Coverage | Excluded | Missing |")
    print("|----------|-------|---------|----------|----------|---------|")

    for contract, s in stats.items():
        status = "✅" if s["missing"] == 0 else "⚠️" if s["coverage"] >= 80 else "❌"
        print(
            f"| {status} {contract} | {s['total']} | {s['covered']} | "
            f"{s['coverage']:.1f}% | {s['excluded']} | {s['missing']} |"
        )


if __name__ == "__main__":
    main()
