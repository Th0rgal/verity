#!/usr/bin/env python3
"""Check that all theorems in the manifest have property tests (or are excluded)."""

from __future__ import annotations

from property_utils import collect_covered, load_exclusions, load_manifest, report_errors


def main() -> None:
    manifest = load_manifest()
    exclusions = load_exclusions()
    covered = collect_covered()

    errors: list[str] = []

    for contract, names in exclusions.items():
        if contract not in manifest:
            errors.append(f"Exclusion contract not in manifest: {contract}")
            continue
        unknown = names - manifest[contract]
        if unknown:
            errors.append(
                f"Exclusions for {contract} include unknown theorem(s): {', '.join(sorted(unknown))}"
            )

    for contract, names in manifest.items():
        covered_names = covered.get(contract, set())
        excluded_names = exclusions.get(contract, set())
        stale = covered_names & excluded_names
        if stale:
            errors.append(
                f"{contract}: exclusions list covered theorem(s): {', '.join(sorted(stale))}"
            )
        missing = names - covered_names - excluded_names
        if missing:
            errors.append(
                f"{contract}: missing property tests for {len(missing)} theorem(s): {', '.join(sorted(missing))}"
            )

    report_errors(errors, "Property coverage check failed")
    print("Property coverage check passed.")


if __name__ == "__main__":
    main()
