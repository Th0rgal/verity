#!/usr/bin/env python3
"""Report theorems that lack property test coverage."""

from __future__ import annotations

import argparse

from property_utils import (
    collect_covered,
    load_exclusions,
    load_manifest,
)


def snake_to_camel(name: str) -> str:
    """Convert snake_case to CamelCase.

    Args:
        name: Snake-case identifier (may contain apostrophes).

    Returns:
        CamelCase identifier.

    Example:
        >>> snake_to_camel("transfer_preserves_balance")
        'TransferPreservesBalance'
    """
    parts = [p for p in name.replace("'", "").split("_") if p]
    return "".join(part[:1].upper() + part[1:] for part in parts)


def main() -> None:
    parser = argparse.ArgumentParser(description="Report proof->test property gaps.")
    parser.add_argument("--stubs", action="store_true", help="Emit stub test templates.")
    args = parser.parse_args()

    manifest = load_manifest()
    exclusions = load_exclusions()
    covered = collect_covered()

    missing_total = 0
    for contract, names in sorted(manifest.items()):
        covered_names = covered.get(contract, set())
        excluded_names = exclusions.get(contract, set())
        missing = sorted(names - covered_names - excluded_names)
        if not missing:
            continue
        missing_total += len(missing)
        print(f"\n{contract}: {len(missing)} missing")
        for name in missing:
            print(f"  - {name}")
        if args.stubs:
            print("\n  // Stub templates")
            for name in missing:
                func_name = f"testProperty_{snake_to_camel(name)}"
                print("  /// Property: " + name)
                print(f"  function {func_name}() public {{")
                print("      // TODO: implement via proof->test extraction")
                print("      revert(\"TODO\");")
                print("  }")

    if missing_total == 0:
        print("All properties covered (respecting exclusions).")


if __name__ == "__main__":
    main()
