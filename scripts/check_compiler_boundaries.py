#!/usr/bin/env python3
"""Run compiler-boundary CI checks behind one entrypoint."""

from __future__ import annotations

import argparse

import check_builtin_list_sync
import check_evmyullean_capability_boundary
import check_mapping_slot_boundary


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-builtin-list-sync", action="store_true")
    parser.add_argument("--skip-mapping-slot", action="store_true")
    parser.add_argument("--skip-evmyullean-capability", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)

    if not args.skip_builtin_list_sync:
        rc = check_builtin_list_sync.main()
        if rc != 0:
            return rc

    if not args.skip_mapping_slot:
        rc = check_mapping_slot_boundary.main()
        if rc != 0:
            return rc

    if not args.skip_evmyullean_capability:
        rc = check_evmyullean_capability_boundary.main()
        if rc != 0:
            return rc

    print("compiler boundary checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
