#!/usr/bin/env python3
"""Run gas-related CI checks behind one entrypoint."""

from __future__ import annotations

import argparse

import check_gas_calibration
import check_gas_model_coverage
import check_gas_report


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    coverage = subparsers.add_parser("coverage")
    coverage.add_argument("--dir", dest="dirs", action="append", default=[])

    subparsers.add_parser("report")

    calibration = subparsers.add_parser("calibration")
    calibration.add_argument("--static-report")
    calibration.add_argument("--match-path", default=check_gas_calibration.DEFAULT_FOUNDRY_PATH_GLOB)
    calibration.add_argument("--foundry-report")
    calibration.add_argument("--tx-base-gas", type=int, default=check_gas_calibration.TX_BASE_GAS)
    calibration.add_argument(
        "--create-tx-base-gas",
        type=int,
        default=check_gas_calibration.CREATE_TX_BASE_GAS,
    )
    calibration.add_argument(
        "--code-deposit-gas-per-byte",
        type=int,
        default=check_gas_calibration.CODE_DEPOSIT_GAS_PER_BYTE,
    )
    calibration.add_argument("--allow-missing-contract", action="append", default=[])
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)

    if args.command == "coverage":
        coverage_args: list[str] = []
        for directory in args.dirs:
            coverage_args.extend(["--dir", directory])
        return check_gas_model_coverage.main(coverage_args)

    if args.command == "report":
        return check_gas_report.main()

    calibration_args: list[str] = []
    if args.static_report is not None:
        calibration_args.extend(["--static-report", args.static_report])
    if args.match_path != check_gas_calibration.DEFAULT_FOUNDRY_PATH_GLOB:
        calibration_args.extend(["--match-path", args.match_path])
    if args.foundry_report is not None:
        calibration_args.extend(["--foundry-report", args.foundry_report])
    if args.tx_base_gas != check_gas_calibration.TX_BASE_GAS:
        calibration_args.extend(["--tx-base-gas", str(args.tx_base_gas)])
    if args.create_tx_base_gas != check_gas_calibration.CREATE_TX_BASE_GAS:
        calibration_args.extend(["--create-tx-base-gas", str(args.create_tx_base_gas)])
    if args.code_deposit_gas_per_byte != check_gas_calibration.CODE_DEPOSIT_GAS_PER_BYTE:
        calibration_args.extend(
            ["--code-deposit-gas-per-byte", str(args.code_deposit_gas_per_byte)]
        )
    for contract in args.allow_missing_contract:
        calibration_args.extend(["--allow-missing-contract", contract])
    return check_gas_calibration.main(calibration_args)


if __name__ == "__main__":
    raise SystemExit(main())
