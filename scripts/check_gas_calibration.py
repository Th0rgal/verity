#!/usr/bin/env python3
"""Cross-check static gas bounds against Foundry gas measurements."""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_FOUNDRY_PATH_GLOB = "test/yul/*.t.sol"
# Slightly above intrinsic transaction base to absorb calldata overhead in Foundry calls.
TX_BASE_GAS = 22000
CREATE_TX_BASE_GAS = 53000
CODE_DEPOSIT_GAS_PER_BYTE = 200

STATIC_HEADER = "contract\tdeploy_upper_bound\truntime_upper_bound\ttotal_upper_bound"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--static-report",
        type=Path,
        default=None,
        help="Path to precomputed `lake exe gas-report` output. If omitted, runs `lake exe gas-report`.",
    )
    parser.add_argument(
        "--match-path",
        default=DEFAULT_FOUNDRY_PATH_GLOB,
        help="Foundry --match-path pattern used when collecting gas report.",
    )
    parser.add_argument(
        "--foundry-report",
        type=Path,
        default=None,
        help="Path to precomputed Foundry gas report output. If omitted, runs `forge test --gas-report`.",
    )
    parser.add_argument(
        "--tx-base-gas",
        type=int,
        default=TX_BASE_GAS,
        help="Fixed call overhead added when comparing static runtime upper bound to Foundry call gas.",
    )
    parser.add_argument(
        "--create-tx-base-gas",
        type=int,
        default=CREATE_TX_BASE_GAS,
        help="Fixed deployment transaction overhead (tx base + create surcharge).",
    )
    parser.add_argument(
        "--code-deposit-gas-per-byte",
        type=int,
        default=CODE_DEPOSIT_GAS_PER_BYTE,
        help="Gas charged per deployed runtime bytecode byte.",
    )
    parser.add_argument(
        "--allow-missing-contract",
        action="append",
        default=[],
        help=(
            "Contract allowed to exist in static report but be absent from Foundry gas report. "
            "Can be repeated."
        ),
    )
    return parser.parse_args()


def run_command(cmd: list[str], env: dict[str, str] | None = None) -> str:
    proc = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
        env=env,
    )
    if proc.returncode != 0:
        if proc.stdout:
            sys.stderr.write(proc.stdout)
        if proc.stderr:
            sys.stderr.write(proc.stderr)
        raise RuntimeError(f"`{' '.join(cmd)}` failed with exit code {proc.returncode}")
    return proc.stdout


def load_static_bounds(path: Path | None) -> dict[str, tuple[int, int]]:
    if path is None:
        stdout = run_command(["lake", "exe", "gas-report"])
    else:
        stdout = path.read_text(encoding="utf-8")

    lines = [line.strip() for line in stdout.splitlines() if line.strip()]
    if len(lines) < 4:
        raise ValueError("Static gas report is too short")
    if lines[1] != STATIC_HEADER:
        raise ValueError(f"Unexpected static report header: {lines[1]}")

    bounds: dict[str, tuple[int, int]] = {}
    for raw in lines[2:]:
        parts = raw.split("\t")
        if len(parts) != 4:
            raise ValueError(f"Malformed static gas row: {raw}")
        contract, deploy, runtime, total = parts
        if contract == "TOTAL":
            continue
        deploy_n = int(deploy)
        runtime_n = int(runtime)
        if int(total) != deploy_n + runtime_n:
            raise ValueError(f"Invalid static total arithmetic for {contract}")
        bounds[contract] = (deploy_n, runtime_n)

    if not bounds:
        raise ValueError("No contract rows found in static gas report")
    return bounds


def run_foundry_gas_report(match_path: str) -> str:
    env = dict(os.environ)
    env.setdefault("FOUNDRY_PROFILE", "difftest")
    cmd = ["forge", "test", "--gas-report", "--match-path", match_path]
    return run_command(cmd, env=env)


def parse_cell_int(raw: str) -> int | None:
    cleaned = raw.strip().replace(",", "").replace("_", "")
    if not cleaned or not cleaned.isdigit():
        return None
    return int(cleaned)


def parse_table_cells(raw: str) -> list[str]:
    cells = [part.strip() for part in raw.split("|")]
    if len(cells) >= 2:
        return cells[1:-1]
    return []


def table_index(header: list[str], name: str) -> int:
    for i, cell in enumerate(header):
        if cell == name:
            return i
    return -1


def parse_foundry_report(stdout: str) -> tuple[dict[str, int], dict[str, tuple[int, int]]]:
    contract_header = re.compile(r"\|\s+[^|]*:(?P<name>[A-Za-z0-9_]+)\s+Contract\s*\|")
    observed_runtime: dict[str, int] = {}
    observed_deploy: dict[str, tuple[int, int]] = {}
    current: str | None = None
    mode: str | None = None
    deploy_gas_idx = -1
    deploy_size_idx = -1
    runtime_name_idx = -1
    runtime_max_idx = -1

    for raw in stdout.splitlines():
        m = contract_header.search(raw)
        if m:
            current = m.group("name")
            observed_runtime.setdefault(current, 0)
            mode = None
            deploy_gas_idx = -1
            deploy_size_idx = -1
            runtime_name_idx = -1
            runtime_max_idx = -1
            continue

        if current is None or "|" not in raw:
            continue
        stripped = raw.strip()
        if stripped.startswith("| Deployment Cost"):
            header = parse_table_cells(raw)
            deploy_gas_idx = table_index(header, "Deployment Cost")
            deploy_size_idx = table_index(header, "Deployment Size")
            mode = None
            continue
        if stripped.startswith("| Function Name"):
            header = parse_table_cells(raw)
            runtime_name_idx = table_index(header, "Function Name")
            runtime_max_idx = table_index(header, "Max")
            mode = "runtime"
            continue
        if set(stripped) <= {"|", "-", "+", "=", "╭", "╰", "╮", "╯"}:
            continue

        cols = parse_table_cells(raw)
        if not cols:
            continue

        if deploy_gas_idx >= 0 and deploy_size_idx >= 0 and max(deploy_gas_idx, deploy_size_idx) < len(cols):
            deploy_gas = parse_cell_int(cols[deploy_gas_idx])
            deploy_size = parse_cell_int(cols[deploy_size_idx])
            if deploy_gas is not None and deploy_size is not None:
                observed_deploy[current] = (deploy_gas, deploy_size)
                deploy_gas_idx = -1
                deploy_size_idx = -1
                continue
            deploy_gas_idx = -1
            deploy_size_idx = -1

        if mode != "runtime" or runtime_name_idx < 0 or runtime_max_idx < 0:
            continue
        if max(runtime_name_idx, runtime_max_idx) >= len(cols):
            continue

        fn_name = cols[runtime_name_idx]
        if not fn_name or fn_name in {"Function Name", "Deployment Cost"}:
            continue

        max_col = cols[runtime_max_idx]
        max_gas = parse_cell_int(max_col)
        if max_gas is None:
            continue

        if max_gas > observed_runtime[current]:
            observed_runtime[current] = max_gas

    observed_runtime = {k: v for k, v in observed_runtime.items() if v > 0}
    if not observed_runtime:
        raise ValueError("No Foundry function gas rows parsed from gas report output")
    if not observed_deploy:
        raise ValueError("No Foundry deployment rows parsed from gas report output")
    return observed_runtime, observed_deploy


def validate_runtime_bounds(
    static_bounds: dict[str, tuple[int, int]],
    foundry_runtime: dict[str, int],
    tx_base_gas: int,
) -> list[str]:
    failures: list[str] = []
    for contract, observed in sorted(foundry_runtime.items()):
        static = static_bounds.get(contract)
        if static is None:
            failures.append(f"{contract}: missing in static gas report")
            continue
        _, static_runtime = static
        bound = static_runtime + tx_base_gas
        if observed > bound:
            failures.append(
                f"{contract}: foundry max {observed} exceeds static+txBase {bound} (static={static_runtime}, txBase={tx_base_gas})"
            )
    return failures


def validate_deploy_bounds(
    static_bounds: dict[str, tuple[int, int]],
    foundry_deploy: dict[str, tuple[int, int]],
    create_tx_base_gas: int,
    code_deposit_gas_per_byte: int,
) -> list[str]:
    failures: list[str] = []
    for contract, (observed_deploy, deploy_size) in sorted(foundry_deploy.items()):
        static = static_bounds.get(contract)
        if static is None:
            failures.append(f"{contract}: missing in static gas report")
            continue
        static_deploy, _ = static
        bound = static_deploy + create_tx_base_gas + code_deposit_gas_per_byte * deploy_size
        if observed_deploy > bound:
            failures.append(
                f"{contract}: deployment {observed_deploy} exceeds static+createOverhead {bound} "
                f"(staticDeploy={static_deploy}, createTxBase={create_tx_base_gas}, "
                f"depositPerByte={code_deposit_gas_per_byte}, deploySize={deploy_size})"
            )
    return failures


def validate_contract_coverage(
    static_bounds: dict[str, tuple[int, int]],
    foundry_runtime: dict[str, int],
    foundry_deploy: dict[str, tuple[int, int]],
    allowed_missing: set[str],
) -> list[str]:
    failures: list[str] = []
    foundry_all = set(foundry_runtime).union(foundry_deploy)
    for contract in sorted(set(static_bounds).difference(foundry_all).difference(allowed_missing)):
        failures.append(
            f"{contract}: present in static gas report but missing in Foundry gas report "
            "(no runtime/deploy measurements found)"
        )
    return failures


def main() -> int:
    args = parse_args()
    try:
        static_bounds = load_static_bounds(args.static_report)
        if args.foundry_report is None:
            foundry_stdout = run_foundry_gas_report(args.match_path)
        else:
            foundry_stdout = args.foundry_report.read_text(encoding="utf-8")
        foundry_runtime, foundry_deploy = parse_foundry_report(foundry_stdout)
        allowed_missing = set(args.allow_missing_contract)
        failures = validate_runtime_bounds(static_bounds, foundry_runtime, args.tx_base_gas)
        failures.extend(
            validate_deploy_bounds(
                static_bounds,
                foundry_deploy,
                args.create_tx_base_gas,
                args.code_deposit_gas_per_byte,
            )
        )
        failures.extend(
            validate_contract_coverage(
                static_bounds,
                foundry_runtime,
                foundry_deploy,
                allowed_missing,
            )
        )
    except Exception as exc:  # pragma: no cover - CI entrypoint
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    if failures:
        print("ERROR: static-vs-foundry gas calibration check failed:", file=sys.stderr)
        for line in failures:
            print(f"  - {line}", file=sys.stderr)
        return 1

    runtime_overlap = sorted(set(static_bounds).intersection(foundry_runtime))
    deploy_overlap = sorted(set(static_bounds).intersection(foundry_deploy))
    print(
        "OK: static bounds dominate Foundry gas "
        f"(runtime contracts={len(runtime_overlap)}, deploy contracts={len(deploy_overlap)}, "
        f"static contracts={len(static_bounds)}, "
        f"tx_base_gas={args.tx_base_gas}, create_tx_base_gas={args.create_tx_base_gas}, "
        f"code_deposit_gas_per_byte={args.code_deposit_gas_per_byte})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
