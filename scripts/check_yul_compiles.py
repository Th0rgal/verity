#!/usr/bin/env python3
"""Verify that generated Yul files compile with solc.

This check ensures trust in the Yul->EVM compilation step by verifying
that all generated Yul can be compiled to bytecode by solc.
"""

from __future__ import annotations

import subprocess
from pathlib import Path

from property_utils import report_errors

ROOT = Path(__file__).resolve().parents[1]
YUL_DIRS = [ROOT / "compiler" / "yul"]


def collect_yul_files() -> list[Path]:
    files: list[Path] = []
    for yul_dir in YUL_DIRS:
        if not yul_dir.exists():
            continue
        files.extend(sorted(yul_dir.glob("*.yul")))
    return files


def run_solc(path: Path) -> tuple[int, str, str]:
    result = subprocess.run(
        ["solc", "--strict-assembly", "--bin", str(path)],
        capture_output=True,
        text=True,
        check=False,
    )
    return result.returncode, result.stdout, result.stderr


def main() -> None:
    files = collect_yul_files()
    if not files:
        raise SystemExit("No generated Yul files found in compiler/yul")

    failures: list[str] = []
    for path in files:
        code, stdout, stderr = run_solc(path)
        if code != 0:
            failures.append(f"{path}: solc failed\n{stderr.strip()}")
            continue
        if not stdout.strip():
            failures.append(f"{path}: solc returned no output")

    report_errors(failures, "Yul->EVM compilation failed")

    print(f"Yul->EVM compilation check passed ({len(files)} files).")


if __name__ == "__main__":
    main()
