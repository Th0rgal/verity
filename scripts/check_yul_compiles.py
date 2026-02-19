#!/usr/bin/env python3
"""Verify that generated Yul files compile with solc.

This check ensures trust in the Yul->EVM compilation step by verifying
that all generated Yul can be compiled to bytecode by solc.
"""

from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path

from property_utils import ROOT, YUL_DIR, report_errors


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compile generated Yul with solc and optionally compare bytecode parity."
    )
    parser.add_argument(
        "--dir",
        dest="dirs",
        action="append",
        help="Yul directory to check (repeatable). Default: compiler/yul",
    )
    parser.add_argument(
        "--compare-dirs",
        nargs=2,
        metavar=("DIR_A", "DIR_B"),
        help="Compare compiled bytecode parity by filename between two Yul directories.",
    )
    return parser.parse_args()


def resolve_dir(path_str: str) -> Path:
    path = Path(path_str)
    return path if path.is_absolute() else (ROOT / path)


def collect_yul_files(yul_dirs: list[Path]) -> list[Path]:
    files: list[Path] = []
    for yul_dir in yul_dirs:
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


def extract_bytecode(stdout: str) -> str | None:
    lines = stdout.splitlines()
    for index, line in enumerate(lines):
        if line.strip() == "Binary representation:" and index + 1 < len(lines):
            candidate = lines[index + 1].strip()
            if re.fullmatch(r"[0-9a-fA-F]+", candidate):
                return candidate.lower()

    hex_lines = [line.strip() for line in lines if re.fullmatch(r"[0-9a-fA-F]+", line.strip())]
    if hex_lines:
        return max(hex_lines, key=len).lower()

    return None


def index_by_filename(files: list[Path], root: Path) -> dict[str, Path]:
    return {path.relative_to(root).name: path for path in files}


def main() -> None:
    args = parse_args()
    yul_dirs = [resolve_dir(d) for d in (args.dirs or [str(YUL_DIR)])]
    files = collect_yul_files(yul_dirs)
    if not files:
        checked = ", ".join(str(path) for path in yul_dirs)
        raise SystemExit(f"No generated Yul files found in: {checked}")

    failures: list[str] = []
    bytecode_by_file: dict[Path, str] = {}
    for path in files:
        code, stdout, stderr = run_solc(path)
        if code != 0:
            failures.append(f"{path}: solc failed\n{stderr.strip()}")
            continue
        bytecode = extract_bytecode(stdout)
        if bytecode is None:
            failures.append(f"{path}: could not parse bytecode from solc output")
            continue
        bytecode_by_file[path] = bytecode

    if args.compare_dirs is not None:
        dir_a = resolve_dir(args.compare_dirs[0])
        dir_b = resolve_dir(args.compare_dirs[1])
        files_a = sorted(dir_a.glob("*.yul"))
        files_b = sorted(dir_b.glob("*.yul"))
        by_name_a = index_by_filename(files_a, dir_a)
        by_name_b = index_by_filename(files_b, dir_b)

        names_a = set(by_name_a.keys())
        names_b = set(by_name_b.keys())
        only_a = sorted(names_a - names_b)
        only_b = sorted(names_b - names_a)
        if only_a:
            failures.append(f"{dir_b} missing files present in {dir_a}: {', '.join(only_a)}")
        if only_b:
            failures.append(f"{dir_a} missing files present in {dir_b}: {', '.join(only_b)}")

        for name in sorted(names_a & names_b):
            path_a = by_name_a[name]
            path_b = by_name_b[name]
            bytecode_a = bytecode_by_file.get(path_a)
            bytecode_b = bytecode_by_file.get(path_b)
            if bytecode_a is None or bytecode_b is None:
                continue
            if bytecode_a != bytecode_b:
                failures.append(f"Bytecode mismatch for {name}: {path_a} vs {path_b}")

    report_errors(failures, "Yul->EVM compilation failed")

    print(f"Yul->EVM compilation check passed ({len(files)} files across {len(yul_dirs)} dirs).")
    if args.compare_dirs is not None:
        print(f"Bytecode parity check passed: {args.compare_dirs[0]} == {args.compare_dirs[1]}")


if __name__ == "__main__":
    main()
