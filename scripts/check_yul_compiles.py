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
    parser.add_argument(
        "--allow-compare-diff-file",
        type=str,
        help=(
            "Optional allowlist for known compare diffs. "
            "Format: one entry per line as "
            "'mismatch:<file>', 'missing_in_a:<file>', or 'missing_in_b:<file>'."
        ),
    )
    return parser.parse_args()


def resolve_dir(path_str: str) -> Path:
    path = Path(path_str)
    return path if path.is_absolute() else (ROOT / path)


def collect_yul_files(yul_dirs: list[Path]) -> tuple[list[Path], list[str]]:
    files: list[Path] = []
    failures: list[str] = []
    for yul_dir in yul_dirs:
        if not yul_dir.exists():
            failures.append(f"Missing Yul directory: {yul_dir}")
            continue
        dir_files = sorted(yul_dir.glob("*.yul"))
        if not dir_files:
            failures.append(f"No Yul files found in requested directory: {yul_dir}")
            continue
        files.extend(dir_files)
    return files, failures


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


def load_allowed_compare_diffs(path: str | None) -> set[tuple[str, str]]:
    if path is None:
        return set()

    allow_path = resolve_dir(path)
    if not allow_path.exists():
        raise SystemExit(f"Allowlist file not found: {allow_path}")

    allowed: set[tuple[str, str]] = set()
    for raw_line in allow_path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if ":" not in line:
            raise SystemExit(
                f"Invalid allowlist entry '{line}' in {allow_path}; expected '<kind>:<file>'"
            )
        kind, name = line.split(":", 1)
        kind = kind.strip()
        name = name.strip()
        if kind not in {"mismatch", "missing_in_a", "missing_in_b"} or not name:
            raise SystemExit(
                f"Invalid allowlist entry '{line}' in {allow_path}; "
                "kind must be mismatch|missing_in_a|missing_in_b"
            )
        allowed.add((kind, name))
    return allowed


def main() -> None:
    args = parse_args()
    yul_dirs = [resolve_dir(d) for d in (args.dirs or [str(YUL_DIR)])]
    files, failures = collect_yul_files(yul_dirs)
    if not files and not failures:
        checked = ", ".join(str(path) for path in yul_dirs)
        failures.append(f"No generated Yul files found in: {checked}")

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
        allowed_diffs = load_allowed_compare_diffs(args.allow_compare_diff_file)
        seen_diffs: set[tuple[str, str]] = set()
        dir_a = resolve_dir(args.compare_dirs[0])
        dir_b = resolve_dir(args.compare_dirs[1])
        files_a = sorted(dir_a.glob("*.yul")) if dir_a.exists() else []
        files_b = sorted(dir_b.glob("*.yul")) if dir_b.exists() else []
        if not dir_a.exists():
            failures.append(f"Compare directory does not exist: {dir_a}")
        if not dir_b.exists():
            failures.append(f"Compare directory does not exist: {dir_b}")
        if dir_a.exists() and not files_a:
            failures.append(f"No Yul files found in compare directory: {dir_a}")
        if dir_b.exists() and not files_b:
            failures.append(f"No Yul files found in compare directory: {dir_b}")
        if dir_a.exists() and dir_b.exists() and files_a and files_b:
            by_name_a = index_by_filename(files_a, dir_a)
            by_name_b = index_by_filename(files_b, dir_b)

            names_a = set(by_name_a.keys())
            names_b = set(by_name_b.keys())
            only_a = sorted(names_a - names_b)
            only_b = sorted(names_b - names_a)
            if only_a:
                for name in only_a:
                    diff = ("missing_in_b", name)
                    seen_diffs.add(diff)
                    if diff not in allowed_diffs:
                        failures.append(f"{dir_b} missing file present in {dir_a}: {name}")
            if only_b:
                for name in only_b:
                    diff = ("missing_in_a", name)
                    seen_diffs.add(diff)
                    if diff not in allowed_diffs:
                        failures.append(f"{dir_a} missing file present in {dir_b}: {name}")

            for name in sorted(names_a & names_b):
                path_a = by_name_a[name]
                path_b = by_name_b[name]
                bytecode_a = bytecode_by_file.get(path_a)
                bytecode_b = bytecode_by_file.get(path_b)
                if bytecode_a is None or bytecode_b is None:
                    continue
                if bytecode_a != bytecode_b:
                    diff = ("mismatch", name)
                    seen_diffs.add(diff)
                    if diff not in allowed_diffs:
                        failures.append(f"Bytecode mismatch for {name}: {path_a} vs {path_b}")

            stale_allowed = sorted(allowed_diffs - seen_diffs)
            if stale_allowed:
                stale_rendered = ", ".join(f"{kind}:{name}" for kind, name in stale_allowed)
                failures.append(
                    "Allowlist contains stale compare diffs no longer present: "
                    f"{stale_rendered}"
                )

    report_errors(failures, "Yul->EVM compilation failed")

    print(f"Yul->EVM compilation check passed ({len(files)} files across {len(yul_dirs)} dirs).")
    if args.compare_dirs is not None:
        print(f"Bytecode parity check passed: {args.compare_dirs[0]} == {args.compare_dirs[1]}")


if __name__ == "__main__":
    main()
