#!/usr/bin/env python3
"""Run Yul-related CI checks.

This merges the generated-Yul compilation/parity checks with the Lean builtin
boundary guard so Yul validation lives behind one entrypoint with targeted
flags for CI contexts that do not have solc installed.
"""

from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path

from property_utils import ROOT, report_errors, scrub_lean_code

PROOFS_DIR = ROOT / "Compiler" / "Proofs"
BUILTINS_FILE = PROOFS_DIR / "YulGeneration" / "Builtins.lean"
DEFAULT_YUL_DIR = ROOT / "artifacts" / "yul"
RUNTIME_INTERPRETERS = [
    PROOFS_DIR / "IRGeneration" / "IRInterpreter.lean",
    PROOFS_DIR / "YulGeneration" / "Semantics.lean",
]

IMPORT_BUILTINS_RE = re.compile(
    r"^\s*import\s+Compiler\.Proofs\.YulGeneration\.Builtins\s*$", re.MULTILINE
)
BUILTIN_CALL_RE = re.compile(
    r"\bCompiler\.Proofs\.YulGeneration\.(?:"
    r"evalBuiltinCall"
    r"|evalBuiltinCallWithContext"
    r"|evalBuiltinCallWithBackend"
    r"|evalBuiltinCallWithBackendContext"
    r")\b"
)
INLINE_DISPATCH_RE = re.compile(
    r'func\s*=\s*"(?:mappingSlot|sload|add|sub|mul|div|mod|lt|gt|eq|iszero|and|or|xor|not|shl|shr|caller|calldataload|address|timestamp)"'
)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run Yul builtin-boundary and generated-Yul compilation checks."
    )
    parser.add_argument(
        "--dir",
        dest="dirs",
        action="append",
        help="Yul directory to check (repeatable). Default: artifacts/yul",
    )
    parser.add_argument(
        "--compare-dirs",
        nargs=2,
        metavar=("DIR_A", "DIR_B"),
        help="Compare compiled bytecode parity by filename between two Yul directories.",
    )
    parser.add_argument(
        "--require-same-files",
        dest="same_file_pairs",
        action="append",
        nargs=2,
        metavar=("DIR_A", "DIR_B"),
        help=(
            "Require matching .yul filename sets between two directories (repeatable). "
            "Unlike --compare-dirs, this does not require bytecode parity."
        ),
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
    parser.add_argument(
        "--builtin-boundary-only",
        action="store_true",
        help="Run only the Lean builtin-boundary guard and skip solc compilation checks.",
    )
    parser.add_argument(
        "--skip-builtin-boundary",
        action="store_true",
        help="Skip the Lean builtin-boundary guard and run only generated-Yul checks.",
    )
    return parser.parse_args(argv)


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


def compare_filename_sets(
    dir_a: Path,
    files_a: list[Path],
    dir_b: Path,
    files_b: list[Path],
    failures: list[str],
    *,
    missing_a_label: str,
    missing_b_label: str,
) -> None:
    by_name_a = index_by_filename(files_a, dir_a)
    by_name_b = index_by_filename(files_b, dir_b)
    names_a = set(by_name_a.keys())
    names_b = set(by_name_b.keys())

    only_a = sorted(names_a - names_b)
    only_b = sorted(names_b - names_a)
    for name in only_a:
        failures.append(f"{missing_b_label}: {name}")
    for name in only_b:
        failures.append(f"{missing_a_label}: {name}")


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


def collect_builtin_boundary_failures() -> list[str]:
    failures: list[str] = []

    if not BUILTINS_FILE.exists():
        failures.append(f"{BUILTINS_FILE.relative_to(ROOT)}: missing builtin boundary module")

    for lean_file in RUNTIME_INTERPRETERS:
        text = scrub_lean_code(lean_file.read_text(encoding="utf-8"))
        rel = lean_file.relative_to(ROOT)

        if not IMPORT_BUILTINS_RE.search(text):
            failures.append(f"{rel}: missing import Compiler.Proofs.YulGeneration.Builtins")

        if not BUILTIN_CALL_RE.search(text):
            failures.append(
                f"{rel}: missing call to Compiler.Proofs.YulGeneration."
                "evalBuiltinCall, evalBuiltinCallWithContext, "
                "evalBuiltinCallWithBackend, or evalBuiltinCallWithBackendContext"
            )

        if INLINE_DISPATCH_RE.search(text):
            failures.append(
                f"{rel}: inline builtin dispatch detected; move builtin semantics to "
                "Compiler/Proofs/YulGeneration/Builtins.lean"
            )

    return failures


def run_compilation_checks(args: argparse.Namespace) -> tuple[list[str], int, int]:
    yul_dirs = [resolve_dir(d) for d in (args.dirs or [str(DEFAULT_YUL_DIR)])]
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

    compare_count = 0
    if args.compare_dirs is not None:
        compare_count += 1
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

    same_file_pairs = args.same_file_pairs or []
    compare_count += len(same_file_pairs)
    for raw_a, raw_b in same_file_pairs:
        dir_a = resolve_dir(raw_a)
        dir_b = resolve_dir(raw_b)
        files_a = sorted(dir_a.glob("*.yul")) if dir_a.exists() else []
        files_b = sorted(dir_b.glob("*.yul")) if dir_b.exists() else []
        if not dir_a.exists():
            failures.append(f"Same-file check directory does not exist: {dir_a}")
            continue
        if not dir_b.exists():
            failures.append(f"Same-file check directory does not exist: {dir_b}")
            continue
        if not files_a:
            failures.append(f"No Yul files found in same-file check directory: {dir_a}")
            continue
        if not files_b:
            failures.append(f"No Yul files found in same-file check directory: {dir_b}")
            continue
        compare_filename_sets(
            dir_a,
            files_a,
            dir_b,
            files_b,
            failures,
            missing_a_label=f"{dir_a} missing file present in {dir_b}",
            missing_b_label=f"{dir_b} missing file present in {dir_a}",
        )

    return failures, len(files), compare_count


def main(argv: list[str] | None = None) -> None:
    args = parse_args(argv)
    if args.builtin_boundary_only and args.skip_builtin_boundary:
        raise SystemExit("--builtin-boundary-only cannot be combined with --skip-builtin-boundary")

    failures: list[str] = []
    if not args.skip_builtin_boundary:
        failures.extend(collect_builtin_boundary_failures())

    checked_files = 0
    compare_count = 0
    if not args.builtin_boundary_only:
        compile_failures, checked_files, compare_count = run_compilation_checks(args)
        failures.extend(compile_failures)

    report_errors(failures, "Yul checks failed")

    if not args.skip_builtin_boundary:
        print("✓ Yul builtin boundary is enforced")
    if not args.builtin_boundary_only:
        print(
            f"Yul->EVM compilation check passed ({checked_files} files across "
            f"{len(args.dirs or [str(DEFAULT_YUL_DIR)])} dirs)."
        )
        if args.compare_dirs is not None:
            print(f"Bytecode parity check passed: {args.compare_dirs[0]} == {args.compare_dirs[1]}")
        if compare_count and args.compare_dirs is None:
            print(f"Filename parity check passed for {compare_count} directory pair(s).")


if __name__ == "__main__":
    main()
