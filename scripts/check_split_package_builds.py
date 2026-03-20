#!/usr/bin/env python3
"""Build each split Lake package independently to guard package decoupling."""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
from pathlib import Path

from property_utils import ROOT

DEFAULT_PACKAGES = [
    "packages/verity-edsl",
    "packages/verity-compiler",
    "packages/verity-examples",
]


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--package",
        action="append",
        dest="packages",
        default=[],
        help="Package directory relative to repo root. May be passed multiple times.",
    )
    return parser.parse_args(argv)


def resolve_packages(package_args: list[str]) -> list[Path]:
    rel_paths = package_args or DEFAULT_PACKAGES
    return [ROOT / rel_path for rel_path in rel_paths]


def display_path(package_dir: Path) -> Path:
    try:
        return package_dir.relative_to(ROOT)
    except ValueError:
        return package_dir


def seed_packages_dir(package_dir: Path) -> None:
    root_packages_dir = ROOT / ".lake" / "packages"
    if not root_packages_dir.is_dir():
        return

    package_lake_dir = package_dir / ".lake"
    package_lake_dir.mkdir(exist_ok=True)
    package_packages_dir = package_lake_dir / "packages"
    if package_packages_dir.exists():
        return

    try:
        package_packages_dir.symlink_to(root_packages_dir, target_is_directory=True)
    except OSError:
        # Fall back to a local copy when symlinks are unavailable.
        shutil.copytree(root_packages_dir, package_packages_dir, symlinks=True)


def run_lake_build(package_dir: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "build"],
        cwd=package_dir,
        check=False,
        capture_output=True,
        text=True,
    )


def check_split_package_builds(package_dirs: list[Path]) -> int:
    failures: list[str] = []
    for package_dir in package_dirs:
        rel_path = display_path(package_dir)
        if not package_dir.exists():
            failures.append(f"{rel_path}: package directory does not exist")
            continue
        if not package_dir.is_dir():
            failures.append(f"{rel_path}: package path is not a directory")
            continue
        if not any((package_dir / lakefile).is_file() for lakefile in ("lakefile.lean", "lakefile.toml")):
            failures.append(f"{rel_path}: package directory does not contain a Lake manifest")
            continue

        print(f"Building {rel_path}...")
        seed_packages_dir(package_dir)
        proc = run_lake_build(package_dir)
        if proc.returncode == 0:
            print(f"  OK {rel_path}")
            continue

        failures.append(f"{rel_path}: lake build failed with exit code {proc.returncode}")
        stdout = proc.stdout.strip()
        stderr = proc.stderr.strip()
        if stdout:
            failures.append(f"{rel_path}: stdout:\n{stdout}")
        if stderr:
            failures.append(f"{rel_path}: stderr:\n{stderr}")

    if failures:
        print("split package build check failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print(f"Split package build check passed ({len(package_dirs)} package(s)).")
    return 0


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    return check_split_package_builds(resolve_packages(args.packages))


if __name__ == "__main__":
    raise SystemExit(main())
