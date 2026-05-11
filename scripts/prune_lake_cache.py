#!/usr/bin/env python3
"""Prune stale Lake package state without mutating the committed manifest."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path
import argparse


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "lake-manifest.json"
LAKE_DIR = ROOT / ".lake"
PACKAGES_DIR = LAKE_DIR / "packages"


def expected_git_revs() -> dict[str, str]:
    manifest = json.loads(MANIFEST.read_text())
    packages: dict[str, str] = {}
    for package in manifest.get("packages", []):
        if package.get("type") != "git":
            continue
        name = package.get("name")
        rev = package.get("rev")
        if isinstance(name, str) and isinstance(rev, str):
            packages[name] = rev
    return packages


def git_head(path: Path) -> str | None:
    try:
        result = subprocess.run(
            ["git", "-C", str(path), "rev-parse", "HEAD"],
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return None
    return result.stdout.strip()


def remove_path(path: Path, reason: str) -> None:
    print(f"prune_lake_cache: removing {path.relative_to(ROOT)} ({reason})")
    shutil.rmtree(path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--packages-only",
        action="store_true",
        help="prune stale package checkouts without clearing .lake/build outputs",
    )
    args = parser.parse_args([] if argv is None else argv)

    package_dirs: list[Path] = []
    if PACKAGES_DIR.exists():
        package_dirs = [path for path in PACKAGES_DIR.iterdir() if path.is_dir()]
    else:
        print("prune_lake_cache: no .lake/packages directory to prune")

    if package_dirs:
        expected = expected_git_revs()
        for package_dir in package_dirs:
            expected_rev = expected.get(package_dir.name)
            if expected_rev is None:
                remove_path(package_dir, "package not present in lake-manifest.json")
                continue

            actual_rev = git_head(package_dir)
            if actual_rev is None:
                remove_path(package_dir, "package checkout is missing git metadata")
                continue
            if actual_rev != expected_rev:
                remove_path(package_dir, f"expected {expected_rev[:12]}, found {actual_rev[:12]}")

    if args.packages_only:
        return 0

    root_build = LAKE_DIR / "build"
    if root_build.exists():
        remove_path(root_build, "clearing root build outputs after partial cache restore")

    if PACKAGES_DIR.exists():
        for package_dir in [path for path in PACKAGES_DIR.iterdir() if path.is_dir()]:
            package_build = package_dir / ".lake" / "build"
            if package_build.exists():
                remove_path(package_build, "clearing dependency build outputs after partial cache restore")

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
