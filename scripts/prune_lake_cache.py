#!/usr/bin/env python3
"""Prune stale Lake package state without mutating the committed manifest."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path


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


def main() -> int:
    if not PACKAGES_DIR.exists():
        print("prune_lake_cache: no .lake/packages directory to prune")
        return 0

    expected = expected_git_revs()
    for package_dir in PACKAGES_DIR.iterdir():
        if not package_dir.is_dir():
            continue
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

    root_build = LAKE_DIR / "build"
    if root_build.exists():
        remove_path(root_build, "clearing root build outputs after partial cache restore")

    for package_dir in PACKAGES_DIR.iterdir():
        if not package_dir.is_dir():
            continue
        package_build = package_dir / ".lake" / "build"
        if package_build.exists():
            remove_path(package_build, "clearing dependency build outputs after partial cache restore")

    return 0


if __name__ == "__main__":
    sys.exit(main())
