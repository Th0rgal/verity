#!/usr/bin/env python3
from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import prune_lake_cache


class PruneLakeCacheTests(unittest.TestCase):
    def test_clears_root_build_without_packages_dir(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            lake_dir = root / ".lake"
            (lake_dir / "build").mkdir(parents=True)
            manifest = root / "lake-manifest.json"
            manifest.write_text(json.dumps({"packages": []}))

            with (
                mock.patch.object(prune_lake_cache, "ROOT", root),
                mock.patch.object(prune_lake_cache, "LAKE_DIR", lake_dir),
                mock.patch.object(prune_lake_cache, "PACKAGES_DIR", lake_dir / "packages"),
                mock.patch.object(prune_lake_cache, "MANIFEST", manifest),
            ):
                rc = prune_lake_cache.main()

            self.assertEqual(rc, 0)
            self.assertFalse((lake_dir / "build").exists())

    def test_prunes_mismatched_package_and_dependency_build_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            lake_dir = root / ".lake"
            packages_dir = lake_dir / "packages"
            pkg_dir = packages_dir / "demo"
            dep_build = pkg_dir / ".lake" / "build"
            dep_build.mkdir(parents=True)
            root_build = lake_dir / "build"
            root_build.mkdir(parents=True)
            manifest = root / "lake-manifest.json"
            manifest.write_text(
                json.dumps(
                    {
                        "packages": [
                            {"type": "git", "name": "demo", "rev": "expected-rev"},
                        ]
                    }
                )
            )

            with (
                mock.patch.object(prune_lake_cache, "ROOT", root),
                mock.patch.object(prune_lake_cache, "LAKE_DIR", lake_dir),
                mock.patch.object(prune_lake_cache, "PACKAGES_DIR", packages_dir),
                mock.patch.object(prune_lake_cache, "MANIFEST", manifest),
                mock.patch.object(prune_lake_cache, "git_head", return_value="actual-rev"),
            ):
                rc = prune_lake_cache.main()

            self.assertEqual(rc, 0)
            self.assertFalse(pkg_dir.exists())
            self.assertFalse(root_build.exists())

    def test_packages_only_prunes_bad_packages_without_clearing_build(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            lake_dir = root / ".lake"
            packages_dir = lake_dir / "packages"
            pkg_dir = packages_dir / "demo"
            pkg_dir.mkdir(parents=True)
            root_build = lake_dir / "build"
            root_build.mkdir(parents=True)
            manifest = root / "lake-manifest.json"
            manifest.write_text(
                json.dumps(
                    {
                        "packages": [
                            {"type": "git", "name": "demo", "rev": "expected-rev"},
                        ]
                    }
                )
            )

            with (
                mock.patch.object(prune_lake_cache, "ROOT", root),
                mock.patch.object(prune_lake_cache, "LAKE_DIR", lake_dir),
                mock.patch.object(prune_lake_cache, "PACKAGES_DIR", packages_dir),
                mock.patch.object(prune_lake_cache, "MANIFEST", manifest),
                mock.patch.object(prune_lake_cache, "git_head", return_value=None),
            ):
                rc = prune_lake_cache.main(["--packages-only"])

            self.assertEqual(rc, 0)
            self.assertFalse(pkg_dir.exists())
            self.assertTrue(root_build.exists())


if __name__ == "__main__":
    unittest.main()
