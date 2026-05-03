#!/usr/bin/env python3
from __future__ import annotations

import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RUNNER_SCRIPT = ROOT / "scripts" / "install_self_hosted_runner.sh"
MAINTENANCE_SCRIPT = ROOT / "scripts" / "ci_host_maintenance.sh"
VERIFY_WORKFLOW = ROOT / ".github" / "workflows" / "verify.yml"


class CiInfraMaintenanceTests(unittest.TestCase):
    def test_runner_host_profiles_assign_healthier_build_host(self) -> None:
        text = RUNNER_SCRIPT.read_text(encoding="utf-8")
        self.assertIn("88.99.4.254|healthy-build", text)
        self.assertIn('RUNNER_PROFILE="${RUNNER_PROFILE_INPUT:-build}"', text)
        self.assertIn('RUNNER_COUNT="${RUNNER_COUNT:-1}"', text)
        self.assertIn("ci-host-88-99-4-254", text)
        self.assertIn("build-heavy", text)

    def test_runner_host_profiles_keep_overloaded_host_fastlane_only(self) -> None:
        text = RUNNER_SCRIPT.read_text(encoding="utf-8")
        self.assertIn("95.216.244.60|mixed-8core", text)
        self.assertIn('RUNNER_PROFILE="${RUNNER_PROFILE_INPUT:-fastlane}"', text)
        self.assertIn("ci-host-95-216-244-60", text)
        self.assertIn("decommission_surplus_runners", text)
        self.assertIn('if [ "$index" -gt "$RUNNER_COUNT" ]; then', text)

    def test_weekly_host_maintenance_prunes_ci_disk_journald_and_docker(self) -> None:
        text = MAINTENANCE_SCRIPT.read_text(encoding="utf-8")
        self.assertIn('CACHE_ROOT="${CACHE_ROOT:-/srv/verity-ci-cache}"', text)
        self.assertIn('prune_tree "$CACHE_ROOT/lake-build"', text)
        self.assertIn('prune_tree "$CACHE_ROOT/compiler-ccache"', text)
        self.assertIn('journalctl --vacuum-time="$JOURNAL_VACUUM_TIME"', text)
        self.assertIn('journalctl --vacuum-size="$JOURNAL_VACUUM_SIZE"', text)
        self.assertIn('docker image prune -af --filter "$DOCKER_PRUNE_FILTER"', text)
        self.assertIn("OnCalendar=Sun *-*-* 04:30:00", text)
        self.assertIn("verity-ci-host-maintenance.timer", text)

    def test_parallel_build_jobs_use_four_lean_threads(self) -> None:
        text = VERIFY_WORKFLOW.read_text(encoding="utf-8")
        for job in (
            "prepare-macro-fuzz",
            "macro-fuzz",
            "build-compiler-binaries",
            "compiler-regressions",
        ):
            match = re.search(rf"^  {job}:\n(?P<body>.*?)(?=^  [a-zA-Z0-9_-]+:|\Z)", text, re.S | re.M)
            self.assertIsNotNone(match, job)
            body = match.group("body")
            self.assertIn("LEAN_NUM_THREADS: 4", body, job)
            self.assertNotIn("LEAN_NUM_THREADS: 8", body, job)


if __name__ == "__main__":
    unittest.main()
