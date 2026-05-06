#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import profile_ci_resources


class ProfileCiResourcesTests(unittest.TestCase):
    def test_summarize_reports_zeroes_for_empty_samples(self) -> None:
        self.assertEqual(profile_ci_resources.summarize([]), {"avg": 0.0, "max": 0.0})

    def test_summarize_reports_average_and_maximum(self) -> None:
        self.assertEqual(profile_ci_resources.summarize([1.0, 2.0, 6.0]), {"avg": 3.0, "max": 6.0})

    def test_parse_gnu_time_only_reads_marked_block(self) -> None:
        log_text = "\n".join(
            [
                "Maximum resident set size (kbytes): ignored",
                "PROFILE_CI_RESOURCES_TIME_BEGIN",
                "Command being timed: bash -lc true",
                "User time (seconds): 0.01",
                "Maximum resident set size (kbytes): 1234",
                "PROFILE_CI_RESOURCES_TIME_END",
                "User time (seconds): ignored",
            ]
        )
        self.assertEqual(
            profile_ci_resources.parse_gnu_time(log_text),
            {
                "Command being timed": "bash -lc true",
                "User time (seconds)": "0.01",
                "Maximum resident set size (kbytes)": "1234",
            },
        )

    def test_parse_gnu_time_reads_unmarked_time_file(self) -> None:
        log_text = "\n".join(
            [
                "Command being timed: python3 -c pass",
                "Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.23",
                "User time (seconds): 0.01",
                "Maximum resident set size (kbytes): 4321",
            ]
        )
        self.assertEqual(
            profile_ci_resources.parse_gnu_time(log_text),
            {
                "Command being timed": "python3 -c pass",
                "Elapsed (wall clock) time (h:mm:ss or m:ss)": "0:01.23",
                "User time (seconds)": "0.01",
                "Maximum resident set size (kbytes)": "4321",
            },
        )

    def test_cpu_delta_clamps_percentages(self) -> None:
        before = profile_ci_resources.CpuSnapshot(total=100, idle=80, iowait=5)
        after = profile_ci_resources.CpuSnapshot(total=200, idle=130, iowait=15)
        self.assertEqual(
            profile_ci_resources.cpu_delta(before, after),
            {"cpu_percent": 50.0, "iowait_percent": 10.0},
        )

    def test_script_runs_command_and_writes_json_and_log(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            output_dir = Path(tmpdir)
            result = subprocess.run(
                [
                    sys.executable,
                    str(SCRIPT_DIR / "profile_ci_resources.py"),
                    "--name",
                    "smoke",
                    "--output-dir",
                    str(output_dir),
                    "--interval",
                    "0.05",
                    "--",
                    sys.executable,
                    "-c",
                    "import time; print('profile-smoke'); time.sleep(0.12)",
                ],
                text=True,
                capture_output=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("profile-smoke", result.stdout)

            summary = json.loads((output_dir / "smoke.json").read_text(encoding="utf-8"))
            self.assertEqual(summary["name"], "smoke")
            self.assertEqual(summary["returncode"], 0)
            self.assertGreater(summary["elapsed_seconds"], 0.0)
            self.assertGreaterEqual(summary["sample_count"], 1)
            self.assertEqual(summary["command"][0], sys.executable)
            self.assertIn("cpu_percent", summary)
            self.assertIn("mem_used_mb", summary)
            self.assertIn("disk", summary)
            self.assertIn("gnu_time", summary)
            self.assertIn("Command being timed", summary["gnu_time"])
            self.assertTrue(Path(summary["log_path"]).exists())
            self.assertTrue(Path(summary["time_path"]).exists())
            self.assertIn("profile-smoke", Path(summary["log_path"]).read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
