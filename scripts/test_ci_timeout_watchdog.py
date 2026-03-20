#!/usr/bin/env python3
from __future__ import annotations

import tempfile
import textwrap
import unittest
from pathlib import Path
import sys

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import ci_timeout_watchdog as watchdog


class TimeoutWatchdogTests(unittest.TestCase):
    def test_load_timeouts_extracts_top_level_job_timeouts(self) -> None:
        workflow = textwrap.dedent(
            """
            name: Verify proofs
            jobs:
              checks:
                runs-on: ubuntu-latest
                timeout-minutes: 5
                steps: []
              macro-fuzz:
                runs-on: ubuntu-latest
                timeout-minutes: 90
                strategy:
                  fail-fast: false
                steps: []
            """
        ).lstrip()
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "verify.yml"
            path.write_text(workflow, encoding="utf-8")
            self.assertEqual(
                watchdog.load_timeouts(path),
                {"checks": 5, "macro-fuzz": 90},
            )

    def test_collect_timeout_risk_samples_matches_matrix_job_names(self) -> None:
        runs = [{"id": 1, "display_title": "Verify proofs"}]
        run_jobs = {
            1: [
                {
                    "name": "macro-fuzz (0)",
                    "started_at": "2026-03-19T23:00:00Z",
                    "completed_at": "2026-03-20T00:18:00Z",
                    "conclusion": "success",
                },
                {
                    "name": "build-compiler",
                    "started_at": "2026-03-19T23:00:00Z",
                    "completed_at": "2026-03-20T00:50:00Z",
                    "conclusion": "success",
                },
            ]
        }
        samples = watchdog.collect_timeout_risk_samples(
            runs,
            run_jobs,
            {"macro-fuzz": 90, "build-compiler": 120},
        )
        self.assertEqual(len(samples["macro-fuzz"]), 1)
        self.assertAlmostEqual(samples["macro-fuzz"][0].ratio, 78 / 90, places=3)
        self.assertEqual(len(samples["build-compiler"]), 1)

    def test_summarize_risk_warns_only_after_minimum_samples(self) -> None:
        samples = {
            "macro-fuzz": [
                watchdog.Sample(1, "run 1", 78.0, 90, 78.0 / 90.0, "success"),
                watchdog.Sample(2, "run 2", 74.0, 90, 74.0 / 90.0, "cancelled"),
                watchdog.Sample(3, "run 3", 10.0, 90, 10.0 / 90.0, "success"),
            ]
        }
        warnings = watchdog.summarize_risk(samples, threshold=0.8, min_risk_samples=2)
        self.assertEqual(len(warnings), 1)
        self.assertIn("macro-fuzz", warnings[0])


if __name__ == "__main__":
    unittest.main()
