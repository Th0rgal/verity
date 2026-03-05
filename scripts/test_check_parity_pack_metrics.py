from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent / "check_parity_pack_metrics.py"


class CheckParityPackMetricsTests(unittest.TestCase):
    def _write_report(self, by_kind: dict[str, int]) -> str:
        payload = {
            "summary": {
                "byKind": by_kind,
            }
        }
        tmp = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False)
        json.dump(payload, tmp)
        tmp.write("\n")
        tmp.close()
        return tmp.name

    def _run(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["python3", str(SCRIPT), *args],
            text=True,
            capture_output=True,
            check=False,
        )

    def test_passes_when_within_bounds(self) -> None:
        report = self._write_report(
            {
                "missing_in_solc": 0,
                "missing_in_verity": 0,
                "line_mismatch": 0,
            }
        )
        proc = self._run("--report", report)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("onlyInVerity=0", proc.stdout)
        self.assertIn("onlyInSolidity=0", proc.stdout)
        self.assertIn("hashMismatch=0", proc.stdout)

    def test_fails_when_metric_exceeds_threshold(self) -> None:
        report = self._write_report({"line_mismatch": 2})
        proc = self._run("--report", report, "--max-hash-mismatch", "1")
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("hashMismatch=2 exceeds max 1", proc.stdout)

    def test_markdown_output(self) -> None:
        report = self._write_report({"missing_in_solc": 1, "line_mismatch": 3})
        proc = self._run(
            "--report",
            report,
            "--max-only-in-verity",
            "1",
            "--max-hash-mismatch",
            "3",
            "--format",
            "markdown",
        )
        self.assertEqual(proc.returncode, 0, proc.stdout)
        self.assertIn("### Parity Pack Metrics", proc.stdout)
        self.assertIn("`onlyInVerity`", proc.stdout)


if __name__ == "__main__":
    unittest.main()
