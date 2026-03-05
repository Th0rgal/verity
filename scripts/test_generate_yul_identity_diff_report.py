import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import generate_yul_identity_diff_report as checker


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


class GenerateYulIdentityDiffReportTests(unittest.TestCase):
    def test_identical_inputs_report_identical(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            verity = root / "verity"
            solc = root / "solc"
            yul = """object "C" {
  code {
    function foo() {
      let x := 1
    }
  }
}
"""
            _write(verity / "C.yul", yul)
            _write(solc / "C.yul", yul)

            report = checker.build_report(verity, solc)
            self.assertEqual(report["status"], "identical")
            self.assertEqual(report["summary"]["totalMismatches"], 0)
            self.assertEqual(report["mismatches"], [])

    def test_mismatch_localizes_to_function_scope(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            verity = root / "verity"
            solc = root / "solc"
            _write(
                verity / "C.yul",
                """object "C" {
  code {
    function foo() {
      let x := 1
    }
  }
}
""",
            )
            _write(
                solc / "C.yul",
                """object "C" {
  code {
    function foo() {
      let x := 2
    }
  }
}
""",
            )

            report = checker.build_report(verity, solc)
            self.assertEqual(report["status"], "non_identical")
            self.assertGreater(report["summary"]["totalMismatches"], 0)
            first = report["mismatches"][0]
            self.assertEqual(first["file"], "C.yul")
            self.assertIn("function:foo", first["path"])

    def test_repeated_runs_are_stable(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            verity = root / "verity"
            solc = root / "solc"
            out1 = root / "r1.json"
            out2 = root / "r2.json"

            _write(
                verity / "C.yul",
                """object "C" {
  code {
    function foo() {
      let x := 1
    }
  }
}
""",
            )
            _write(
                solc / "C.yul",
                """object "C" {
  code {
    function foo() {
      let x := 2
    }
  }
}
""",
            )

            rc1 = checker.main(["--verity-dir", str(verity), "--solc-dir", str(solc), "--output", str(out1)])
            rc2 = checker.main(["--verity-dir", str(verity), "--solc-dir", str(solc), "--output", str(out2)])
            self.assertEqual(rc1, 0)
            self.assertEqual(rc2, 0)

            j1 = json.loads(out1.read_text(encoding="utf-8"))
            j2 = json.loads(out2.read_text(encoding="utf-8"))
            self.assertEqual(j1, j2)


if __name__ == "__main__":
    unittest.main()
