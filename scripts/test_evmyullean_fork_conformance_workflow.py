import json
import re
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github" / "workflows" / "evmyullean-fork-conformance.yml"
TRUST_ASSUMPTIONS = ROOT / "TRUST_ASSUMPTIONS.md"
AXIOMS = ROOT / "AXIOMS.md"
MAKEFILE = ROOT / "Makefile"
ADAPTER_REPORT = ROOT / "artifacts" / "evmyullean_adapter_report.json"
ROADMAP = ROOT / "docs" / "ROADMAP.md"


class EvmYulLeanForkConformanceWorkflowTests(unittest.TestCase):
    def test_concrete_bridge_test_count_matches_adapter_report(self) -> None:
        report = json.loads(ADAPTER_REPORT.read_text(encoding="utf-8"))
        count = report["concrete_test_count"]
        test_count_re = re.compile(
            r"\b(\d+)\s+(?:concrete\s+)?(?:`native_decide`\s+|native_decide\s+)?"
            r"bridge(?:-equivalence)?\s+tests\b",
        )

        for path in [MAKEFILE, WORKFLOW, TRUST_ASSUMPTIONS, ROADMAP]:
            text = path.read_text(encoding="utf-8")
            normalized_text = re.sub(r"(?m)^\s*#\s?", "", text)
            normalized_text = re.sub(r"\s+", " ", normalized_text)
            documented_counts = {int(match) for match in test_count_re.findall(normalized_text)}
            self.assertIn(
                count,
                documented_counts,
                f"{path.relative_to(ROOT)} should document the generated concrete bridge-test count",
            )
            self.assertEqual(
                {count},
                documented_counts,
                f"{path.relative_to(ROOT)} should not contain stale concrete bridge-test counts",
            )

    def test_post_burn_in_failures_open_or_update_issue(self) -> None:
        text = WORKFLOW.read_text(encoding="utf-8")

        self.assertIn("BURN_IN_END_UTC: '2026-05-04T00:00:00Z'", text)
        for path in [
            "scripts/test_evmyullean_fork_conformance_workflow.py",
            "artifacts/evmyullean_adapter_report.json",
            "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean",
            "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeTest.lean",
            "Compiler/Proofs/YulGeneration/ReferenceOracle/Builtins.lean",
        ]:
            self.assertEqual(
                text.count(path),
                2,
                f"{path} should trigger both push and pull_request probes",
            )

        top_permissions = re.search(
            r"(?m)^permissions:\n(?P<body>(?:  .+\n)+)\n(?:env:|concurrency:|jobs:)",
            text,
        )
        self.assertIsNotNone(top_permissions)
        self.assertIn("  contents: read", top_permissions.group("body"))
        self.assertNotIn("issues: write", top_permissions.group("body"))

        issue_job = re.search(
            r"(?m)^  open-drift-issue:\n(?P<body>.*?)(?=\n  [A-Za-z0-9_-]+:|\Z)",
            text,
            re.S,
        )
        self.assertIsNotNone(issue_job)
        issue_job_body = issue_job.group("body")
        self.assertIn("needs: probe", issue_job_body)
        self.assertIn("needs.probe.result == 'failure'", issue_job_body)
        self.assertIn("github.event_name == 'schedule'", issue_job_body)
        self.assertIn("github.event_name == 'workflow_dispatch'", issue_job_body)
        self.assertNotIn("github.event_name == 'pull_request'", issue_job_body)
        self.assertNotIn("github.event_name == 'push'", issue_job_body)
        self.assertIn("issues: write", issue_job_body)
        self.assertIn("uses: actions/github-script@v7", text)
        self.assertIn("const title = \"EVMYulLean fork conformance probe failed\";", text)
        self.assertIn("github.rest.issues.createComment", text)
        self.assertIn("github.rest.issues.create({", text)
        self.assertIn("make test-evmyullean-fork", text)

        issue_step = re.search(
            r"- name: Open or update drift issue\n(?P<body>.*?)(?=\n      - name:|\Z)",
            text,
            re.S,
        )
        self.assertIsNotNone(issue_step)
        body = issue_step.group("body")
        self.assertIn("Date.now() < burnInEnd", body)

        fail_step = re.search(
            r"- name: Fail after burn-in conformance failure\n(?P<body>.*?)(?=\n      - name:|\Z)",
            text,
            re.S,
        )
        self.assertIsNotNone(fail_step)
        self.assertIn('if [ "$now_epoch" -ge "$burn_in_epoch" ]; then', fail_step.group("body"))
        self.assertIn("exit 1", fail_step.group("body"))

    def test_trust_assumptions_describe_post_burn_in_issue_path(self) -> None:
        text = TRUST_ASSUMPTIONS.read_text(encoding="utf-8")
        self.assertIn("weekly scheduled GitHub Actions workflow", text)
        self.assertIn("two-week `continue-on-error` burn-in ending 2026-05-04", text)
        self.assertIn("automatically opened or updated GitHub issue", text)

    def test_axioms_document_non_axiom_evmyullean_controls(self) -> None:
        text = AXIOMS.read_text(encoding="utf-8")
        self.assertIn("## EVMYulLean Runtime Semantics (Non-Axiom)", text)
        self.assertIn("make test-evmyullean-fork", text)
        self.assertIn(".github/workflows/evmyullean-fork-conformance.yml", text)
        self.assertIn("open or update a GitHub issue", text)


if __name__ == "__main__":
    unittest.main()
