#!/usr/bin/env python3
from __future__ import annotations

import io
import json
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_verify_sync as check

FAILURE_HINTS_SCRIPT = textwrap.dedent(
    """
    const marker = "<!-- ci-failure-hints -->";
    const needs = JSON.parse(process.env.NEEDS_JSON || "{}");
    const failed = Object.entries(needs)
      .filter(([, info]) => info && info.result === "failure")
      .map(([name]) => name);
    if (failed.length === 0) {
      core.info("No failed jobs; no hint comment needed.");
      return;
    }

    const lines = [];
    lines.push(marker);
    lines.push("### CI Failure Hints");
    lines.push("");
    lines.push("Failed jobs: " + failed.map((n) => "`" + n + "`").join(", "));
    lines.push("");
    lines.push("Copy-paste local triage:");
    lines.push("```bash");
    lines.push("make check");
    lines.push("lake build");
    lines.push("FOUNDRY_PROFILE=difftest forge test -vv");
    lines.push("```");
    const body = lines.join("\\n");

    const owner = context.repo.owner;
    const repo = context.repo.repo;
    const issue_number = context.issue.number;
    const comments = await github.paginate(github.rest.issues.listComments, {
      owner,
      repo,
      issue_number,
      per_page: 100
    });
    const existing = comments.find((c) =>
      c.user && c.user.type === "Bot" && typeof c.body === "string" && c.body.includes(marker)
    );
    if (existing) {
      await github.rest.issues.updateComment({
        owner,
        repo,
        comment_id: existing.id,
        body
      });
    } else {
      await github.rest.issues.createComment({
        owner,
        repo,
        issue_number,
        body
      });
    }
    """
).strip()


class VerifySyncTests(unittest.TestCase):
    def _run_jobs_check(self, workflow_text: str, expected_jobs: list[str]) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as td:
            root = Path(td)
            verify = root / "verify.yml"
            spec = root / "verify_sync_spec.json"
            verify.write_text(workflow_text, encoding="utf-8")
            spec.write_text(json.dumps({"expected_jobs": expected_jobs}), encoding="utf-8")

            old_verify = check.VERIFY_YML
            old_spec = check.SPEC_PATH
            check.VERIFY_YML = verify
            check.SPEC_PATH = spec
            old_argv = sys.argv
            sys.argv = ["check_verify_sync.py", "--only", "jobs"]
            try:
                stderr = io.StringIO()
                stdout = io.StringIO()
                with redirect_stderr(stderr), redirect_stdout(stdout):
                    rc = check.main()
                return rc, stdout.getvalue(), stderr.getvalue()
            finally:
                check.VERIFY_YML = old_verify
                check.SPEC_PATH = old_spec
                sys.argv = old_argv

    def _run_paths_check(
        self,
        workflow_text: str,
        *,
        check_only_paths: list[str],
        compiler_paths: list[str],
        expected_trigger_keys: list[str] | None = None,
        expected_push_branches: list[str] | None = None,
        require_workflow_dispatch: bool = False,
    ) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as td:
            root = Path(td)
            verify = root / "verify.yml"
            spec = root / "verify_sync_spec.json"
            verify.write_text(workflow_text, encoding="utf-8")
            spec.write_text(
                json.dumps(
                    {
                        "check_only_paths": check_only_paths,
                        "compiler_paths": compiler_paths,
                        "expected_trigger_keys": expected_trigger_keys or [],
                        "expected_push_branches": expected_push_branches or [],
                        "require_workflow_dispatch": require_workflow_dispatch,
                    }
                ),
                encoding="utf-8",
            )

            old_verify = check.VERIFY_YML
            old_spec = check.SPEC_PATH
            check.VERIFY_YML = verify
            check.SPEC_PATH = spec
            old_argv = sys.argv
            sys.argv = ["check_verify_sync.py", "--only", "paths"]
            try:
                stderr = io.StringIO()
                stdout = io.StringIO()
                with redirect_stderr(stderr), redirect_stdout(stdout):
                    rc = check.main()
                return rc, stdout.getvalue(), stderr.getvalue()
            finally:
                check.VERIFY_YML = old_verify
                check.SPEC_PATH = old_spec
                sys.argv = old_argv

    def _run_job_contracts_check(
        self,
        workflow_text: str,
        *,
        expected_job_needs: dict[str, list[str]],
        expected_job_if_conditions: dict[str, str | None],
        expected_job_runs_on: dict[str, str] | None = None,
        expected_job_timeouts: dict[str, int] | None = None,
        expected_job_strategy_fail_fast: dict[str, bool] | None = None,
        expected_job_outputs: dict[str, dict[str, str]] | None = None,
        expected_job_permissions: dict[str, dict[str, str]] | None = None,
        expected_workflow_permissions: dict[str, str] | None = None,
        expected_workflow_concurrency: dict[str, str] | None = None,
        expected_workflow_env: dict[str, str] | None = None,
    ) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as td:
            root = Path(td)
            verify = root / "verify.yml"
            spec = root / "verify_sync_spec.json"
            verify.write_text(workflow_text, encoding="utf-8")
            spec.write_text(
                json.dumps(
                    {
                        "expected_job_needs": expected_job_needs,
                        "expected_job_if_conditions": expected_job_if_conditions,
                        "expected_job_runs_on": expected_job_runs_on or {},
                        "expected_job_timeouts": expected_job_timeouts or {},
                        "expected_job_strategy_fail_fast": expected_job_strategy_fail_fast or {},
                        "expected_job_outputs": expected_job_outputs or {},
                        "expected_job_permissions": expected_job_permissions or {},
                        "expected_workflow_permissions": expected_workflow_permissions or {},
                        "expected_workflow_concurrency": expected_workflow_concurrency or {},
                        "expected_workflow_env": expected_workflow_env or {},
                    }
                ),
                encoding="utf-8",
            )

            old_verify = check.VERIFY_YML
            old_spec = check.SPEC_PATH
            check.VERIFY_YML = verify
            check.SPEC_PATH = spec
            old_argv = sys.argv
            sys.argv = ["check_verify_sync.py", "--only", "job-contracts"]
            try:
                stderr = io.StringIO()
                stdout = io.StringIO()
                with redirect_stderr(stderr), redirect_stdout(stdout):
                    rc = check.main()
                return rc, stdout.getvalue(), stderr.getvalue()
            finally:
                check.VERIFY_YML = old_verify
                check.SPEC_PATH = old_spec
                sys.argv = old_argv

    def _run_step_contracts_check(
        self,
        workflow_text: str,
        *,
        expected_step_contracts: dict[str, list[dict]],
    ) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as td:
            root = Path(td)
            verify = root / "verify.yml"
            spec = root / "verify_sync_spec.json"
            verify.write_text(workflow_text, encoding="utf-8")
            spec.write_text(
                json.dumps({"expected_step_contracts": expected_step_contracts}),
                encoding="utf-8",
            )

            old_verify = check.VERIFY_YML
            old_spec = check.SPEC_PATH
            check.VERIFY_YML = verify
            check.SPEC_PATH = spec
            old_argv = sys.argv
            sys.argv = ["check_verify_sync.py", "--only", "step-contracts"]
            try:
                stderr = io.StringIO()
                stdout = io.StringIO()
                with redirect_stderr(stderr), redirect_stdout(stdout):
                    rc = check.main()
                return rc, stdout.getvalue(), stderr.getvalue()
            finally:
                check.VERIFY_YML = old_verify
                check.SPEC_PATH = old_spec
                sys.argv = old_argv

    def _run_makefile_check(
        self,
        makefile_text: str,
        *,
        expected_checks_commands: list[str],
        required_makefile_check_commands: list[str] | None = None,
        expected_checks_other_commands: list[str] | None = None,
    ) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as td:
            root = Path(td)
            verify = root / "verify.yml"
            spec = root / "verify_sync_spec.json"
            makefile = root / "Makefile"
            verify.write_text("name: verify\njobs:\n  checks:\n    runs-on: ubuntu-latest\n    steps: []\n", encoding="utf-8")
            makefile.write_text(textwrap.dedent(makefile_text).lstrip(), encoding="utf-8")
            spec.write_text(
                json.dumps(
                    {
                        "expected_checks_commands": expected_checks_commands,
                        "required_makefile_check_commands": required_makefile_check_commands or [],
                        "expected_checks_other_commands": expected_checks_other_commands or [],
                    }
                ),
                encoding="utf-8",
            )

            old_verify = check.VERIFY_YML
            old_spec = check.SPEC_PATH
            old_makefile = check.MAKEFILE
            check.VERIFY_YML = verify
            check.SPEC_PATH = spec
            check.MAKEFILE = makefile
            old_argv = sys.argv
            sys.argv = ["check_verify_sync.py", "--only", "makefile"]
            try:
                stderr = io.StringIO()
                stdout = io.StringIO()
                with redirect_stderr(stderr), redirect_stdout(stdout):
                    rc = check.main()
                return rc, stdout.getvalue(), stderr.getvalue()
            finally:
                check.VERIFY_YML = old_verify
                check.SPEC_PATH = old_spec
                check.MAKEFILE = old_makefile
                sys.argv = old_argv

    def _run_artifacts_check(
        self,
        workflow_text: str,
        *,
        expected_uploaded_artifacts: dict[str, list[str]],
        expected_downloaded_artifacts: dict[str, list[str]],
        expected_uploaded_artifact_paths: dict[str, list[str | None]] | None = None,
        expected_downloaded_artifact_paths: dict[str, list[str | None]] | None = None,
    ) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as td:
            root = Path(td)
            verify = root / "verify.yml"
            spec = root / "verify_sync_spec.json"
            verify.write_text(textwrap.dedent(workflow_text).lstrip(), encoding="utf-8")
            spec.write_text(
                json.dumps(
                    {
                        "expected_uploaded_artifacts": expected_uploaded_artifacts,
                        "expected_downloaded_artifacts": expected_downloaded_artifacts,
                        "expected_uploaded_artifact_paths": expected_uploaded_artifact_paths or {},
                        "expected_downloaded_artifact_paths": expected_downloaded_artifact_paths or {},
                    }
                ),
                encoding="utf-8",
            )

            old_verify = check.VERIFY_YML
            old_spec = check.SPEC_PATH
            check.VERIFY_YML = verify
            check.SPEC_PATH = spec
            old_argv = sys.argv
            sys.argv = ["check_verify_sync.py", "--only", "artifacts"]
            try:
                stderr = io.StringIO()
                stdout = io.StringIO()
                with redirect_stderr(stderr), redirect_stdout(stdout):
                    rc = check.main()
                return rc, stdout.getvalue(), stderr.getvalue()
            finally:
                check.VERIFY_YML = old_verify
                check.SPEC_PATH = old_spec
                sys.argv = old_argv

    def _run_python_commands_check(
        self,
        workflow_text: str,
        *,
        expected_checks_commands: list[str],
        expected_build_commands: list[str],
        expected_build_audit_commands: list[str] | None = None,
        expected_build_compiler_commands: list[str],
        expected_compiler_audit_commands: list[str] | None = None,
        required_build_run_commands: list[str] | None = None,
        required_build_audit_run_commands: list[str] | None = None,
        required_build_compiler_run_commands: list[str] | None = None,
        required_compiler_audit_run_commands: list[str] | None = None,
    ) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as td:
            root = Path(td)
            verify = root / "verify.yml"
            spec = root / "verify_sync_spec.json"
            verify.write_text(textwrap.dedent(workflow_text).lstrip(), encoding="utf-8")
            spec.write_text(
                json.dumps(
                    {
                        "expected_checks_commands": expected_checks_commands,
                        "expected_checks_other_commands": [],
                        "expected_build_commands": expected_build_commands,
                        "expected_build_audit_commands": expected_build_audit_commands or [],
                        "expected_build_compiler_commands": expected_build_compiler_commands,
                        "expected_compiler_audit_commands": expected_compiler_audit_commands or [],
                        "required_build_run_commands": required_build_run_commands or [],
                        "required_build_audit_run_commands": required_build_audit_run_commands or [],
                        "required_build_compiler_run_commands": required_build_compiler_run_commands or [],
                        "required_compiler_audit_run_commands": required_compiler_audit_run_commands or [],
                    }
                ),
                encoding="utf-8",
            )

            old_verify = check.VERIFY_YML
            old_spec = check.SPEC_PATH
            check.VERIFY_YML = verify
            check.SPEC_PATH = spec
            old_argv = sys.argv
            sys.argv = ["check_verify_sync.py", "--only", "python-commands"]
            try:
                stderr = io.StringIO()
                stdout = io.StringIO()
                with redirect_stderr(stderr), redirect_stdout(stdout):
                    rc = check.main()
                return rc, stdout.getvalue(), stderr.getvalue()
            finally:
                check.VERIFY_YML = old_verify
                check.SPEC_PATH = old_spec
                sys.argv = old_argv

    def test_jobs_check_passes_when_order_matches(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps: []
              checks:
                runs-on: ubuntu-latest
                steps: []
            """
        )
        rc, out, err = self._run_jobs_check(workflow, ["changes", "checks"])
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] jobs", out)

    def test_jobs_check_fails_when_order_drifts(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              checks:
                runs-on: ubuntu-latest
                steps: []
              changes:
                runs-on: ubuntu-latest
                steps: []
            """
        )
        rc, _, err = self._run_jobs_check(workflow, ["changes", "checks"])
        self.assertEqual(rc, 1)
        self.assertIn("[FAIL] jobs", err)

    def test_paths_check_fails_when_push_branch_and_workflow_dispatch_drift(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                branches:
                  - release
                paths:
                  - 'src/**'
              pull_request:
                paths:
                  - 'src/**'
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: actions/checkout@v4
                  - id: filter
                    uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - 'src/**'
                        compiler:
                          - 'src/**'
            """
        )
        rc, _, err = self._run_paths_check(
            workflow,
            check_only_paths=[],
            compiler_paths=["src/**"],
            expected_trigger_keys=["push", "pull_request", "workflow_dispatch"],
            expected_push_branches=["main"],
            require_workflow_dispatch=True,
        )
        self.assertEqual(rc, 1)
        self.assertIn("[FAIL] paths", err)
        self.assertIn("workflow triggers does not match spec workflow triggers.", err)
        self.assertIn("on.push.branches does not match spec push branches.", err)
        self.assertIn("workflow_dispatch trigger is missing from verify.yml", err)

    def test_paths_check_fails_when_extra_trigger_is_added(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                branches: [main]
                paths:
                  - 'src/**'
              pull_request:
                paths:
                  - 'src/**'
              workflow_dispatch:
              schedule:
                - cron: '0 0 * * *'
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: actions/checkout@v4
                  - id: filter
                    uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - 'src/**'
                        compiler:
                          - 'src/**'
            """
        )
        rc, _, err = self._run_paths_check(
            workflow,
            check_only_paths=[],
            compiler_paths=["src/**"],
            expected_trigger_keys=["push", "pull_request", "workflow_dispatch"],
            expected_push_branches=["main"],
            require_workflow_dispatch=True,
        )
        self.assertEqual(rc, 1)
        self.assertIn("workflow triggers does not match spec workflow triggers.", err)
        self.assertIn("idx 3: workflow triggers='schedule', spec workflow triggers='<missing>'", err)

    def test_paths_check_passes_when_trigger_contracts_match_spec(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                branches: [main]
                paths:
                  - 'src/**'
              pull_request:
                paths:
                  - 'src/**'
              workflow_dispatch:
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: actions/checkout@v4
                  - id: filter
                    uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - 'src/**'
                        compiler:
                          - 'src/**'
            """
        )
        rc, out, err = self._run_paths_check(
            workflow,
            check_only_paths=[],
            compiler_paths=["src/**"],
            expected_trigger_keys=["push", "pull_request", "workflow_dispatch"],
            expected_push_branches=["main"],
            require_workflow_dispatch=True,
        )
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] paths", out)

    def test_job_contracts_check_fails_when_needs_and_if_drift(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps: []
              build:
                runs-on: ubuntu-latest
                needs: checks
                if: github.event_name == 'push'
                steps: []
            """
        )
        rc, _, err = self._run_job_contracts_check(
            workflow,
            expected_job_needs={"changes": [], "build": ["changes"]},
            expected_job_if_conditions={
                "changes": None,
                "build": "needs.changes.outputs.code == 'true'",
            },
            expected_job_runs_on={"changes": "ubuntu-latest", "build": "ubuntu-latest"},
            expected_job_timeouts={"changes": 5, "build": 45},
        )
        self.assertEqual(rc, 1)
        self.assertIn("[FAIL] job-contracts", err)
        self.assertIn("build needs does not match spec build needs.", err)
        self.assertIn(
            "build if does not match spec: workflow=\"github.event_name == 'push'\", spec=\"needs.changes.outputs.code == 'true'\"",
            err,
        )

    def test_job_contracts_check_passes_when_needs_and_if_match_spec(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps: []
              build:
                runs-on: ubuntu-latest
                needs: changes
                if: needs.changes.outputs.code == 'true'
                steps: []
              foundry:
                runs-on: ubuntu-latest
                needs: [changes, build]
                if: always() && github.event_name == 'pull_request'
                steps: []
            """
        )
        rc, out, err = self._run_job_contracts_check(
            workflow,
            expected_job_needs={
                "changes": [],
                "build": ["changes"],
                "foundry": ["changes", "build"],
            },
            expected_job_if_conditions={
                "changes": None,
                "build": "needs.changes.outputs.code == 'true'",
                "foundry": "always() && github.event_name == 'pull_request'",
            },
            expected_job_runs_on={
                "changes": "ubuntu-latest",
                "build": "ubuntu-latest",
                "foundry": "ubuntu-latest",
            },
        )
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] job-contracts", out)

    def test_job_contracts_check_passes_when_needs_uses_multiline_yaml_list(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps: []
              build:
                runs-on: ubuntu-latest
                needs:
                  - changes
                if: needs.changes.outputs.code == 'true'
                steps: []
              foundry:
                runs-on: ubuntu-latest
                needs:
                  - changes
                  - build
                if: always() && github.event_name == 'pull_request'
                steps: []
            """
        )
        rc, out, err = self._run_job_contracts_check(
            workflow,
            expected_job_needs={
                "changes": [],
                "build": ["changes"],
                "foundry": ["changes", "build"],
            },
            expected_job_if_conditions={
                "changes": None,
                "build": "needs.changes.outputs.code == 'true'",
                "foundry": "always() && github.event_name == 'pull_request'",
            },
            expected_job_runs_on={
                "changes": "ubuntu-latest",
                "build": "ubuntu-latest",
                "foundry": "ubuntu-latest",
            },
        )
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] job-contracts", out)

    def test_job_contracts_check_fails_when_runner_timeout_outputs_and_permissions_drift(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            permissions:
              contents: write
            concurrency:
              group: ${{ github.ref }}
              cancel-in-progress: false
            env:
              SOLC_VERSION: "0.8.32"
            jobs:
              changes:
                runs-on: ubuntu-22.04
                timeout-minutes: 7
                outputs:
                  code: ${{ steps.filter.outputs.code }}
                  compiler: ${{ steps.filter.outputs.code }}
                steps: []
              failure-hints:
                runs-on: ubuntu-latest
                permissions:
                  contents: read
                steps: []
            """
        )
        rc, _, err = self._run_job_contracts_check(
            workflow,
            expected_job_needs={"changes": [], "failure-hints": []},
            expected_job_if_conditions={"changes": None, "failure-hints": None},
            expected_job_runs_on={
                "changes": "ubuntu-latest",
                "failure-hints": "ubuntu-latest",
            },
            expected_job_timeouts={"changes": 5},
            expected_job_outputs={
                "changes": {
                    "code": "${{ steps.filter.outputs.code }}",
                    "compiler": "${{ steps.filter.outputs.compiler }}",
                }
            },
            expected_job_permissions={
                "failure-hints": {
                    "contents": "read",
                    "pull-requests": "write",
                }
            },
            expected_workflow_permissions={"contents": "read"},
            expected_workflow_concurrency={
                "group": "${{ github.workflow }}-${{ github.ref }}",
                "cancel-in-progress": "true",
            },
            expected_workflow_env={"SOLC_VERSION": "0.8.33"},
        )
        self.assertEqual(rc, 1)
        self.assertIn("workflow permissions does not match spec workflow permissions.", err)
        self.assertIn("workflow concurrency does not match spec workflow concurrency.", err)
        self.assertIn("workflow env does not match spec workflow env.", err)
        self.assertIn(
            "changes runs-on does not match spec: workflow='ubuntu-22.04', spec='ubuntu-latest'",
            err,
        )
        self.assertIn(
            "changes timeout-minutes does not match spec: workflow='7', spec='5'",
            err,
        )
        self.assertIn("changes outputs does not match spec changes outputs.", err)
        self.assertIn("failure-hints permissions does not match spec failure-hints permissions.", err)

    def test_job_contracts_check_fails_when_strategy_fail_fast_drifts(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              foundry:
                runs-on: ubuntu-latest
                timeout-minutes: 15
                strategy:
                  fail-fast: true
                  matrix:
                    shard_index: [0, 1]
                steps: []
            """
        )
        rc, _, err = self._run_job_contracts_check(
            workflow,
            expected_job_needs={"foundry": []},
            expected_job_if_conditions={"foundry": None},
            expected_job_runs_on={"foundry": "ubuntu-latest"},
            expected_job_timeouts={"foundry": 15},
            expected_job_strategy_fail_fast={"foundry": False},
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "foundry strategy.fail-fast does not match spec: workflow='true', spec='false'",
            err,
        )

    def test_job_contracts_check_passes_when_workflow_platform_contracts_match_spec(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            permissions:
              contents: read
            concurrency:
              group: ${{ github.workflow }}-${{ github.ref }}
              cancel-in-progress: true
            env:
              SOLC_VERSION: "0.8.33"
              SOLC_URL: "https://example.invalid/solc"
            jobs:
              changes:
                runs-on: ubuntu-latest
                timeout-minutes: 5
                outputs:
                  code: ${{ steps.filter.outputs.code }}
                  compiler: ${{ steps.filter.outputs.compiler }}
                steps: []
              failure-hints:
                runs-on: ubuntu-latest
                permissions:
                  contents: read
                  pull-requests: write
                steps: []
            """
        )
        rc, out, err = self._run_job_contracts_check(
            workflow,
            expected_job_needs={"changes": [], "failure-hints": []},
            expected_job_if_conditions={"changes": None, "failure-hints": None},
            expected_job_runs_on={
                "changes": "ubuntu-latest",
                "failure-hints": "ubuntu-latest",
            },
            expected_job_timeouts={"changes": 5},
            expected_job_outputs={
                "changes": {
                    "code": "${{ steps.filter.outputs.code }}",
                    "compiler": "${{ steps.filter.outputs.compiler }}",
                }
            },
            expected_job_permissions={
                "failure-hints": {
                    "contents": "read",
                    "pull-requests": "write",
                }
            },
            expected_workflow_permissions={"contents": "read"},
            expected_workflow_concurrency={
                "group": "${{ github.workflow }}-${{ github.ref }}",
                "cancel-in-progress": "true",
            },
            expected_workflow_env={
                "SOLC_VERSION": "0.8.33",
                "SOLC_URL": "https://example.invalid/solc",
            },
        )
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] job-contracts", out)

    def test_job_contracts_check_passes_when_strategy_fail_fast_matches_spec(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              foundry:
                runs-on: ubuntu-latest
                timeout-minutes: 15
                strategy:
                  fail-fast: false
                  matrix:
                    shard_index: [0, 1]
                steps: []
              foundry-multi-seed:
                runs-on: ubuntu-latest
                timeout-minutes: 25
                strategy:
                  fail-fast: false
                  matrix:
                    seed: [42, 123]
                steps: []
            """
        )
        rc, out, err = self._run_job_contracts_check(
            workflow,
            expected_job_needs={"foundry": [], "foundry-multi-seed": []},
            expected_job_if_conditions={"foundry": None, "foundry-multi-seed": None},
            expected_job_runs_on={
                "foundry": "ubuntu-latest",
                "foundry-multi-seed": "ubuntu-latest",
            },
            expected_job_timeouts={"foundry": 15, "foundry-multi-seed": 25},
            expected_job_strategy_fail_fast={
                "foundry": False,
                "foundry-multi-seed": False,
            },
        )
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] job-contracts", out)

    def test_job_contracts_check_fails_when_multiline_needs_contains_empty_item(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps: []
              build:
                runs-on: ubuntu-latest
                needs:
                  -
                steps: []
            """
        )
        job_body = check.extract_job_body(workflow, "build", Path("verify.yml"))
        with self.assertRaisesRegex(ValueError, "Empty needs entry"):
            check._extract_job_needs(job_body)

    def test_step_contracts_check_fails_when_action_config_drifts(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: actions/checkout@v4
                  - id: changed-filter
                    uses: dorny/paths-filter@v3
              checks:
                runs-on: ubuntu-latest
                steps:
                  - uses: actions/checkout@v4
                  - name: Run all checks
                    run: make verify
              build:
                runs-on: ubuntu-latest
                steps:
                  - uses: actions/checkout@v4
                    with:
                      submodules: false
                  - name: Setup Lean
                    uses: ./.github/actions/setup-lean
                    with:
                      cache-key-prefix: stale
                  - name: Save Lake packages cache
                    if: success()
                    uses: actions/cache/save@v4
                    with:
                      path: build-cache
                      key: bad-key
              failure-hints:
                runs-on: ubuntu-latest
                steps:
                  - name: Post CI failure hints
                    uses: actions/github-script@v7
                    env:
                      NEEDS_JSON: stale
                    with:
                      script: |
                        core.info("stale")
            """
        )
        rc, _, err = self._run_step_contracts_check(
            workflow,
            expected_step_contracts={
                "changes": [
                    {
                        "uses": "actions/checkout@v4",
                    },
                    {
                        "id": "filter",
                        "uses": "dorny/paths-filter@v3",
                    },
                ],
                "checks": [
                    {
                        "uses": "actions/checkout@v4",
                    },
                    {
                        "name": "Run all checks",
                        "run": "make check",
                    },
                ],
                "build": [
                    {
                        "uses": "actions/checkout@v4",
                        "with": {"submodules": "recursive"},
                    },
                    {
                        "name": "Setup Lean",
                        "uses": "./.github/actions/setup-lean",
                        "with": {"cache-key-prefix": "lake"},
                    },
                    {
                        "name": "Save current run Lake cache",
                        "uses": "actions/cache/save@v4",
                        "if": "success() && needs.changes.outputs.code == 'true'",
                        "with": {"path": ".lake", "key": "run-key"},
                    },
                    {
                        "name": "Save Lake packages cache",
                        "uses": "actions/cache/save@v4",
                        "if": "success() && needs.changes.outputs.code == 'true' && steps.setup-lean.outputs.cache-hit != 'true'",
                        "with": {"path": ".lake", "key": "good-key"},
                    },
                ],
                "failure-hints": [
                    {
                        "name": "Post CI failure hints",
                        "uses": "actions/github-script@v7",
                        "env": {"NEEDS_JSON": "${{ toJson(needs) }}"},
                        "with": {"script": FAILURE_HINTS_SCRIPT},
                    }
                ],
            },
        )
        self.assertEqual(rc, 1)
        self.assertIn("[FAIL] step-contracts", err)
        self.assertIn(
            "changes is missing expected step id='filter', uses='dorny/paths-filter@v3'",
            err,
        )
        self.assertIn(
            "checks step name='Run all checks' has run='make verify', expected 'make check'",
            err,
        )
        self.assertIn(
            "build step name='Setup Lean', uses='./.github/actions/setup-lean' has with.cache-key-prefix='stale', expected 'lake'",
            err,
        )
        self.assertIn(
            "build step name='Save Lake packages cache', uses='actions/cache/save@v4' has if='success()', expected \"success() && needs.changes.outputs.code == 'true' && steps.setup-lean.outputs.cache-hit != 'true'\"",
            err,
        )
        self.assertIn(
            "failure-hints step name='Post CI failure hints', uses='actions/github-script@v7' has env.NEEDS_JSON='stale', expected '${{ toJson(needs) }}'",
            err,
        )
        self.assertIn(
            "failure-hints step name='Post CI failure hints', uses='actions/github-script@v7' has with.script='core.info(\"stale\")', expected",
            err,
        )

    def test_step_contracts_check_passes_when_critical_steps_match_spec(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: actions/checkout@v4
                  - id: filter
                    uses: dorny/paths-filter@v3
              checks:
                runs-on: ubuntu-latest
                steps:
                  - uses: actions/checkout@v4
                  - name: Run all checks
                    run: make check
              build:
                runs-on: ubuntu-latest
                steps:
                  - uses: actions/checkout@v4
                    with:
                      submodules: recursive
                  - name: Setup Lean
                    uses: ./.github/actions/setup-lean
                    with:
                      cache-key-prefix: lake
                  - name: Save current run Lake cache
                    if: success() && needs.changes.outputs.code == 'true'
                    uses: actions/cache/save@v4
                    with:
                      path: .lake
                      key: run-key
                  - name: Save Lake packages cache
                    if: success() && needs.changes.outputs.code == 'true' && steps.setup-lean.outputs.cache-hit != 'true'
                    uses: actions/cache/save@v4
                    with:
                      path: .lake
                      key: good-key
              failure-hints:
                runs-on: ubuntu-latest
                steps:
                  - name: Post CI failure hints
                    uses: actions/github-script@v7
                    env:
                      NEEDS_JSON: ${{ toJson(needs) }}
                    with:
                      script: |
                        const marker = "<!-- ci-failure-hints -->";
                        const needs = JSON.parse(process.env.NEEDS_JSON || "{}");
                        const failed = Object.entries(needs)
                          .filter(([, info]) => info && info.result === "failure")
                          .map(([name]) => name);
                        if (failed.length === 0) {
                          core.info("No failed jobs; no hint comment needed.");
                          return;
                        }

                        const lines = [];
                        lines.push(marker);
                        lines.push("### CI Failure Hints");
                        lines.push("");
                        lines.push("Failed jobs: " + failed.map((n) => "`" + n + "`").join(", "));
                        lines.push("");
                        lines.push("Copy-paste local triage:");
                        lines.push("```bash");
                        lines.push("make check");
                        lines.push("lake build");
                        lines.push("FOUNDRY_PROFILE=difftest forge test -vv");
                        lines.push("```");
                        const body = lines.join("\\n");

                        const owner = context.repo.owner;
                        const repo = context.repo.repo;
                        const issue_number = context.issue.number;
                        const comments = await github.paginate(github.rest.issues.listComments, {
                          owner,
                          repo,
                          issue_number,
                          per_page: 100
                        });
                        const existing = comments.find((c) =>
                          c.user && c.user.type === "Bot" && typeof c.body === "string" && c.body.includes(marker)
                        );
                        if (existing) {
                          await github.rest.issues.updateComment({
                            owner,
                            repo,
                            comment_id: existing.id,
                            body
                          });
                        } else {
                          await github.rest.issues.createComment({
                            owner,
                            repo,
                            issue_number,
                            body
                          });
                        }
            """
        )
        rc, out, err = self._run_step_contracts_check(
            workflow,
            expected_step_contracts={
                "changes": [
                    {
                        "uses": "actions/checkout@v4",
                    },
                    {
                        "id": "filter",
                        "uses": "dorny/paths-filter@v3",
                    },
                ],
                "checks": [
                    {
                        "uses": "actions/checkout@v4",
                    },
                    {
                        "name": "Run all checks",
                        "run": "make check",
                    },
                ],
                "build": [
                    {
                        "uses": "actions/checkout@v4",
                        "with": {"submodules": "recursive"},
                    },
                    {
                        "name": "Setup Lean",
                        "uses": "./.github/actions/setup-lean",
                        "with": {"cache-key-prefix": "lake"},
                    },
                    {
                        "name": "Save current run Lake cache",
                        "uses": "actions/cache/save@v4",
                        "if": "success() && needs.changes.outputs.code == 'true'",
                        "with": {"path": ".lake", "key": "run-key"},
                    },
                    {
                        "name": "Save Lake packages cache",
                        "uses": "actions/cache/save@v4",
                        "if": "success() && needs.changes.outputs.code == 'true' && steps.setup-lean.outputs.cache-hit != 'true'",
                        "with": {"path": ".lake", "key": "good-key"},
                    },
                ],
                "failure-hints": [
                    {
                        "name": "Post CI failure hints",
                        "uses": "actions/github-script@v7",
                        "env": {"NEEDS_JSON": "${{ toJson(needs) }}"},
                        "with": {"script": FAILURE_HINTS_SCRIPT},
                    }
                ],
            },
        )
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] step-contracts", out)

    def test_step_contracts_check_folds_with_script_block_scalars(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              failure-hints:
                runs-on: ubuntu-latest
                steps:
                  - name: Post CI failure hints
                    uses: actions/github-script@v7
                    with:
                      script: >-
                        const marker = "<!-- ci-failure-hints -->";

                        core.info(marker);
            """
        )
        rc, out, err = self._run_step_contracts_check(
            workflow,
            expected_step_contracts={
                "failure-hints": [
                    {
                        "name": "Post CI failure hints",
                        "uses": "actions/github-script@v7",
                        "with": {
                            "script": 'const marker = "<!-- ci-failure-hints -->";\ncore.info(marker);'
                        },
                    }
                ]
            },
        )
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] step-contracts", out)

    def test_paths_check_fails_when_check_only_path_is_missing_from_triggers(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                paths:
                  - 'docs/**'
                  - 'README.md'
                  - 'Compiler/**'
              pull_request:
                paths:
                  - 'docs/**'
                  - 'README.md'
                  - 'Compiler/**'
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - 'Compiler/**'
                        compiler:
                          - 'Compiler/**'
            """
        )
        rc, _, err = self._run_paths_check(
            workflow,
            check_only_paths=["docs/**", "README.md", "AUDIT.md"],
            compiler_paths=["Compiler/**"],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "check_only_paths includes entries missing from on.push.paths: AUDIT.md",
            err,
        )

    def test_paths_check_fails_when_workflow_glob_is_missing_from_triggers(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                paths:
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
              pull_request:
                paths:
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
                        compiler:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
            """
        )
        rc, _, err = self._run_paths_check(
            workflow,
            check_only_paths=[".github/workflows/**"],
            compiler_paths=[".github/workflows/verify.yml", "scripts/**"],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "check_only_paths includes entries missing from on.push.paths: .github/workflows/**",
            err,
        )

    def test_paths_check_fails_when_artifacts_are_missing_from_triggers(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                paths:
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
              pull_request:
                paths:
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
                        compiler:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
            """
        )
        rc, _, err = self._run_paths_check(
            workflow,
            check_only_paths=["artifacts/**"],
            compiler_paths=[".github/workflows/verify.yml", "scripts/**"],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "check_only_paths includes entries missing from on.push.paths: artifacts/**",
            err,
        )

    def test_paths_check_fails_when_artifacts_are_missing_from_triggers(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                paths:
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
              pull_request:
                paths:
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
                        compiler:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
            """
        )
        rc, _, err = self._run_paths_check(
            workflow,
            check_only_paths=["artifacts/**"],
            compiler_paths=[".github/workflows/verify.yml", "scripts/**"],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "check_only_paths includes entries missing from on.push.paths: artifacts/**",
            err,
        )

    def test_paths_check_passes_with_workflow_wildcard_and_explicit_verify_filters(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                paths:
                  - '.github/workflows/**'
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
              pull_request:
                paths:
                  - '.github/workflows/**'
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
                        compiler:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
            """
        )
        rc, out, err = self._run_paths_check(
            workflow,
            check_only_paths=[".github/workflows/**"],
            compiler_paths=[".github/workflows/verify.yml", "scripts/**"],
        )
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] paths", out)

    def test_paths_check_accepts_makefile_as_check_only_trigger(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                paths:
                  - 'scripts/**'
                  - 'Makefile'
              pull_request:
                paths:
                  - 'scripts/**'
                  - 'Makefile'
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - 'scripts/**'
                        compiler:
                          - 'scripts/**'
            """
        )
        rc, out, err = self._run_paths_check(
            workflow,
            check_only_paths=["Makefile"],
            compiler_paths=["scripts/**"],
        )
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] paths", out)

    def test_paths_check_fails_when_makefile_is_missing_from_triggers(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                paths:
                  - 'scripts/**'
              pull_request:
                paths:
                  - 'scripts/**'
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - 'scripts/**'
                        compiler:
                          - 'scripts/**'
            """
        )
        rc, _, err = self._run_paths_check(
            workflow,
            check_only_paths=["Makefile"],
            compiler_paths=["scripts/**"],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "check_only_paths includes entries missing from on.push.paths: Makefile",
            err,
        )

    def test_python_commands_check_fails_when_required_build_run_commands_are_missing(self) -> None:
        workflow = """
        name: verify
        jobs:
          checks:
            runs-on: ubuntu-latest
            steps:
              - run: make check
          build:
            runs-on: ubuntu-latest
            steps:
              - run: python3 scripts/check_lean_warning_regression.py --log lake-build.log
          build-audits:
            runs-on: ubuntu-latest
            steps:
              - run: python3 scripts/check_split_package_builds.py
          build-compiler:
            runs-on: ubuntu-latest
            steps:
              - run: python3 scripts/check_gas.py report
        """
        rc, _, err = self._run_python_commands_check(
            workflow,
            expected_checks_commands=["make check"],
            expected_build_commands=["check_lean_warning_regression.py --log lake-build.log"],
            expected_build_audit_commands=["check_split_package_builds.py"],
            expected_build_compiler_commands=["check_gas.py report"],
            required_build_audit_run_commands=[
                "lake build PrintAxioms",
                "lake env lean PrintAxioms.lean",
            ],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "build-audits job is missing required run commands: "
            "lake build PrintAxioms, "
            "lake env lean PrintAxioms.lean",
            err,
        )

    def test_python_commands_check_passes_when_required_build_run_commands_are_present(self) -> None:
        workflow = """
        name: verify
        jobs:
          checks:
            runs-on: ubuntu-latest
            steps:
              - run: make check
          build:
            runs-on: ubuntu-latest
            steps:
              - run: python3 scripts/check_lean_warning_regression.py --log lake-build.log
          build-audits:
            runs-on: ubuntu-latest
            steps:
              - run: python3 scripts/check_split_package_builds.py
              - run: |
                  lake build PrintAxioms
                  lake env lean PrintAxioms.lean 2>&1 | tee axiom-report-raw.log
              - run: python3 scripts/check_proof_length.py --format=markdown >> $GITHUB_STEP_SUMMARY
          build-compiler:
            runs-on: ubuntu-latest
            steps:
              - run: python3 scripts/check_gas.py report
        """
        rc, out, err = self._run_python_commands_check(
            workflow,
            expected_checks_commands=["make check"],
            expected_build_commands=["check_lean_warning_regression.py --log lake-build.log"],
            expected_build_audit_commands=[
                "check_split_package_builds.py",
                "check_proof_length.py --format=markdown >> $GITHUB_STEP_SUMMARY",
            ],
            expected_build_compiler_commands=["check_gas.py report"],
            required_build_audit_run_commands=[
                "lake build PrintAxioms",
                "lake env lean PrintAxioms.lean",
            ],
        )
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] python-commands", out)

    def test_python_commands_check_fails_when_required_build_compiler_run_commands_are_missing(self) -> None:
        workflow = """
        name: verify
        jobs:
          checks:
            runs-on: ubuntu-latest
            steps:
              - run: make check
          build:
            runs-on: ubuntu-latest
            steps:
              - run: python3 scripts/check_lean_warning_regression.py --log lake-build.log
          build-compiler:
            runs-on: ubuntu-latest
            steps:
              - run: lake build difftest-interpreter
              - run: ./.lake/build/bin/verity-compiler --manifest packages/verity-examples/contracts.manifest --output compiler/yul
          compiler-audits:
            runs-on: ubuntu-latest
            steps:
              - run: python3 scripts/check_gas.py report
        """
        rc, _, err = self._run_python_commands_check(
            workflow,
            expected_checks_commands=["make check"],
            expected_build_commands=["check_lean_warning_regression.py --log lake-build.log"],
            expected_build_compiler_commands=[],
            expected_compiler_audit_commands=["check_gas.py report"],
            required_build_compiler_run_commands=[
                "lake build difftest-interpreter",
                "--output compiler/yul",
                "--output compiler/yul-patched",
                "lake exe gas-report --manifest packages/verity-examples/contracts.manifest > gas-report-static.tsv",
                "lake exe gas-report --manifest packages/verity-examples/contracts.manifest --enable-patches --patch-max-iterations 2 > gas-report-static-patched.tsv",
            ],
            required_compiler_audit_run_commands=[
                "--parity-pack solc-0.8.33-o200-viair-false-evm-shanghai",
                "--backend-profile solidity-parity",
            ],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "build-compiler job is missing required run commands: "
            "--output compiler/yul-patched, "
            "lake exe gas-report --manifest packages/verity-examples/contracts.manifest > gas-report-static.tsv, "
            "lake exe gas-report --manifest packages/verity-examples/contracts.manifest --enable-patches --patch-max-iterations 2 > gas-report-static-patched.tsv",
            err,
        )
        self.assertIn(
            "compiler-audits job is missing required run commands: "
            "--parity-pack solc-0.8.33-o200-viair-false-evm-shanghai, "
            "--backend-profile solidity-parity",
            err,
        )

    def test_python_commands_check_does_not_treat_yul_patched_as_yul(self) -> None:
        workflow = """
        name: verify
        jobs:
          checks:
            runs-on: ubuntu-latest
            steps:
              - run: make check
          build:
            runs-on: ubuntu-latest
            steps:
              - run: python3 scripts/check_lean_warning_regression.py --log lake-build.log
          build-compiler:
            runs-on: ubuntu-latest
            steps:
              - run: lake build difftest-interpreter
              - run: |
                  ./.lake/build/bin/verity-compiler \
                    --manifest packages/verity-examples/contracts.manifest \
                    --enable-patches \
                    --output compiler/yul-patched
              - run: lake exe gas-report --manifest packages/verity-examples/contracts.manifest > gas-report-static.tsv
              - run: lake exe gas-report --manifest packages/verity-examples/contracts.manifest --enable-patches --patch-max-iterations 2 > gas-report-static-patched.tsv
          compiler-audits:
            runs-on: ubuntu-latest
            steps:
              - run: ./.lake/build/bin/verity-compiler-patched --parity-pack solc-0.8.33-o200-viair-false-evm-shanghai --backend-profile solidity-parity
              - run: python3 scripts/check_gas.py report
        """
        rc, _, err = self._run_python_commands_check(
            workflow,
            expected_checks_commands=["make check"],
            expected_build_commands=["check_lean_warning_regression.py --log lake-build.log"],
            expected_build_compiler_commands=[],
            expected_compiler_audit_commands=["check_gas.py report"],
            required_build_compiler_run_commands=[
                "lake build difftest-interpreter",
                "--output compiler/yul",
                "--output compiler/yul-patched",
                "lake exe gas-report --manifest packages/verity-examples/contracts.manifest > gas-report-static.tsv",
                "lake exe gas-report --manifest packages/verity-examples/contracts.manifest --enable-patches --patch-max-iterations 2 > gas-report-static-patched.tsv",
            ],
            required_compiler_audit_run_commands=[
                "--parity-pack solc-0.8.33-o200-viair-false-evm-shanghai",
                "--backend-profile solidity-parity",
            ],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "build-compiler job is missing required run commands: --output compiler/yul",
            err,
        )

    def test_python_commands_check_passes_when_required_build_compiler_run_commands_are_present(self) -> None:
        workflow = """
        name: verify
        jobs:
          checks:
            runs-on: ubuntu-latest
            steps:
              - run: make check
          build:
            runs-on: ubuntu-latest
            steps:
              - run: python3 scripts/check_lean_warning_regression.py --log lake-build.log
          build-compiler:
            runs-on: ubuntu-latest
            steps:
              - run: lake build difftest-interpreter
              - run: ./.lake/build/bin/verity-compiler --manifest packages/verity-examples/contracts.manifest --output compiler/yul
              - run: ./.lake/build/bin/verity-compiler --manifest packages/verity-examples/contracts.manifest --enable-patches --output compiler/yul-patched
              - run: lake exe gas-report --manifest packages/verity-examples/contracts.manifest > gas-report-static.tsv
              - run: lake exe gas-report --manifest packages/verity-examples/contracts.manifest --enable-patches --patch-max-iterations 2 > gas-report-static-patched.tsv
          compiler-audits:
            runs-on: ubuntu-latest
            steps:
              - run: ./.lake/build/bin/verity-compiler --manifest packages/verity-examples/contracts.manifest --parity-pack solc-0.8.33-o200-viair-false-evm-shanghai --output compiler/yul-parity-pack
              - run: ./.lake/build/bin/verity-compiler --manifest packages/verity-examples/contracts.manifest --backend-profile solidity-parity --output compiler/yul-parity-reference
              - run: python3 scripts/check_gas.py report
        """
        rc, out, err = self._run_python_commands_check(
            workflow,
            expected_checks_commands=["make check"],
            expected_build_commands=["check_lean_warning_regression.py --log lake-build.log"],
            expected_build_compiler_commands=[],
            expected_compiler_audit_commands=["check_gas.py report"],
            required_build_compiler_run_commands=[
                "lake build difftest-interpreter",
                "--output compiler/yul",
                "--output compiler/yul-patched",
                "lake exe gas-report --manifest packages/verity-examples/contracts.manifest > gas-report-static.tsv",
                "lake exe gas-report --manifest packages/verity-examples/contracts.manifest --enable-patches --patch-max-iterations 2 > gas-report-static-patched.tsv",
            ],
            required_compiler_audit_run_commands=[
                "--parity-pack solc-0.8.33-o200-viair-false-evm-shanghai",
                "--backend-profile solidity-parity",
            ],
        )
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] python-commands", out)

    def test_makefile_check_fails_when_required_unit_test_command_is_missing(self) -> None:
        rc, _, err = self._run_makefile_check(
            """
            check:
            	python3 scripts/generate_verification_status.py --check
            	python3 scripts/check_verification_status_doc.py
            	python3 scripts/check_verify_sync.py
            	python3 scripts/check_issue_templates.py
            	python3 scripts/check_docs_workflow_sync.py
            	python3 scripts/check_solc_pin.py
            """,
            expected_checks_commands=["make check"],
            required_makefile_check_commands=[
                "python3 scripts/generate_verification_status.py --check",
                "python3 scripts/check_verification_status_doc.py",
                "python3 scripts/check_verify_sync.py",
                "python3 scripts/check_issue_templates.py",
                "python3 scripts/check_docs_workflow_sync.py",
                "python3 scripts/check_solc_pin.py",
                "python3 -m unittest discover -s scripts -p 'test_*.py' -v",
            ],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "Makefile check target is missing required commands: "
            "python3 -m unittest discover -s scripts -p 'test_*.py' -v",
            err,
        )

    def test_makefile_check_passes_when_required_commands_are_present(self) -> None:
        makefile = """
        check:
        \tpython3 scripts/generate_verification_status.py --check
        \tpython3 scripts/check_verification_status_doc.py
        \tpython3 scripts/check_verify_sync.py
        \tpython3 scripts/check_issue_templates.py
        \tpython3 scripts/check_docs_workflow_sync.py
        \tpython3 scripts/check_solc_pin.py
        \tpython3 scripts/check_rewrite_proof_metadata.py
        \tpython3 scripts/generate_evmyullean_capability_report.py --check
        \tpython3 scripts/generate_evmyullean_adapter_report.py --check
        \tpython3 scripts/generate_print_axioms.py --check
        \tpython3 scripts/check_issue_1060_integrity.py
        \tpython3 -m unittest discover -s scripts -p 'test_*.py' -v
        """
        rc, out, err = self._run_makefile_check(
            makefile,
            expected_checks_commands=["make check"],
            required_makefile_check_commands=[
                "python3 scripts/generate_verification_status.py --check",
                "python3 scripts/check_verification_status_doc.py",
                "python3 scripts/check_verify_sync.py",
                "python3 scripts/check_issue_templates.py",
                "python3 scripts/check_docs_workflow_sync.py",
                "python3 scripts/check_solc_pin.py",
                "python3 scripts/check_rewrite_proof_metadata.py",
                "python3 scripts/generate_evmyullean_capability_report.py --check",
                "python3 scripts/generate_evmyullean_adapter_report.py --check",
                "python3 scripts/generate_print_axioms.py --check",
                "python3 scripts/check_issue_1060_integrity.py",
            ],
        )
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] makefile", out)

    def test_makefile_check_fails_when_generated_report_commands_are_missing(self) -> None:
        makefile = """
        check:
        \tpython3 scripts/generate_verification_status.py --check
        \tpython3 scripts/check_verification_status_doc.py
        \tpython3 scripts/check_verify_sync.py
        \tpython3 scripts/check_issue_templates.py
        \tpython3 scripts/check_docs_workflow_sync.py
        \tpython3 scripts/check_solc_pin.py
        \tpython3 -m unittest discover -s scripts -p 'test_*.py' -v
        """
        rc, _, err = self._run_makefile_check(
            makefile,
            expected_checks_commands=["make check"],
            required_makefile_check_commands=[
                "python3 scripts/generate_verification_status.py --check",
                "python3 scripts/check_verification_status_doc.py",
                "python3 scripts/check_verify_sync.py",
                "python3 scripts/check_issue_templates.py",
                "python3 scripts/check_docs_workflow_sync.py",
                "python3 scripts/check_solc_pin.py",
                "python3 scripts/check_rewrite_proof_metadata.py",
                "python3 scripts/generate_evmyullean_capability_report.py --check",
                "python3 scripts/generate_evmyullean_adapter_report.py --check",
                "python3 scripts/generate_print_axioms.py --check",
                "python3 scripts/check_issue_1060_integrity.py",
                "python3 -m unittest discover -s scripts -p 'test_*.py' -v",
            ],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "Makefile check target is missing required commands: "
            "python3 scripts/check_rewrite_proof_metadata.py, "
            "python3 scripts/generate_evmyullean_capability_report.py --check, "
            "python3 scripts/generate_evmyullean_adapter_report.py --check, "
            "python3 scripts/generate_print_axioms.py --check, "
            "python3 scripts/check_issue_1060_integrity.py",
            err,
        )

    def test_makefile_check_fails_when_required_solc_pin_command_is_missing(self) -> None:
        makefile = """
        check:
        \tpython3 scripts/generate_verification_status.py --check
        \tpython3 scripts/check_verification_status_doc.py
        \tpython3 scripts/check_verify_sync.py
        \tpython3 scripts/check_issue_templates.py
        \tpython3 scripts/check_docs_workflow_sync.py
        """
        rc, _, err = self._run_makefile_check(
            makefile,
            expected_checks_commands=["make check"],
            required_makefile_check_commands=[
                "python3 scripts/generate_verification_status.py --check",
                "python3 scripts/check_verification_status_doc.py",
                "python3 scripts/check_verify_sync.py",
                "python3 scripts/check_issue_templates.py",
                "python3 scripts/check_docs_workflow_sync.py",
                "python3 scripts/check_solc_pin.py",
            ],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "Makefile check target is missing required commands: python3 scripts/check_solc_pin.py",
            err,
        )

    def test_makefile_check_fails_when_boundary_and_hygiene_commands_are_missing(self) -> None:
        makefile = """
        check:
        \tpython3 scripts/check_property_manifest.py
        \tpython3 scripts/check_property_coverage.py
        \tpython3 scripts/check_contract_structure.py
        \tpython3 scripts/check_paths.py
        \tpython3 scripts/check_compilationmodel_split.py
        \tpython3 scripts/check_axioms.py
        \tpython3 scripts/generate_verification_status.py --check
        \tpython3 scripts/check_verification_status_doc.py
        \tpython3 scripts/check_verify_sync.py
        \tpython3 scripts/check_issue_templates.py
        \tpython3 scripts/check_docs_workflow_sync.py
        \tpython3 scripts/check_solc_pin.py
        \tpython3 scripts/check_rewrite_proof_metadata.py
        \tpython3 scripts/generate_evmyullean_capability_report.py --check
        \tpython3 scripts/generate_evmyullean_adapter_report.py --check
        \tpython3 scripts/generate_print_axioms.py --check
        \tpython3 scripts/check_issue_1060_integrity.py
        \tpython3 -m unittest discover -s scripts -p 'test_*.py' -v
        """
        rc, _, err = self._run_makefile_check(
            makefile,
            expected_checks_commands=["make check"],
            required_makefile_check_commands=[
                "python3 scripts/check_property_manifest.py",
                "python3 scripts/check_property_coverage.py",
                "python3 scripts/check_contract_structure.py",
                "python3 scripts/check_paths.py",
                "python3 scripts/check_compilationmodel_split.py",
                "python3 scripts/check_axioms.py",
                "python3 scripts/generate_verification_status.py --check",
                "python3 scripts/check_verification_status_doc.py",
                "python3 scripts/check_verify_sync.py",
                "python3 scripts/check_bridge_coverage_sync.py",
                "python3 scripts/check_builtin_bridge_matrix_sync.py",
                "python3 scripts/check_interpreter_feature_boundary_catalog_sync.py",
                "python3 scripts/check_interpreter_feature_summary_sync.py",
                "python3 scripts/check_low_level_call_boundary_sync.py",
                "python3 scripts/check_linear_memory_boundary_sync.py",
                "python3 scripts/check_axiomatized_primitive_boundary_sync.py",
                "python3 scripts/check_struct_mapping_surface_sync.py",
                "python3 scripts/check_issue_templates.py",
                "python3 scripts/check_docs_workflow_sync.py",
                "python3 scripts/check_solc_pin.py",
                "python3 scripts/check_property_manifest_sync.py",
                "python3 scripts/check_macro_health.py",
                "python3 scripts/check_storage_layout.py",
                "python3 scripts/check_lean_hygiene.py",
                "python3 scripts/check_gas.py coverage",
                "python3 scripts/check_compiler_boundaries.py",
                "python3 scripts/check_split_compiler_test_artifacts.py",
                "python3 scripts/check_yul.py --builtin-boundary-only",
                "python3 scripts/check_rewrite_proof_metadata.py",
                "python3 scripts/generate_evmyullean_capability_report.py --check",
                "python3 scripts/generate_evmyullean_adapter_report.py --check",
                "python3 scripts/generate_print_axioms.py --check",
                "python3 scripts/check_proof_length.py",
                "python3 scripts/check_issue_1060_integrity.py",
                "python3 -m unittest discover -s scripts -p 'test_*.py' -v",
            ],
        )
        self.assertEqual(rc, 1)
        self.assertIn("python3 scripts/check_bridge_coverage_sync.py", err)
        self.assertIn("python3 scripts/check_storage_layout.py", err)
        self.assertIn("python3 scripts/check_proof_length.py", err)

    def test_artifacts_check_fails_when_expected_upload_is_missing(self) -> None:
        workflow = """
        name: verify
        jobs:
          build-audits:
            runs-on: ubuntu-latest
            steps:
              - uses: actions/upload-artifact@v4
                with:
                  name: axiom-dependency-report
          build-compiler:
            runs-on: ubuntu-latest
            steps:
              - uses: actions/upload-artifact@v4
                with:
                  name: generated-yul
          foundry:
            runs-on: ubuntu-latest
            steps:
              - uses: actions/download-artifact@v4
                with:
                  name: generated-yul
        """
        rc, _, err = self._run_artifacts_check(
            workflow,
            expected_uploaded_artifacts={
                "build-audits": ["axiom-dependency-report"],
                "build-compiler": ["generated-yul", "static-gas-report"],
            },
            expected_downloaded_artifacts={
                "foundry": ["generated-yul"],
            },
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "build-compiler upload artifacts does not match spec build-compiler upload artifacts.",
            err,
        )
        self.assertIn(
            "idx 1: build-compiler upload artifacts='<missing>', spec build-compiler upload artifacts='static-gas-report'",
            err,
        )

    def test_artifacts_check_fails_when_upload_name_is_empty(self) -> None:
        job_body = textwrap.dedent(
            """
            runs-on: ubuntu-latest
            steps:
              - uses: actions/upload-artifact@v4
                with:
                  name:
            """
        ).lstrip()
        with self.assertRaisesRegex(
            ValueError, "Found upload-artifact step without literal with.name"
        ):
            check._extract_artifact_names(job_body, action="upload-artifact")

    def test_artifacts_check_fails_when_upload_path_drifts(self) -> None:
        workflow = """
        name: verify
        jobs:
          build-audits:
            runs-on: ubuntu-latest
            steps:
              - uses: actions/upload-artifact@v4
                with:
                  name: axiom-dependency-report
                  path: |
                    axiom-report.md
                    unexpected.log
        """
        rc, _, err = self._run_artifacts_check(
            workflow,
            expected_uploaded_artifacts={
                "build-audits": ["axiom-dependency-report"],
            },
            expected_downloaded_artifacts={},
            expected_uploaded_artifact_paths={
                "build-audits": ["axiom-report.md\naxiom-report-raw.log"],
            },
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "build-audits upload artifact paths does not match spec build-audits upload artifact paths.",
            err,
        )
        self.assertIn(
            "idx 0: build-audits upload artifact paths=\"'axiom-report.md\\\\nunexpected.log'\", spec build-audits upload artifact paths=\"'axiom-report.md\\\\naxiom-report-raw.log'\"",
            err,
        )

    def test_artifacts_check_fails_when_expected_download_is_missing(self) -> None:
        workflow = """
        name: verify
        jobs:
          build-compiler:
            runs-on: ubuntu-latest
            steps:
              - uses: actions/upload-artifact@v4
                with:
                  name: static-gas-report
              - uses: actions/upload-artifact@v4
                with:
                  name: generated-yul
          foundry-gas-calibration:
            runs-on: ubuntu-latest
            steps:
              - uses: actions/download-artifact@v4
                with:
                  name: static-gas-report
        """
        rc, _, err = self._run_artifacts_check(
            workflow,
            expected_uploaded_artifacts={
                "build-compiler": ["static-gas-report", "generated-yul"],
            },
            expected_downloaded_artifacts={
                "foundry-gas-calibration": ["static-gas-report", "generated-yul"],
            },
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "foundry-gas-calibration download artifacts does not match spec foundry-gas-calibration download artifacts.",
            err,
        )
        self.assertIn(
            "idx 1: foundry-gas-calibration download artifacts='<missing>', spec foundry-gas-calibration download artifacts='generated-yul'",
            err,
        )

    def test_artifacts_check_fails_when_download_path_drift_removes_destination(self) -> None:
        workflow = """
        name: verify
        jobs:
          build-compiler:
            runs-on: ubuntu-latest
            steps:
              - uses: actions/upload-artifact@v4
                with:
                  name: generated-yul
                  path: compiler/yul
          foundry:
            runs-on: ubuntu-latest
            steps:
              - uses: actions/download-artifact@v4
                with:
                  name: generated-yul
        """
        rc, _, err = self._run_artifacts_check(
            workflow,
            expected_uploaded_artifacts={
                "build-compiler": ["generated-yul"],
            },
            expected_downloaded_artifacts={
                "foundry": ["generated-yul"],
            },
            expected_uploaded_artifact_paths={
                "build-compiler": ["compiler/yul"],
            },
            expected_downloaded_artifact_paths={
                "foundry": ["compiler/yul"],
            },
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "foundry download artifact paths does not match spec foundry download artifact paths.",
            err,
        )
        self.assertIn(
            "idx 0: foundry download artifact paths='None', spec foundry download artifact paths=\"'compiler/yul'\"",
            err,
        )

    def test_artifacts_check_passes_when_uploads_and_downloads_match_spec(self) -> None:
        workflow = """
        name: verify
        jobs:
          build-audits:
            runs-on: ubuntu-latest
            steps:
              - uses: actions/upload-artifact@v4
                with:
                  name: axiom-dependency-report
                  path: |
                    axiom-report.md
                    axiom-report-raw.log
          build-compiler:
            runs-on: ubuntu-latest
            steps:
              - uses: actions/upload-artifact@v4
                with:
                  name: generated-yul
                  path: compiler/yul
              - uses: actions/upload-artifact@v4
                with:
                  name: static-gas-report
                  path: gas-report-static.tsv
          lean-profile:
            runs-on: ubuntu-latest
            steps:
              - uses: actions/upload-artifact@v4
                with:
                  name: lean-perf-queue
                  path: lean-perf-queue.md
          foundry-gas-calibration:
            runs-on: ubuntu-latest
            steps:
              - uses: actions/download-artifact@v4
                with:
                  name: static-gas-report
              - uses: actions/download-artifact@v4
                with:
                  name: generated-yul
                  path: compiler/yul
        """
        rc, out, err = self._run_artifacts_check(
            workflow,
            expected_uploaded_artifacts={
                "build-audits": ["axiom-dependency-report"],
                "build-compiler": ["generated-yul", "static-gas-report"],
                "lean-profile": ["lean-perf-queue"],
            },
            expected_downloaded_artifacts={
                "foundry-gas-calibration": ["static-gas-report", "generated-yul"],
            },
            expected_uploaded_artifact_paths={
                "build-audits": ["axiom-report.md\naxiom-report-raw.log"],
                "build-compiler": ["compiler/yul", "gas-report-static.tsv"],
                "lean-profile": ["lean-perf-queue.md"],
            },
            expected_downloaded_artifact_paths={
                "foundry-gas-calibration": [None, "compiler/yul"],
            },
        )
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] artifacts", out)


if __name__ == "__main__":
    unittest.main()
