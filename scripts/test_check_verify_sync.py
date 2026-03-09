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

    def _run_python_commands_check(
        self,
        workflow_text: str,
        *,
        expected_checks_commands: list[str],
        expected_build_commands: list[str],
        expected_build_compiler_commands: list[str],
        required_build_run_commands: list[str] | None = None,
        required_build_compiler_run_commands: list[str] | None = None,
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
                        "expected_build_compiler_commands": expected_build_compiler_commands,
                        "required_build_run_commands": required_build_run_commands or [],
                        "required_build_compiler_run_commands": required_build_compiler_run_commands or [],
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
              - run: python3 scripts/check_split_package_builds.py
              - run: python3 scripts/check_lean_warning_regression.py --log lake-build.log
              - run: lake exe compiler-main-test
          build-compiler:
            runs-on: ubuntu-latest
            steps:
              - run: python3 scripts/check_gas.py report
        """
        rc, _, err = self._run_python_commands_check(
            workflow,
            expected_checks_commands=["make check"],
            expected_build_commands=[
                "check_split_package_builds.py",
                "check_lean_warning_regression.py --log lake-build.log",
            ],
            expected_build_compiler_commands=["check_gas.py report"],
            required_build_run_commands=[
                "lake exe compiler-main-test",
                "lake build Compiler.CompilationModelFeatureTest",
                "lake exe macro-roundtrip-fuzz",
                "lake build PrintAxioms",
                "lake env lean PrintAxioms.lean",
            ],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "build job is missing required run commands: "
            "lake build Compiler.CompilationModelFeatureTest, "
            "lake exe macro-roundtrip-fuzz, "
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
              - run: python3 scripts/check_split_package_builds.py
              - run: python3 scripts/check_lean_warning_regression.py --log lake-build.log
              - run: |
                  lake exe compiler-main-test
                  lake build Compiler.CompilationModelFeatureTest
                  lake exe macro-roundtrip-fuzz
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
            expected_build_commands=[
                "check_split_package_builds.py",
                "check_lean_warning_regression.py --log lake-build.log",
                "check_proof_length.py --format=markdown >> $GITHUB_STEP_SUMMARY",
            ],
            expected_build_compiler_commands=["check_gas.py report"],
            required_build_run_commands=[
                "lake exe compiler-main-test",
                "lake build Compiler.CompilationModelFeatureTest",
                "lake exe macro-roundtrip-fuzz",
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
              - run: python3 scripts/check_split_package_builds.py
          build-compiler:
            runs-on: ubuntu-latest
            steps:
              - run: lake build difftest-interpreter
              - run: |
                  ./.lake/build/bin/verity-compiler \
                    --manifest packages/verity-examples/contracts.manifest \
                    --output compiler/yul
              - run: python3 scripts/check_gas.py report
        """
        rc, _, err = self._run_python_commands_check(
            workflow,
            expected_checks_commands=["make check"],
            expected_build_commands=["check_split_package_builds.py"],
            expected_build_compiler_commands=["check_gas.py report"],
            required_build_compiler_run_commands=[
                "lake build difftest-interpreter",
                "--output compiler/yul",
                "--output compiler/yul-patched",
                "--parity-pack solc-0.8.33-o200-viair-false-evm-shanghai",
                "--backend-profile solidity-parity",
                "lake exe gas-report --manifest packages/verity-examples/contracts.manifest > gas-report-static.tsv",
                "lake exe gas-report --manifest packages/verity-examples/contracts.manifest --enable-patches --patch-max-iterations 2 > gas-report-static-patched.tsv",
            ],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "build-compiler job is missing required run commands: "
            "--output compiler/yul-patched, "
            "--parity-pack solc-0.8.33-o200-viair-false-evm-shanghai, "
            "--backend-profile solidity-parity, "
            "lake exe gas-report --manifest packages/verity-examples/contracts.manifest > gas-report-static.tsv, "
            "lake exe gas-report --manifest packages/verity-examples/contracts.manifest --enable-patches --patch-max-iterations 2 > gas-report-static-patched.tsv",
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
              - run: python3 scripts/check_split_package_builds.py
          build-compiler:
            runs-on: ubuntu-latest
            steps:
              - run: lake build difftest-interpreter
              - run: |
                  ./.lake/build/bin/verity-compiler \
                    --manifest packages/verity-examples/contracts.manifest \
                    --enable-patches \
                    --output compiler/yul-patched
              - run: |
                  ./.lake/build/bin/verity-compiler \
                    --manifest packages/verity-examples/contracts.manifest \
                    --parity-pack solc-0.8.33-o200-viair-false-evm-shanghai \
                    --backend-profile solidity-parity
              - run: lake exe gas-report --manifest packages/verity-examples/contracts.manifest > gas-report-static.tsv
              - run: lake exe gas-report --manifest packages/verity-examples/contracts.manifest --enable-patches --patch-max-iterations 2 > gas-report-static-patched.tsv
              - run: python3 scripts/check_gas.py report
        """
        rc, _, err = self._run_python_commands_check(
            workflow,
            expected_checks_commands=["make check"],
            expected_build_commands=["check_split_package_builds.py"],
            expected_build_compiler_commands=["check_gas.py report"],
            required_build_compiler_run_commands=[
                "lake build difftest-interpreter",
                "--output compiler/yul",
                "--output compiler/yul-patched",
                "--parity-pack solc-0.8.33-o200-viair-false-evm-shanghai",
                "--backend-profile solidity-parity",
                "lake exe gas-report --manifest packages/verity-examples/contracts.manifest > gas-report-static.tsv",
                "lake exe gas-report --manifest packages/verity-examples/contracts.manifest --enable-patches --patch-max-iterations 2 > gas-report-static-patched.tsv",
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
              - run: python3 scripts/check_split_package_builds.py
          build-compiler:
            runs-on: ubuntu-latest
            steps:
              - run: lake build difftest-interpreter
              - run: ./.lake/build/bin/verity-compiler --manifest packages/verity-examples/contracts.manifest --output compiler/yul
              - run: ./.lake/build/bin/verity-compiler --manifest packages/verity-examples/contracts.manifest --enable-patches --output compiler/yul-patched
              - run: ./.lake/build/bin/verity-compiler --manifest packages/verity-examples/contracts.manifest --parity-pack solc-0.8.33-o200-viair-false-evm-shanghai --output compiler/yul-parity-pack
              - run: ./.lake/build/bin/verity-compiler --manifest packages/verity-examples/contracts.manifest --backend-profile solidity-parity --output compiler/yul-parity-reference
              - run: python3 scripts/check_gas.py report
              - run: lake exe gas-report --manifest packages/verity-examples/contracts.manifest > gas-report-static.tsv
              - run: lake exe gas-report --manifest packages/verity-examples/contracts.manifest --enable-patches --patch-max-iterations 2 > gas-report-static-patched.tsv
        """
        rc, out, err = self._run_python_commands_check(
            workflow,
            expected_checks_commands=["make check"],
            expected_build_commands=["check_split_package_builds.py"],
            expected_build_compiler_commands=["check_gas.py report"],
            required_build_compiler_run_commands=[
                "lake build difftest-interpreter",
                "--output compiler/yul",
                "--output compiler/yul-patched",
                "--parity-pack solc-0.8.33-o200-viair-false-evm-shanghai",
                "--backend-profile solidity-parity",
                "lake exe gas-report --manifest packages/verity-examples/contracts.manifest > gas-report-static.tsv",
                "lake exe gas-report --manifest packages/verity-examples/contracts.manifest --enable-patches --patch-max-iterations 2 > gas-report-static-patched.tsv",
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


if __name__ == "__main__":
    unittest.main()
