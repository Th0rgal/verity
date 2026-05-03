#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_solc_pin


class CheckSolcPinTests(unittest.TestCase):
    def _run(
        self,
        *,
        extra_verify_env: str = "",
        action_body: str | None = None,
    ) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            verify = root / ".github" / "workflows" / "verify.yml"
            action = root / ".github" / "actions" / "setup-solc" / "action.yml"
            foundry = root / "foundry.toml"
            trust = root / "TRUST_ASSUMPTIONS.md"
            verify.parent.mkdir(parents=True, exist_ok=True)
            action.parent.mkdir(parents=True, exist_ok=True)

            verify.write_text(
                "\n".join(
                    [
                        'name: "Verify"',
                        "env:",
                        '  SOLC_VERSION: "0.8.33"',
                        '  SOLC_URL: "https://binaries.soliditylang.org/linux-amd64/solc-linux-amd64-v0.8.33+commit.64118f21"',
                        '  SOLC_SHA256: "1274e5c4621ae478090c5a1f48466fd3c5f658ed9e14b15a0b213dc806215468"',
                        "jobs:",
                        "  build:",
                        "    runs-on: ubuntu-latest",
                        extra_verify_env.rstrip("\n"),
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            action.write_text(
                (
                    action_body
                    or "\n".join(
                        [
                            "name: setup-solc",
                            "runs:",
                            "  using: composite",
                            "  steps:",
                            "    - shell: bash",
                            "      run: |",
                            '        curl -sSfL "$SOLC_URL" -o solc',
                            '        echo "${SOLC_SHA256}  solc" | sha256sum -c -',
                        ]
                    )
                )
                + "\n",
                encoding="utf-8",
            )
            foundry.write_text('[profile.default]\nsolc_version = "0.8.33"\n', encoding="utf-8")
            trust.write_text("**Version**: 0.8.33+commit.64118f21 (pinned)\n", encoding="utf-8")

            old_root = check_solc_pin.ROOT
            old_verify = check_solc_pin.VERIFY_YML
            old_action = check_solc_pin.SETUP_SOLC_ACTION
            old_foundry = check_solc_pin.FOUNDRY_TOML
            old_trust = check_solc_pin.TRUST_ASSUMPTIONS
            check_solc_pin.ROOT = root
            check_solc_pin.VERIFY_YML = verify
            check_solc_pin.SETUP_SOLC_ACTION = action
            check_solc_pin.FOUNDRY_TOML = foundry
            check_solc_pin.TRUST_ASSUMPTIONS = trust
            try:
                stdout = io.StringIO()
                stderr = io.StringIO()
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    rc = check_solc_pin.main()
                return rc, stdout.getvalue(), stderr.getvalue()
            finally:
                check_solc_pin.ROOT = old_root
                check_solc_pin.VERIFY_YML = old_verify
                check_solc_pin.SETUP_SOLC_ACTION = old_action
                check_solc_pin.FOUNDRY_TOML = old_foundry
                check_solc_pin.TRUST_ASSUMPTIONS = old_trust

    def test_rejects_conflicting_job_level_override(self) -> None:
        rc, _stdout, stderr = self._run(
            extra_verify_env="\n".join(
                [
                    "    env:",
                    '      SOLC_VERSION: "0.8.32"',
                    '      SOLC_URL: "https://binaries.soliditylang.org/linux-amd64/solc-linux-amd64-v0.8.32+commit.11223344"',
                    '      SOLC_SHA256: "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"',
                ]
            )
        )
        self.assertEqual(rc, 1)
        self.assertIn("SOLC_VERSION occurrence 2", stderr)
        self.assertIn("SOLC_URL occurrence 2", stderr)
        self.assertIn("SOLC_SHA256 occurrence 2", stderr)

    def test_allows_duplicate_assignments_when_values_match(self) -> None:
        rc, stdout, stderr = self._run(
            extra_verify_env="\n".join(
                [
                    "    env:",
                    '      SOLC_VERSION: "0.8.33"',
                    '      SOLC_URL: "https://binaries.soliditylang.org/linux-amd64/solc-linux-amd64-v0.8.33+commit.64118f21"',
                    '      SOLC_SHA256: "1274e5c4621ae478090c5a1f48466fd3c5f658ed9e14b15a0b213dc806215468"',
                ]
            )
        )
        self.assertEqual(rc, 0)
        self.assertIn("solc pin is consistent", stdout)
        self.assertEqual(stderr, "")

    def test_rejects_privileged_solc_install_path(self) -> None:
        rc, _stdout, stderr = self._run(
            action_body="\n".join(
                [
                    "name: setup-solc",
                    "runs:",
                    "  using: composite",
                    "  steps:",
                    "    - shell: bash",
                    "      run: |",
                    '        curl -sSfL "$SOLC_URL" -o solc',
                    '        echo "${SOLC_SHA256}  solc" | sha256sum -c -',
                    "        sudo mv solc /usr/local/bin/solc",
                ]
            )
        )
        self.assertEqual(rc, 1)
        self.assertIn("workspace-local", stderr)
        self.assertIn("must not require sudo", stderr)


if __name__ == "__main__":
    unittest.main()
