#!/usr/bin/env python3
"""Fast AXLE verify_proof pre-check for changed Lean files in CI."""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

AXLE_BASE_URL = "https://axle.axiommath.ai"
FALLBACK_ENVIRONMENT = "lean-4.28.0"
REQUEST_TIMEOUT_SECONDS = 180


def _post_json(url: str, payload: dict[str, Any], api_key: str) -> dict[str, Any]:
    body = json.dumps(payload).encode("utf-8")
    request = Request(
        url,
        data=body,
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        },
        method="POST",
    )
    try:
        with urlopen(request, timeout=REQUEST_TIMEOUT_SECONDS) as response:
            return json.loads(response.read().decode("utf-8"))
    except HTTPError as err:
        raw = err.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"HTTP {err.code} from {url}: {raw}") from err
    except URLError as err:
        raise RuntimeError(f"Network error calling {url}: {err}") from err


def _get_json(url: str, api_key: str) -> Any:
    request = Request(
        url,
        headers={"Authorization": f"Bearer {api_key}"},
        method="GET",
    )
    with urlopen(request, timeout=REQUEST_TIMEOUT_SECONDS) as response:
        return json.loads(response.read().decode("utf-8"))


def _detect_environment(repo_root: Path, api_key: str) -> str:
    toolchain_file = repo_root / "lean-toolchain"
    candidate = None
    if toolchain_file.exists():
        text = toolchain_file.read_text(encoding="utf-8").strip()
        match = re.search(r"v(\d+\.\d+\.\d+)", text)
        if match:
            candidate = f"lean-{match.group(1)}"
    if not candidate:
        return FALLBACK_ENVIRONMENT

    try:
        environments = _get_json(f"{AXLE_BASE_URL}/v1/environments", api_key)
    except Exception:
        return FALLBACK_ENVIRONMENT

    names = {env.get("name") for env in environments if isinstance(env, dict)}
    if candidate in names:
        return candidate
    return FALLBACK_ENVIRONMENT


def _parse_changed_files(csv_value: str) -> list[Path]:
    paths: list[Path] = []
    for entry in csv_value.split(","):
        item = entry.strip()
        if not item:
            continue
        paths.append(Path(item))
    return paths


def _has_local_imports(content: str) -> bool:
    for line in content.splitlines():
        stripped = line.strip()
        if not stripped.startswith("import "):
            continue
        modules = stripped[len("import ") :].split()
        if any(module.startswith("Verity") or module.startswith("Compiler") for module in modules):
            return True
    return False


def _first_messages(response: dict[str, Any]) -> list[str]:
    out: list[str] = []
    for key in ("lean_messages", "tool_messages"):
        payload = response.get(key)
        if not isinstance(payload, dict):
            continue
        errors = payload.get("errors")
        if isinstance(errors, list):
            for err in errors[:5]:
                out.append(str(err))
    return out


def _run_smoke_verify(environment: str, api_key: str) -> None:
    formal = "import Mathlib\ntheorem axle_ci_smoke : (1:Nat) = 1 := by sorry\n"
    proof = "import Mathlib\ntheorem axle_ci_smoke : (1:Nat) = 1 := by rfl\n"
    response = _post_json(
        f"{AXLE_BASE_URL}/api/v1/verify_proof",
        {
            "formal_statement": formal,
            "content": proof,
            "environment": environment,
            "ignore_imports": True,
            "timeout_seconds": 60,
        },
        api_key,
    )
    if not response.get("okay", False):
        details = "\n".join(_first_messages(response))
        raise RuntimeError(f"AXLE smoke verify_proof failed.\n{details}")


def main() -> int:
    parser = argparse.ArgumentParser(description="Run AXLE verify_proof on changed Lean files.")
    parser.add_argument("--files-csv", default="", help="Comma-separated changed files from paths-filter.")
    args = parser.parse_args()

    api_key = os.environ.get("AXLE_API_KEY", "").strip()
    if not api_key:
        print("AXLE_API_KEY is not set; skipping AXLE verify_proof pre-check.")
        return 0

    repo_root = Path(__file__).resolve().parents[1]
    environment = _detect_environment(repo_root, api_key)
    print(f"Using AXLE environment: {environment}")

    _run_smoke_verify(environment, api_key)
    print("AXLE verify_proof smoke check passed.")

    changed_files = _parse_changed_files(args.files_csv)
    lean_files = [path for path in changed_files if path.suffix == ".lean"]
    if not lean_files:
        print("No changed Lean files; AXLE file-level checks skipped.")
        return 0

    failures: list[str] = []
    checked = 0
    skipped_local_imports = 0

    for rel_path in lean_files:
        abs_path = repo_root / rel_path
        if not abs_path.exists():
            print(f"Skipping missing file: {rel_path}")
            continue
        content = abs_path.read_text(encoding="utf-8")
        if _has_local_imports(content):
            skipped_local_imports += 1
            print(f"Skipping {rel_path}: local Verity/Compiler imports are not supported by AXLE public envs.")
            continue

        checked += 1
        theorem2sorry = _post_json(
            f"{AXLE_BASE_URL}/api/v1/theorem2sorry",
            {
                "content": content,
                "environment": environment,
                "ignore_imports": True,
                "timeout_seconds": 120,
            },
            api_key,
        )
        formal_statement = theorem2sorry.get("content")
        if not isinstance(formal_statement, str) or not formal_statement.strip():
            failures.append(f"{rel_path}: theorem2sorry did not return transformed content")
            continue

        verify_response = _post_json(
            f"{AXLE_BASE_URL}/api/v1/verify_proof",
            {
                "formal_statement": formal_statement,
                "content": content,
                "environment": environment,
                "ignore_imports": True,
                "timeout_seconds": 120,
            },
            api_key,
        )
        if not verify_response.get("okay", False):
            details = "; ".join(_first_messages(verify_response))
            failures.append(f"{rel_path}: verify_proof failed ({details})")

    print(
        f"AXLE file check summary: checked={checked}, "
        f"skipped_local_imports={skipped_local_imports}, total_changed_lean={len(lean_files)}"
    )
    if failures:
        print("AXLE verify_proof failures:")
        for failure in failures:
            print(f" - {failure}")
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
