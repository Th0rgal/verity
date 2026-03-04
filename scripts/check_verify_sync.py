#!/usr/bin/env python3
"""Unified verify.yml sync validator (table-driven).

This replaces the fragmented check_verify_* scripts with one config-backed validator
that parses workflow data once and reports all invariant violations in one run.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

from workflow_jobs import (
    extract_job_body,
    extract_literal_from_mapping_blocks,
    extract_python_script_commands,
    extract_run_commands_from_job_body,
    extract_top_level_jobs,
    match_shell_command,
    parse_csv_ints,
    strip_yaml_inline_comment,
    unquote_yaml_scalar,
)

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"
MAKEFILE = ROOT / "Makefile"
MULTISEED_SCRIPT = ROOT / "scripts" / "test_multiple_seeds.sh"
SPEC_PATH = ROOT / "scripts" / "verify_sync_spec.json"


@dataclass(frozen=True)
class CheckResult:
    name: str
    errors: list[str]


@dataclass
class Snapshot:
    workflow_text: str
    workflow_lines: list[str]
    jobs: list[str]

    @classmethod
    def load(cls) -> "Snapshot":
        workflow_text = VERIFY_YML.read_text(encoding="utf-8")
        return cls(
            workflow_text=workflow_text,
            workflow_lines=workflow_text.splitlines(),
            jobs=extract_top_level_jobs(workflow_text, VERIFY_YML),
        )

    def job_body(self, job_name: str) -> str:
        return extract_job_body(self.workflow_text, job_name, VERIFY_YML)

    def run_commands(self, job_name: str) -> list[str]:
        return extract_run_commands_from_job_body(
            self.job_body(job_name), source=VERIFY_YML, context=job_name
        )

    def python_commands(self, job_name: str, *, include_args: bool = True) -> list[str]:
        return extract_python_script_commands(
            self.run_commands(job_name),
            source=VERIFY_YML,
            include_args=include_args,
        )


def _normalize_path(raw: str) -> str:
    value = raw.strip()
    if value.startswith("- "):
        value = value[2:].strip()
    if (value.startswith("'") and value.endswith("'")) or (
        value.startswith('"') and value.endswith('"')
    ):
        value = value[1:-1]
    return value


def _extract_list_block(text: str, pattern: str, label: str) -> list[str]:
    match = re.search(pattern, text, re.MULTILINE)
    if not match:
        raise ValueError(f"Could not locate {label} in {VERIFY_YML}")
    block = match.group("block")
    entries = [_normalize_path(line) for line in block.splitlines() if line.strip()]
    if not entries:
        raise ValueError(f"{label} is empty in {VERIFY_YML}")
    return entries


def _extract_push_paths(text: str) -> list[str]:
    return _extract_list_block(
        text,
        r"^  push:\n(?:^    .*\n)*?^    paths:\n(?P<block>(?:^      - .*\n)+)",
        "on.push.paths",
    )


def _extract_pr_paths(text: str) -> list[str]:
    return _extract_list_block(
        text,
        r"^  pull_request:\n(?:^    .*\n)*?^    paths:\n(?P<block>(?:^      - .*\n)+)",
        "on.pull_request.paths",
    )


def _extract_changes_filter_paths(text: str) -> list[str]:
    changes_body = extract_job_body(text, "changes", VERIFY_YML)
    return _extract_list_block(
        changes_body,
        r"^\s*filters:\s*\|\n(?:^\s+.*\n)*?^\s*code:\n(?P<block>(?:^\s*-\s+.*\n)+)",
        "changes.filter.code",
    )


def _compare_lists(name_a: str, a: list[str], name_b: str, b: list[str]) -> list[str]:
    if a == b:
        return []
    errors = [f"{name_a} does not match {name_b}."]
    max_len = max(len(a), len(b))
    for i in range(max_len):
        va = a[i] if i < len(a) else "<missing>"
        vb = b[i] if i < len(b) else "<missing>"
        if va != vb:
            errors.append(f"  idx {i}: {name_a}={va!r}, {name_b}={vb!r}")
    return errors


def _duplicates(values: list[str]) -> list[str]:
    seen: set[str] = set()
    dup: list[str] = []
    for value in values:
        if value in seen and value not in dup:
            dup.append(value)
        seen.add(value)
    return dup


def _extract_verify_shard_indices(foundry_body: str) -> list[int]:
    m = re.search(r"^\s*shard_index:\s*\[(?P<csv>[^\]]+)\]\s*$", foundry_body, flags=re.MULTILINE)
    if not m:
        raise ValueError(f"Could not locate foundry matrix shard_index list in {VERIFY_YML}")
    return parse_csv_ints(m.group("csv"), VERIFY_YML)


def _extract_seed_matrix(foundry_multiseed_body: str) -> list[int]:
    m = re.search(r"^\s*seed:\s*\[(?P<csv>[^\]]+)\]\s*$", foundry_multiseed_body, flags=re.MULTILINE)
    if not m:
        raise ValueError(f"Could not locate foundry-multi-seed matrix seed list in {VERIFY_YML}")
    return parse_csv_ints(m.group("csv"), VERIFY_YML)


def _extract_script_seeds(text: str) -> list[int]:
    m = re.search(r"^DEFAULT_SEEDS=\((?P<vals>[^)]+)\)\s*$", text, re.MULTILINE)
    if not m:
        raise ValueError(f"Could not locate DEFAULT_SEEDS in {MULTISEED_SCRIPT}")
    raw_tokens = m.group("vals").split()
    if not raw_tokens:
        raise ValueError(f"DEFAULT_SEEDS is empty in {MULTISEED_SCRIPT}")
    try:
        return [int(token) for token in raw_tokens]
    except ValueError as exc:
        raise ValueError(f"Non-integer DEFAULT_SEEDS value in {MULTISEED_SCRIPT}") from exc


def _extract_forge_tokens(job_body: str, job_name: str) -> list[str]:
    run_commands = extract_run_commands_from_job_body(job_body, source=VERIFY_YML, context=job_name)
    forge_lines = [
        cmd for cmd in run_commands if match_shell_command(cmd, program="forge", args_prefix=("test",))[0]
    ]
    if not forge_lines:
        raise ValueError(f"Could not locate forge test command in {job_name} job in {VERIFY_YML}")
    if len(forge_lines) > 1:
        raise ValueError(f"Multiple forge test commands in {job_name} job in {VERIFY_YML}")
    matched, tokens = match_shell_command(forge_lines[0], program="forge", args_prefix=("test",))
    if not matched:
        raise ValueError(f"Could not parse forge test command in {job_name} job in {VERIFY_YML}")
    return tokens


def _extract_no_match_target(tokens: list[str]) -> str | None:
    if "--no-match-test" not in tokens:
        return None
    idx = tokens.index("--no-match-test")
    if idx + 1 >= len(tokens):
        return None
    target = tokens[idx + 1]
    if target.startswith("-"):
        return None
    return target


def _iter_step_blocks(job_body: str) -> list[str]:
    lines = job_body.splitlines()
    blocks: list[str] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if not re.match(r"^\s*-\s+\S", line):
            i += 1
            continue
        step_indent = len(line) - len(line.lstrip(" "))
        j = i + 1
        block_lines: list[str] = [line]
        while j < len(lines):
            child = lines[j]
            if child.strip() == "":
                block_lines.append(child)
                j += 1
                continue
            child_indent = len(child) - len(child.lstrip(" "))
            if child_indent <= step_indent:
                break
            block_lines.append(child)
            j += 1
        blocks.append("\n".join(block_lines))
        i = j
    return blocks


def _step_uses_action(step_block: str, action: str) -> bool:
    lines = step_block.splitlines()
    if not lines:
        return False
    step_indent = len(lines[0]) - len(lines[0].lstrip(" "))

    uses_value: str | None = None
    first = re.match(r"^\s*-\s+uses:\s*(?P<value>.+?)\s*$", lines[0])
    if first:
        uses_value = first.group("value")
    else:
        min_child_indent: int | None = None
        for line in lines[1:]:
            if not line.strip():
                continue
            child_indent = len(line) - len(line.lstrip(" "))
            if child_indent <= step_indent:
                continue
            if min_child_indent is None or child_indent < min_child_indent:
                min_child_indent = child_indent
        if min_child_indent is not None:
            for line in lines[1:]:
                if not line.strip():
                    continue
                child_indent = len(line) - len(line.lstrip(" "))
                if child_indent != min_child_indent:
                    continue
                m = re.match(r"^\s*uses:\s*(?P<value>.+?)\s*$", line)
                if m:
                    uses_value = m.group("value")
                    break

    if uses_value is None:
        return False
    uses_clean = unquote_yaml_scalar(strip_yaml_inline_comment(uses_value))
    return bool(re.fullmatch(rf"actions/{re.escape(action)}@v\d+", uses_clean))


def _extract_artifact_names(job_body: str, *, action: str) -> list[str]:
    names: list[str] = []
    for block in _iter_step_blocks(job_body):
        if not _step_uses_action(block, action):
            continue
        name = _extract_name_from_with_block(block)
        if name is None:
            raise ValueError(f"Found {action} step without literal with.name")
        names.append(name)
    return names


def _extract_name_from_with_block(step_block: str) -> str | None:
    lines = step_block.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^(?P<indent>\s*)with:\s*(?:#.*)?$", line)
        if not m:
            i += 1
            continue
        with_indent = len(m.group("indent"))
        j = i + 1
        block_lines: list[str] = []
        while j < len(lines):
            child = lines[j]
            if child.strip() == "":
                block_lines.append(child)
                j += 1
                continue
            child_indent = len(child) - len(child.lstrip(" "))
            if child_indent <= with_indent:
                break
            block_lines.append(child)
            j += 1
        min_child_indent: int | None = None
        for child in block_lines:
            if not child.strip():
                continue
            child_indent = len(child) - len(child.lstrip(" "))
            if min_child_indent is None or child_indent < min_child_indent:
                min_child_indent = child_indent
        if min_child_indent is None:
            i = j
            continue
        for child in block_lines:
            if not child.strip():
                continue
            child_indent = len(child) - len(child.lstrip(" "))
            if child_indent != min_child_indent:
                continue
            km = re.match(r"^\s*name:\s*(?P<value>.+?)\s*$", child)
            if not km:
                continue
            raw = strip_yaml_inline_comment(km.group("value"))
            if raw:
                return unquote_yaml_scalar(raw)
        i = j
    return None


def _load_spec() -> dict:
    return json.loads(SPEC_PATH.read_text(encoding="utf-8"))


def check_paths(snapshot: Snapshot, spec: dict) -> CheckResult:
    errors: list[str] = []
    push_paths = _extract_push_paths(snapshot.workflow_text)
    pr_paths = _extract_pr_paths(snapshot.workflow_text)
    changes_paths = _extract_changes_filter_paths(snapshot.workflow_text)

    for label, values in [
        ("on.push.paths", push_paths),
        ("on.pull_request.paths", pr_paths),
        ("changes.filter.code", changes_paths),
    ]:
        dup = _duplicates(values)
        if dup:
            errors.append(f"{label} has duplicates: {', '.join(dup)}")

    errors.extend(_compare_lists("on.push.paths", push_paths, "on.pull_request.paths", pr_paths))

    check_only = spec["check_only_paths"]
    missing_check_only = sorted(set(check_only) - set(push_paths))
    if missing_check_only:
        errors.append("check_only_paths includes entries missing from on.push.paths: " + ", ".join(missing_check_only))

    expected_changes = [p for p in push_paths if p not in set(check_only)]
    errors.extend(_compare_lists("changes.filter.code", changes_paths, "expected push minus check_only", expected_changes))

    return CheckResult("paths", errors)


def check_jobs(snapshot: Snapshot, spec: dict) -> CheckResult:
    return CheckResult(
        "jobs",
        _compare_lists("workflow jobs", snapshot.jobs, "spec jobs", spec["expected_jobs"]),
    )


def check_python_commands(snapshot: Snapshot, spec: dict) -> CheckResult:
    errors: list[str] = []
    errors.extend(
        _compare_lists(
            "checks python scripts",
            snapshot.python_commands("checks", include_args=True),
            "spec checks scripts",
            spec["expected_checks_commands"],
        )
    )
    errors.extend(
        _compare_lists(
            "build python scripts",
            snapshot.python_commands("build", include_args=True),
            "spec build scripts",
            spec["expected_build_commands"],
        )
    )
    errors.extend(
        _compare_lists(
            "build-compiler python scripts",
            snapshot.python_commands("build-compiler", include_args=True),
            "spec build-compiler scripts",
            spec["expected_build_compiler_commands"],
        )
    )
    return CheckResult("python-commands", errors)


def check_multiseed(snapshot: Snapshot, spec: dict) -> CheckResult:
    errors: list[str] = []
    workflow_seeds = _extract_seed_matrix(snapshot.job_body("foundry-multi-seed"))
    script_seeds = _extract_script_seeds(MULTISEED_SCRIPT.read_text(encoding="utf-8"))
    spec_seeds = spec["expected_foundry_multi_seed"]["seeds"]

    errors.extend(_compare_lists("workflow multi-seed", [str(x) for x in workflow_seeds], "script multi-seed", [str(x) for x in script_seeds]))
    errors.extend(_compare_lists("workflow multi-seed", [str(x) for x in workflow_seeds], "spec multi-seed", [str(x) for x in spec_seeds]))
    return CheckResult("multiseed", errors)


def check_foundry(snapshot: Snapshot, spec: dict) -> CheckResult:
    errors: list[str] = []
    foundry_body = snapshot.job_body("foundry")
    patched_body = snapshot.job_body("foundry-patched")
    multiseed_body = snapshot.job_body("foundry-multi-seed")
    foundry_gas_body = snapshot.job_body("foundry-gas-calibration")

    # foundry shard + seed
    shard_indices = _extract_verify_shard_indices(foundry_body)
    shard_count = int(
        extract_literal_from_mapping_blocks(foundry_body, "env", "DIFFTEST_SHARD_COUNT", source=VERIFY_YML, context="foundry")
    )
    seed = int(
        extract_literal_from_mapping_blocks(foundry_body, "env", "DIFFTEST_RANDOM_SEED", source=VERIFY_YML, context="foundry")
    )
    expected_indices = list(range(len(shard_indices)))
    if shard_indices != expected_indices:
        errors.append(f"foundry shard_index must be contiguous 0..N-1, got {shard_indices}")
    if shard_count != len(shard_indices):
        errors.append(f"foundry DIFFTEST_SHARD_COUNT={shard_count} but matrix size={len(shard_indices)}")

    expected_foundry = spec["expected_foundry"]
    if len(shard_indices) != int(expected_foundry["shards"]):
        errors.append(
            f"foundry shard count {len(shard_indices)} does not match spec {expected_foundry['shards']}"
        )
    if seed != int(expected_foundry["seed"]):
        errors.append(f"foundry seed {seed} does not match spec {expected_foundry['seed']}")

    # shared env invariants across foundry jobs
    def env(job_body: str, key: str, ctx: str) -> str:
        return extract_literal_from_mapping_blocks(job_body, "env", key, source=VERIFY_YML, context=ctx)

    profiles = {
        env(foundry_body, "FOUNDRY_PROFILE", "foundry"),
        env(patched_body, "FOUNDRY_PROFILE", "foundry-patched"),
        env(multiseed_body, "FOUNDRY_PROFILE", "foundry-multi-seed"),
    }
    if profiles != {"difftest"}:
        errors.append(f"FOUNDRY_PROFILE must be difftest across foundry jobs, got {sorted(profiles)}")

    for key in ["DIFFTEST_RANDOM_SMALL", "DIFFTEST_RANDOM_LARGE"]:
        values = {
            env(foundry_body, key, "foundry"),
            env(patched_body, key, "foundry-patched"),
            env(multiseed_body, key, "foundry-multi-seed"),
        }
        if len(values) != 1:
            errors.append(f"{key} must match across foundry jobs, got {sorted(values)}")

    foundry_cmd = _extract_forge_tokens(foundry_body, "foundry")
    patched_cmd = _extract_forge_tokens(patched_body, "foundry-patched")
    multiseed_cmd = _extract_forge_tokens(multiseed_body, "foundry-multi-seed")

    if _extract_no_match_target(foundry_cmd) is not None:
        errors.append("foundry job must not use --no-match-test")
    patched_target = _extract_no_match_target(patched_cmd)
    if patched_target != spec["expected_foundry_patched"]["no_match_test"]:
        errors.append(
            "foundry-patched --no-match-test target mismatch: "
            f"workflow={patched_target!r}, spec={spec['expected_foundry_patched']['no_match_test']!r}"
        )
    if _extract_no_match_target(multiseed_cmd) is not None:
        errors.append("foundry-multi-seed must not use --no-match-test")

    patched_expected = spec["expected_foundry_patched"]
    for key, expected in [
        ("DIFFTEST_RANDOM_SEED", str(patched_expected["seed"])),
        ("DIFFTEST_SHARD_COUNT", str(patched_expected["shard_count"])),
        ("DIFFTEST_SHARD_INDEX", str(patched_expected["shard_index"])),
    ]:
        got = env(patched_body, key, "foundry-patched")
        if got != expected:
            errors.append(f"foundry-patched {key}={got} does not match spec {expected}")

    # gas-calibration invariants
    gas_expected = spec["expected_foundry_gas_calibration"]
    gas_profile = env(foundry_gas_body, "FOUNDRY_PROFILE", "foundry-gas-calibration")
    if gas_profile != gas_expected["profile"]:
        errors.append(
            f"foundry-gas-calibration FOUNDRY_PROFILE={gas_profile} does not match spec {gas_expected['profile']}"
        )
    # Ensure command exists in run commands
    gas_run = "\n".join(snapshot.run_commands("foundry-gas-calibration"))
    if gas_expected["command"] not in gas_run:
        errors.append(
            f"foundry-gas-calibration command missing: {gas_expected['command']}"
        )
    if gas_expected["artifact"] not in foundry_gas_body:
        errors.append(
            f"foundry-gas-calibration artifact name missing: {gas_expected['artifact']}"
        )

    return CheckResult("foundry", errors)


def check_artifacts(snapshot: Snapshot, spec: dict) -> CheckResult:
    errors: list[str] = []
    producer_jobs = spec["artifact_producer_jobs"]

    upload_names: list[str] = []
    for job in producer_jobs:
        if job not in snapshot.jobs:
            errors.append(f"producer job missing from workflow: {job}")
            continue
        upload_names.extend(_extract_artifact_names(snapshot.job_body(job), action="upload-artifact"))

    if not upload_names:
        errors.append("no upload-artifact names found in producer jobs")
        return CheckResult("artifacts", errors)

    dup_upload = sorted([name for name, count in Counter(upload_names).items() if count > 1])
    if dup_upload:
        errors.append("duplicate upload artifacts across producer jobs: " + ", ".join(dup_upload))

    uploaded = set(upload_names)
    for job in snapshot.jobs:
        if job in producer_jobs:
            continue
        names = _extract_artifact_names(snapshot.job_body(job), action="download-artifact")
        if len(names) != len(set(names)):
            errors.append(f"duplicate download artifact names in {job}: {names}")
        for name in names:
            if name not in uploaded:
                errors.append(f"{job} downloads unknown artifact: {name}")

    return CheckResult("artifacts", errors)


def _extract_makefile_check_scripts() -> list[str]:
    """Extract python3 scripts/... commands from the Makefile 'check' target."""
    text = MAKEFILE.read_text(encoding="utf-8")
    in_check = False
    scripts: list[str] = []
    for line in text.splitlines():
        if re.match(r"^check:", line):
            in_check = True
            continue
        if in_check:
            if line and not line[0].isspace():
                break
            m = re.search(r"python3 scripts/(\S+(?:\s+\S+)*)", line)
            if m:
                scripts.append(m.group(1))
    return scripts


def check_makefile(_snapshot: Snapshot, spec: dict) -> CheckResult:
    errors: list[str] = []
    makefile_scripts = _extract_makefile_check_scripts()
    expected = spec["expected_checks_commands"]
    errors.extend(
        _compare_lists(
            "Makefile check scripts",
            makefile_scripts,
            "spec checks scripts",
            expected,
        )
    )
    return CheckResult("makefile", errors)


def _checks() -> dict[str, callable]:
    return {
        "paths": check_paths,
        "jobs": check_jobs,
        "python-commands": check_python_commands,
        "multiseed": check_multiseed,
        "foundry": check_foundry,
        "artifacts": check_artifacts,
        "makefile": check_makefile,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Unified verify sync validator")
    parser.add_argument(
        "--only",
        action="append",
        choices=sorted(_checks().keys()),
        help="Run only the selected invariant(s). Can be repeated.",
    )
    parser.add_argument("--list", action="store_true", help="List available invariants")
    args = parser.parse_args()

    checks = _checks()
    if args.list:
        for name in checks:
            print(name)
        return 0

    selected = args.only if args.only else list(checks.keys())
    spec = _load_spec()
    snapshot = Snapshot.load()

    failures = 0
    for name in selected:
        result = checks[name](snapshot, spec)
        if result.errors:
            failures += 1
            print(f"[FAIL] {name}", file=sys.stderr)
            for err in result.errors:
                print(f"  - {err}", file=sys.stderr)
        else:
            print(f"[PASS] {name}")

    if failures:
        print(f"verify sync failed: {failures}/{len(selected)} invariant groups failed", file=sys.stderr)
        return 1

    print(f"verify sync passed: {len(selected)} invariant groups")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
