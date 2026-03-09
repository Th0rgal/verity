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


def _extract_push_branches(text: str) -> list[str]:
    push_match = re.search(r"^  push:\n(?P<body>(?:^    .*\n)*)", text, re.MULTILINE)
    if not push_match:
        raise ValueError(f"Could not locate on.push in {VERIFY_YML}")

    push_body = push_match.group("body")
    inline_match = re.search(r"^    branches:\s*(?P<value>\[.*\])\s*$", push_body, re.MULTILINE)
    if inline_match:
        raw = strip_yaml_inline_comment(inline_match.group("value"))
        inner = raw[1:-1].strip()
        if not inner:
            raise ValueError(f"on.push.branches is empty in {VERIFY_YML}")
        return [unquote_yaml_scalar(part.strip()) for part in inner.split(",")]

    return _extract_list_block(
        text,
        r"^  push:\n(?:^    .*\n)*?^    branches:\n(?P<block>(?:^      - .*\n)+)",
        "on.push.branches",
    )


def _extract_trigger_keys(text: str) -> list[str]:
    on_match = re.search(r"^on:\n(?P<body>(?:^  .*\n)*)", text, re.MULTILINE)
    if not on_match:
        raise ValueError(f"Could not locate on in {VERIFY_YML}")

    trigger_keys: list[str] = []
    for line in on_match.group("body").splitlines():
        if not line.strip():
            continue
        if len(line) - len(line.lstrip(" ")) != 2:
            continue
        match = re.match(r"^\s{2}(?P<key>[A-Za-z0-9_-]+):(?:\s|$)", line)
        if match:
            trigger_keys.append(match.group("key"))
    if not trigger_keys:
        raise ValueError(f"No workflow triggers found under on in {VERIFY_YML}")
    return trigger_keys


def _extract_pr_paths(text: str) -> list[str]:
    return _extract_list_block(
        text,
        r"^  pull_request:\n(?:^    .*\n)*?^    paths:\n(?P<block>(?:^      - .*\n)+)",
        "on.pull_request.paths",
    )


def _extract_changes_filter_paths(text: str, filter_name: str) -> list[str]:
    changes_body = extract_job_body(text, "changes", VERIFY_YML)
    return _extract_list_block(
        changes_body,
        rf"^\s*filters:\s*\|\n(?:^\s+.*\n)*?^\s*{re.escape(filter_name)}:\n(?P<block>(?:^\s*-\s+.*\n)+)",
        f"changes.filter.{filter_name}",
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


def _iter_top_level_job_entries(job_body: str) -> list[tuple[str, str]]:
    lines = job_body.splitlines()
    min_child_indent: int | None = None
    for line in lines:
        if not line.strip():
            continue
        child_indent = len(line) - len(line.lstrip(" "))
        if min_child_indent is None or child_indent < min_child_indent:
            min_child_indent = child_indent
    if min_child_indent is None:
        return []

    entries: list[tuple[str, str]] = []
    for line in lines:
        if not line.strip():
            continue
        child_indent = len(line) - len(line.lstrip(" "))
        if child_indent != min_child_indent:
            continue
        m = re.match(r"^\s*(?P<key>[A-Za-z0-9_-]+):\s*(?P<value>.*?)\s*$", line)
        if not m:
            continue
        entries.append(
            (
                m.group("key"),
                unquote_yaml_scalar(strip_yaml_inline_comment(m.group("value"))),
            )
        )
    return entries


def _extract_top_level_job_value(job_body: str, key: str) -> str | None:
    for entry_key, value in _iter_top_level_job_entries(job_body):
        if entry_key == key:
            return value
    return None


def _extract_top_level_step_value(step_block: str, key: str) -> str | None:
    lines = step_block.splitlines()
    if not lines:
        return None

    first = re.match(rf"^\s*-\s*{re.escape(key)}:\s*(?P<value>.*?)\s*$", lines[0])
    if first:
        raw = strip_yaml_inline_comment(first.group("value"))
        return unquote_yaml_scalar(raw) if raw else ""

    step_indent = len(lines[0]) - len(lines[0].lstrip(" "))
    min_child_indent: int | None = None
    for line in lines[1:]:
        if not line.strip():
            continue
        child_indent = len(line) - len(line.lstrip(" "))
        if child_indent <= step_indent:
            continue
        if min_child_indent is None or child_indent < min_child_indent:
            min_child_indent = child_indent
    if min_child_indent is None:
        return None

    for line in lines[1:]:
        if not line.strip():
            continue
        child_indent = len(line) - len(line.lstrip(" "))
        if child_indent != min_child_indent:
            continue
        m = re.match(rf"^\s*{re.escape(key)}:\s*(?P<value>.*?)\s*$", line)
        if not m:
            continue
        raw = strip_yaml_inline_comment(m.group("value"))
        return unquote_yaml_scalar(raw) if raw else ""
    return None


def _extract_top_level_step_block_lines(step_block: str, key: str) -> list[str]:
    lines = step_block.splitlines()
    if not lines:
        return []

    step_indent = len(lines[0]) - len(lines[0].lstrip(" "))
    min_child_indent: int | None = None
    for line in lines[1:]:
        if not line.strip():
            continue
        child_indent = len(line) - len(line.lstrip(" "))
        if child_indent <= step_indent:
            continue
        if min_child_indent is None or child_indent < min_child_indent:
            min_child_indent = child_indent
    if min_child_indent is None:
        return []

    for idx, line in enumerate(lines[1:], start=1):
        if not line.strip():
            continue
        child_indent = len(line) - len(line.lstrip(" "))
        if child_indent != min_child_indent:
            continue
        m = re.match(rf"^\s*{re.escape(key)}:\s*(?P<value>.*?)\s*$", line)
        if not m or strip_yaml_inline_comment(m.group("value")):
            continue

        block_lines: list[str] = []
        for nested in lines[idx + 1 :]:
            if not nested.strip():
                block_lines.append("")
                continue
            nested_indent = len(nested) - len(nested.lstrip(" "))
            if nested_indent <= child_indent:
                break
            block_lines.append(nested)
        return block_lines

    return []


def _decode_step_block_scalar(raw_value: str, block_lines: list[str], start_idx: int, child_indent: int) -> str:
    nested_lines: list[str] = []
    nested_indent: int | None = None
    for nested in block_lines[start_idx + 1 :]:
        if not nested.strip():
            nested_lines.append("")
            continue
        current_indent = len(nested) - len(nested.lstrip(" "))
        if current_indent <= child_indent:
            break
        if nested_indent is None or current_indent < nested_indent:
            nested_indent = current_indent
        nested_lines.append(nested)
    if nested_indent is None:
        raise ValueError(f"Empty step block scalar in {VERIFY_YML}")

    normalized_lines = [
        nested[nested_indent:] if nested.strip() else ""
        for nested in nested_lines
    ]
    while normalized_lines and normalized_lines[-1] == "":
        normalized_lines.pop()

    style = raw_value[0]
    if style == "|":
        return "\n".join(normalized_lines)

    if style != ">":
        raise ValueError(f"Unsupported step block scalar style {raw_value!r} in {VERIFY_YML}")

    folded_parts: list[str] = []
    for line in normalized_lines:
        if not line:
            folded_parts.append("\n")
            continue
        if not folded_parts:
            folded_parts.append(line)
            continue
        if folded_parts[-1].endswith("\n"):
            folded_parts.append(line)
            continue
        folded_parts.append(f" {line}")
    return "".join(folded_parts)


def _extract_literal_top_level_mapping(body: str, key: str) -> dict[str, str]:
    block_lines = _extract_top_level_job_block_lines(body, key)
    if not block_lines:
        return {}

    min_child_indent: int | None = None
    for line in block_lines:
        if not line.strip():
            continue
        child_indent = len(line) - len(line.lstrip(" "))
        if min_child_indent is None or child_indent < min_child_indent:
            min_child_indent = child_indent
    if min_child_indent is None:
        return {}

    values: dict[str, str] = {}
    for line in block_lines:
        if not line.strip():
            continue
        child_indent = len(line) - len(line.lstrip(" "))
        if child_indent != min_child_indent:
            continue
        m = re.match(r"^\s*(?P<entry_key>[A-Za-z0-9_-]+):\s*(?P<value>.+?)\s*$", line)
        if not m:
            raise ValueError(f"Unsupported literal mapping entry in {key} block in {VERIFY_YML}")
        entry_key = m.group("entry_key")
        raw_value = strip_yaml_inline_comment(m.group("value"))
        if not raw_value:
            raise ValueError(f"Empty {key}.{entry_key} value in {VERIFY_YML}")
        value = unquote_yaml_scalar(raw_value)
        previous = values.get(entry_key)
        if previous is not None and previous != value:
            raise ValueError(
                f"Conflicting {key}.{entry_key} values in {VERIFY_YML}: {previous!r} vs {value!r}"
            )
        values[entry_key] = value
    return values


def _extract_literal_step_mapping(step_block: str, key: str) -> dict[str, str]:
    block_lines = _extract_top_level_step_block_lines(step_block, key)
    if not block_lines:
        return {}

    min_child_indent: int | None = None
    for line in block_lines:
        if not line.strip():
            continue
        child_indent = len(line) - len(line.lstrip(" "))
        if min_child_indent is None or child_indent < min_child_indent:
            min_child_indent = child_indent
    if min_child_indent is None:
        return {}

    values: dict[str, str] = {}
    for idx, line in enumerate(block_lines):
        if not line.strip():
            continue
        child_indent = len(line) - len(line.lstrip(" "))
        if child_indent != min_child_indent:
            continue
        m = re.match(r"^\s*(?P<entry_key>[A-Za-z0-9_-]+):\s*(?P<value>.+?)\s*$", line)
        if not m:
            raise ValueError(f"Unsupported literal mapping entry in step {key} block in {VERIFY_YML}")
        entry_key = m.group("entry_key")
        raw_value = strip_yaml_inline_comment(m.group("value"))
        if not raw_value:
            raise ValueError(f"Empty step {key}.{entry_key} value in {VERIFY_YML}")
        if raw_value in {"|", "|-", "|+", ">", ">-", ">+"}:
            value = _decode_step_block_scalar(raw_value, block_lines, idx, child_indent)
        else:
            value = unquote_yaml_scalar(raw_value)
        previous = values.get(entry_key)
        if previous is not None and previous != value:
            raise ValueError(
                f"Conflicting step {key}.{entry_key} values in {VERIFY_YML}: {previous!r} vs {value!r}"
            )
        values[entry_key] = value
    return values


def _extract_top_level_job_block_lines(job_body: str, key: str) -> list[str]:
    lines = job_body.splitlines()
    min_child_indent: int | None = None
    for line in lines:
        if not line.strip():
            continue
        child_indent = len(line) - len(line.lstrip(" "))
        if min_child_indent is None or child_indent < min_child_indent:
            min_child_indent = child_indent
    if min_child_indent is None:
        return []

    for idx, line in enumerate(lines):
        if not line.strip():
            continue
        child_indent = len(line) - len(line.lstrip(" "))
        if child_indent != min_child_indent:
            continue
        m = re.match(rf"^\s*{re.escape(key)}:\s*(?P<value>.*?)\s*$", line)
        if not m or strip_yaml_inline_comment(m.group("value")):
            continue

        block_lines: list[str] = []
        for nested in lines[idx + 1 :]:
            if not nested.strip():
                block_lines.append("")
                continue
            nested_indent = len(nested) - len(nested.lstrip(" "))
            if nested_indent <= child_indent:
                break
            block_lines.append(nested)
        return block_lines

    return []


def _extract_job_needs(job_body: str) -> list[str]:
    raw = _extract_top_level_job_value(job_body, "needs")
    if raw is None:
        return []
    if raw.startswith("[") and raw.endswith("]"):
        inner = raw[1:-1].strip()
        if not inner:
            return []
        return [unquote_yaml_scalar(part.strip()) for part in inner.split(",")]
    if not raw:
        block_lines = _extract_top_level_job_block_lines(job_body, "needs")
        if not block_lines:
            return []
        entries: list[str] = []
        for line in block_lines:
            if not line.strip():
                continue
            m = re.match(r"^\s*-\s*(?P<value>.*?)\s*$", line)
            if not m:
                raise ValueError(f"Unsupported non-list needs entry in {VERIFY_YML}")
            value = unquote_yaml_scalar(strip_yaml_inline_comment(m.group("value")))
            if not value:
                raise ValueError(f"Empty needs entry in {VERIFY_YML}")
            entries.append(value)
        return entries
    return [raw]


def _extract_job_strategy_fail_fast(job_body: str) -> str | None:
    block_lines = _extract_top_level_job_block_lines(job_body, "strategy")
    if not block_lines:
        return None

    min_child_indent: int | None = None
    for line in block_lines:
        if not line.strip():
            continue
        child_indent = len(line) - len(line.lstrip(" "))
        if min_child_indent is None or child_indent < min_child_indent:
            min_child_indent = child_indent
    if min_child_indent is None:
        return None

    for line in block_lines:
        if not line.strip():
            continue
        child_indent = len(line) - len(line.lstrip(" "))
        if child_indent != min_child_indent:
            continue
        m = re.match(r"^\s*fail-fast:\s*(?P<value>.+?)\s*$", line)
        if not m:
            continue
        raw_value = strip_yaml_inline_comment(m.group("value"))
        if not raw_value:
            raise ValueError(f"Empty strategy.fail-fast value in {VERIFY_YML}")
        return unquote_yaml_scalar(raw_value)

    return None


def _compare_mappings(
    name_a: str, a: dict[str, str], name_b: str, b: dict[str, str]
) -> list[str]:
    if a == b:
        return []
    errors = [f"{name_a} does not match {name_b}."]
    for key in sorted(set(a) | set(b)):
        va = a.get(key, "<missing>")
        vb = b.get(key, "<missing>")
        if va != vb:
            errors.append(f"  {key}: {name_a}={va!r}, {name_b}={vb!r}")
    return errors


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


def _extract_artifact_paths(job_body: str, *, action: str) -> list[str | None]:
    paths: list[str | None] = []
    for block in _iter_step_blocks(job_body):
        if not _step_uses_action(block, action):
            continue
        paths.append(_extract_with_key_from_block(block, "path"))
    return paths


def _extract_name_from_with_block(step_block: str) -> str | None:
    value = _extract_with_key_from_block(step_block, "name")
    if value == "":
        return None
    return value


def _extract_with_key_from_block(step_block: str, key: str) -> str | None:
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
        for child_idx, child in enumerate(block_lines):
            if not child.strip():
                continue
            child_indent = len(child) - len(child.lstrip(" "))
            if child_indent != min_child_indent:
                continue
            km = re.match(rf"^\s*{re.escape(key)}:\s*(?P<value>.*?)\s*$", child)
            if not km:
                continue
            raw = strip_yaml_inline_comment(km.group("value"))
            if raw in {"|", "|-", "|+", ">", ">-", ">+"}:
                nested_lines: list[str] = []
                nested_indent: int | None = None
                for nested in block_lines[child_idx + 1 :]:
                    if not nested.strip():
                        nested_lines.append("")
                        continue
                    current_indent = len(nested) - len(nested.lstrip(" "))
                    if current_indent <= child_indent:
                        break
                    if nested_indent is None or current_indent < nested_indent:
                        nested_indent = current_indent
                    nested_lines.append(nested)
                if nested_indent is None:
                    return ""
                normalized_lines = [
                    nested[nested_indent:] if nested.strip() else ""
                    for nested in nested_lines
                ]
                while normalized_lines and normalized_lines[-1] == "":
                    normalized_lines.pop()
                return "\n".join(normalized_lines)
            if raw:
                return unquote_yaml_scalar(raw)
            return ""
        i = j
    return None


def _load_spec() -> dict:
    return json.loads(SPEC_PATH.read_text(encoding="utf-8"))


def check_paths(snapshot: Snapshot, spec: dict) -> CheckResult:
    errors: list[str] = []
    trigger_keys = _extract_trigger_keys(snapshot.workflow_text)
    push_paths = _extract_push_paths(snapshot.workflow_text)
    pr_paths = _extract_pr_paths(snapshot.workflow_text)
    changes_paths = _extract_changes_filter_paths(snapshot.workflow_text, "code")
    compiler_changes_paths = _extract_changes_filter_paths(snapshot.workflow_text, "compiler")
    expected_trigger_keys = spec.get("expected_trigger_keys", [])
    expected_push_branches = spec.get("expected_push_branches", [])
    require_workflow_dispatch = spec.get("require_workflow_dispatch", False)

    list_blocks = [
        ("on.push.paths", push_paths),
        ("on.pull_request.paths", pr_paths),
        ("changes.filter.code", changes_paths),
        ("changes.filter.compiler", compiler_changes_paths),
    ]
    push_branches: list[str] = []
    if expected_push_branches:
        push_branches = _extract_push_branches(snapshot.workflow_text)
        list_blocks.insert(0, ("on.push.branches", push_branches))

    for label, values in list_blocks:
        dup = _duplicates(values)
        if dup:
            errors.append(f"{label} has duplicates: {', '.join(dup)}")

    if expected_trigger_keys:
        errors.extend(
            _compare_lists(
                "workflow triggers",
                trigger_keys,
                "spec workflow triggers",
                expected_trigger_keys,
            )
        )

    if expected_push_branches:
        errors.extend(
            _compare_lists(
                "on.push.branches",
                push_branches,
                "spec push branches",
                expected_push_branches,
            )
        )

    errors.extend(_compare_lists("on.push.paths", push_paths, "on.pull_request.paths", pr_paths))

    if require_workflow_dispatch and "\n  workflow_dispatch:\n" not in f"\n{snapshot.workflow_text}":
        errors.append("workflow_dispatch trigger is missing from verify.yml")

    check_only = spec["check_only_paths"]
    missing_check_only = sorted(set(check_only) - set(push_paths))
    if missing_check_only:
        errors.append("check_only_paths includes entries missing from on.push.paths: " + ", ".join(missing_check_only))

    expected_changes = [p for p in push_paths if p not in set(check_only)]
    errors.extend(_compare_lists("changes.filter.code", changes_paths, "expected push minus check_only", expected_changes))
    errors.extend(
        _compare_lists(
            "changes.filter.compiler",
            compiler_changes_paths,
            "spec compiler paths",
            spec["compiler_paths"],
        )
    )

    return CheckResult("paths", errors)


def check_jobs(snapshot: Snapshot, spec: dict) -> CheckResult:
    return CheckResult(
        "jobs",
        _compare_lists("workflow jobs", snapshot.jobs, "spec jobs", spec["expected_jobs"]),
    )


def check_job_contracts(snapshot: Snapshot, spec: dict) -> CheckResult:
    errors: list[str] = []
    expected_needs: dict[str, list[str]] = spec.get("expected_job_needs", {})
    expected_conditions: dict[str, str] = spec.get("expected_job_if_conditions", {})
    expected_runs_on: dict[str, str] = spec.get("expected_job_runs_on", {})
    expected_timeouts: dict[str, int] = spec.get("expected_job_timeouts", {})
    expected_fail_fast: dict[str, bool] = spec.get("expected_job_strategy_fail_fast", {})
    expected_outputs: dict[str, dict[str, str]] = spec.get("expected_job_outputs", {})
    expected_job_permissions: dict[str, dict[str, str]] = spec.get(
        "expected_job_permissions", {}
    )
    expected_workflow_permissions: dict[str, str] = spec.get(
        "expected_workflow_permissions", {}
    )
    expected_workflow_concurrency: dict[str, str] = spec.get(
        "expected_workflow_concurrency", {}
    )
    expected_workflow_env: dict[str, str] = spec.get("expected_workflow_env", {})

    actual_workflow_permissions = _extract_literal_top_level_mapping(
        snapshot.workflow_text, "permissions"
    )
    errors.extend(
        _compare_mappings(
            "workflow permissions",
            actual_workflow_permissions,
            "spec workflow permissions",
            expected_workflow_permissions,
        )
    )

    actual_workflow_concurrency = _extract_literal_top_level_mapping(
        snapshot.workflow_text, "concurrency"
    )
    errors.extend(
        _compare_mappings(
            "workflow concurrency",
            actual_workflow_concurrency,
            "spec workflow concurrency",
            expected_workflow_concurrency,
        )
    )

    actual_workflow_env = _extract_literal_top_level_mapping(snapshot.workflow_text, "env")
    errors.extend(
        _compare_mappings(
            "workflow env",
            actual_workflow_env,
            "spec workflow env",
            expected_workflow_env,
        )
    )

    actual_output_jobs: dict[str, dict[str, str]] = {}
    actual_permission_jobs: dict[str, dict[str, str]] = {}

    for job in snapshot.jobs:
        job_body = snapshot.job_body(job)
        actual_needs = _extract_job_needs(job_body)
        expected_job_needs = expected_needs.get(job, [])
        errors.extend(
            _compare_lists(
                f"{job} needs",
                actual_needs,
                f"spec {job} needs",
                expected_job_needs,
            )
        )

        actual_condition = _extract_top_level_job_value(job_body, "if")
        expected_condition = expected_conditions.get(job)
        if actual_condition != expected_condition:
            errors.append(
                f"{job} if does not match spec: workflow={actual_condition!r}, spec={expected_condition!r}"
            )

        actual_runs_on = _extract_top_level_job_value(job_body, "runs-on")
        expected_job_runs_on = expected_runs_on.get(job)
        if actual_runs_on != expected_job_runs_on:
            errors.append(
                f"{job} runs-on does not match spec: workflow={actual_runs_on!r}, spec={expected_job_runs_on!r}"
            )

        actual_timeout = _extract_top_level_job_value(job_body, "timeout-minutes")
        expected_job_timeout = expected_timeouts.get(job)
        expected_timeout_value = None if expected_job_timeout is None else str(expected_job_timeout)
        if actual_timeout != expected_timeout_value:
            errors.append(
                f"{job} timeout-minutes does not match spec: workflow={actual_timeout!r}, spec={expected_timeout_value!r}"
            )

        expected_fail_fast_value = expected_fail_fast.get(job)
        if expected_fail_fast_value is not None:
            actual_fail_fast = _extract_job_strategy_fail_fast(job_body)
            expected_fail_fast_scalar = "true" if expected_fail_fast_value else "false"
            if actual_fail_fast != expected_fail_fast_scalar:
                errors.append(
                    f"{job} strategy.fail-fast does not match spec: "
                    f"workflow={actual_fail_fast!r}, spec={expected_fail_fast_scalar!r}"
                )

        outputs = _extract_literal_top_level_mapping(job_body, "outputs")
        if outputs:
            actual_output_jobs[job] = outputs

        permissions = _extract_literal_top_level_mapping(job_body, "permissions")
        if permissions:
            actual_permission_jobs[job] = permissions

    errors.extend(
        _compare_lists(
            "jobs with outputs",
            [job for job in snapshot.jobs if job in actual_output_jobs],
            "spec jobs with outputs",
            list(expected_outputs),
        )
    )
    for job, expected_mapping in expected_outputs.items():
        errors.extend(
            _compare_mappings(
                f"{job} outputs",
                actual_output_jobs.get(job, {}),
                f"spec {job} outputs",
                expected_mapping,
            )
        )

    errors.extend(
        _compare_lists(
            "jobs with permissions",
            [job for job in snapshot.jobs if job in actual_permission_jobs],
            "spec jobs with permissions",
            list(expected_job_permissions),
        )
    )
    for job, expected_mapping in expected_job_permissions.items():
        errors.extend(
            _compare_mappings(
                f"{job} permissions",
                actual_permission_jobs.get(job, {}),
                f"spec {job} permissions",
                expected_mapping,
            )
        )

    return CheckResult("job-contracts", errors)


def _describe_step_locator(step_spec: dict) -> str:
    parts: list[str] = []
    if "id" in step_spec:
        parts.append(f"id={step_spec['id']!r}")
    if "name" in step_spec:
        parts.append(f"name={step_spec['name']!r}")
    if "uses" in step_spec:
        parts.append(f"uses={step_spec['uses']!r}")
    return ", ".join(parts) if parts else "<unidentified step>"


def _find_matching_step(job_body: str, step_spec: dict) -> str | None:
    matches: list[str] = []
    for step_block in _iter_step_blocks(job_body):
        actual_id = _extract_top_level_step_value(step_block, "id")
        actual_name = _extract_top_level_step_value(step_block, "name")
        actual_uses = _extract_top_level_step_value(step_block, "uses")
        if "id" in step_spec and actual_id != step_spec["id"]:
            continue
        if "name" in step_spec and actual_name != step_spec["name"]:
            continue
        if "uses" in step_spec and actual_uses != step_spec["uses"]:
            continue
        matches.append(step_block)
    if not matches:
        return None
    if len(matches) > 1:
        raise ValueError(
            f"Multiple workflow steps matched locator {_describe_step_locator(step_spec)} in {VERIFY_YML}"
        )
    return matches[0]


def check_step_contracts(snapshot: Snapshot, spec: dict) -> CheckResult:
    errors: list[str] = []
    expected_step_contracts: dict[str, list[dict]] = spec.get("expected_step_contracts", {})

    for job, step_specs in expected_step_contracts.items():
        job_body = snapshot.job_body(job)
        for step_spec in step_specs:
            step_block = _find_matching_step(job_body, step_spec)
            locator = _describe_step_locator(step_spec)
            if step_block is None:
                errors.append(f"{job} is missing expected step {locator}")
                continue

            for key in ("id", "name", "uses", "if", "run"):
                if key not in step_spec:
                    continue
                actual_value = _extract_top_level_step_value(step_block, key)
                expected_value = step_spec[key]
                if actual_value != expected_value:
                    errors.append(
                        f"{job} step {locator} has {key}={actual_value!r}, expected {expected_value!r}"
                    )

            for mapping_key in ("with", "env"):
                expected_mapping = step_spec.get(mapping_key)
                if not expected_mapping:
                    continue
                actual_mapping = _extract_literal_step_mapping(step_block, mapping_key)
                for entry_key, expected_value in expected_mapping.items():
                    actual_value = actual_mapping.get(entry_key)
                    if actual_value != expected_value:
                        errors.append(
                            f"{job} step {locator} has {mapping_key}.{entry_key}={actual_value!r}, "
                            f"expected {expected_value!r}"
                        )

    return CheckResult("step-contracts", errors)


def _extract_non_script_python_commands(run_commands: list[str]) -> list[str]:
    """Extract python3 commands that are NOT 'python3 scripts/...' from run commands."""
    result: list[str] = []
    for cmd in run_commands:
        stripped = cmd.strip().strip('"').strip("'")
        if stripped.startswith("python3 ") and not stripped.startswith("python3 scripts/"):
            result.append(stripped)
    return result


def _normalize_run_command(raw: str) -> str:
    return raw.rstrip().removesuffix("\\").rstrip()


def _missing_required_run_commands(run_commands: list[str], required_commands: list[str]) -> list[str]:
    normalized_run_commands = [_normalize_run_command(cmd) for cmd in run_commands]
    missing: list[str] = []
    for needle in required_commands:
        normalized_needle = _normalize_run_command(needle)
        if needle.startswith("-"):
            pattern = re.compile(rf"(?:^|\s){re.escape(normalized_needle)}(?:\s|$)")
            present = any(pattern.search(cmd) for cmd in normalized_run_commands)
        else:
            present = any(normalized_needle in cmd for cmd in normalized_run_commands)
        if not present:
            missing.append(needle)
    return missing


def check_python_commands(snapshot: Snapshot, spec: dict) -> CheckResult:
    errors: list[str] = []
    expected_checks = spec["expected_checks_commands"]
    checks_run_cmds = snapshot.run_commands("checks")
    if expected_checks == ["make check"]:
        if not any("make check" in cmd for cmd in checks_run_cmds):
            errors.append("checks job must run 'make check'")
    else:
        errors.extend(
            _compare_lists(
                "checks python scripts",
                snapshot.python_commands("checks", include_args=True),
                "spec checks scripts",
                expected_checks,
            )
        )
        expected_other = spec.get("expected_checks_other_commands", [])
        if expected_other:
            workflow_other = _extract_non_script_python_commands(checks_run_cmds)
            errors.extend(
                _compare_lists(
                    "checks other python commands",
                    workflow_other,
                    "spec checks other commands",
                    expected_other,
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
    missing_build_run = _missing_required_run_commands(
        snapshot.run_commands("build"),
        spec.get("required_build_run_commands", []),
    )
    if missing_build_run:
        errors.append(
            "build job is missing required run commands: " + ", ".join(missing_build_run)
        )

    missing_build_compiler_run = _missing_required_run_commands(
        snapshot.run_commands("build-compiler"),
        spec.get("required_build_compiler_run_commands", []),
    )
    if missing_build_compiler_run:
        errors.append(
            "build-compiler job is missing required run commands: "
            + ", ".join(missing_build_compiler_run)
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
    expected_uploads: dict[str, list[str]] = spec.get("expected_uploaded_artifacts", {})
    expected_downloads: dict[str, list[str]] = spec.get("expected_downloaded_artifacts", {})
    expected_upload_paths: dict[str, list[str | None]] = spec.get("expected_uploaded_artifact_paths", {})
    expected_download_paths: dict[str, list[str | None]] = spec.get("expected_downloaded_artifact_paths", {})

    actual_uploads: dict[str, list[str]] = {}
    actual_downloads: dict[str, list[str]] = {}
    actual_upload_paths: dict[str, list[str | None]] = {}
    actual_download_paths: dict[str, list[str | None]] = {}

    for job in snapshot.jobs:
        job_body = snapshot.job_body(job)
        upload_names = _extract_artifact_names(job_body, action="upload-artifact")
        download_names = _extract_artifact_names(job_body, action="download-artifact")
        upload_paths = _extract_artifact_paths(job_body, action="upload-artifact")
        download_paths = _extract_artifact_paths(job_body, action="download-artifact")

        if upload_names:
            actual_uploads[job] = upload_names
            actual_upload_paths[job] = upload_paths
        if download_names:
            actual_downloads[job] = download_names
            actual_download_paths[job] = download_paths

        if len(upload_names) != len(set(upload_names)):
            errors.append(f"duplicate upload artifact names in {job}: {upload_names}")
        if len(download_names) != len(set(download_names)):
            errors.append(f"duplicate download artifact names in {job}: {download_names}")

    expected_upload_jobs = list(expected_uploads)
    actual_upload_jobs = [job for job in snapshot.jobs if job in actual_uploads]
    errors.extend(
        _compare_lists(
            "upload-artifact jobs",
            actual_upload_jobs,
            "spec upload-artifact jobs",
            expected_upload_jobs,
        )
    )

    expected_download_jobs = list(expected_downloads)
    actual_download_jobs = [job for job in snapshot.jobs if job in actual_downloads]
    errors.extend(
        _compare_lists(
            "download-artifact jobs",
            actual_download_jobs,
            "spec download-artifact jobs",
            expected_download_jobs,
        )
    )

    upload_names = [name for names in actual_uploads.values() for name in names]
    if not upload_names:
        errors.append("no upload-artifact names found in workflow")
        return CheckResult("artifacts", errors)

    dup_upload = sorted([name for name, count in Counter(upload_names).items() if count > 1])
    if dup_upload:
        errors.append("duplicate upload artifacts across workflow: " + ", ".join(dup_upload))

    for job, expected_names in expected_uploads.items():
        if job not in actual_uploads:
            errors.append(f"expected upload-artifact job missing from workflow: {job}")
            continue
        errors.extend(
            _compare_lists(
                f"{job} upload artifacts",
                actual_uploads[job],
                f"spec {job} upload artifacts",
                expected_names,
            )
        )
        if job in expected_upload_paths:
            errors.extend(
                _compare_lists(
                    f"{job} upload artifact paths",
                    [repr(path) for path in actual_upload_paths.get(job, [])],
                    f"spec {job} upload artifact paths",
                    [repr(path) for path in expected_upload_paths[job]],
                )
            )

    for job, expected_names in expected_downloads.items():
        if job not in actual_downloads:
            errors.append(f"expected download-artifact job missing from workflow: {job}")
            continue
        errors.extend(
            _compare_lists(
                f"{job} download artifacts",
                actual_downloads[job],
                f"spec {job} download artifacts",
                expected_names,
            )
        )
        if job in expected_download_paths:
            errors.extend(
                _compare_lists(
                    f"{job} download artifact paths",
                    [repr(path) for path in actual_download_paths.get(job, [])],
                    f"spec {job} download artifact paths",
                    [repr(path) for path in expected_download_paths[job]],
                )
            )

    uploaded = set(upload_names)
    for job, names in actual_downloads.items():
        for name in names:
            if name not in uploaded:
                errors.append(f"{job} downloads unknown artifact: {name}")

    return CheckResult("artifacts", errors)


def _extract_makefile_check_commands() -> list[str]:
    """Extract python3 commands from the Makefile 'check' target."""
    text = MAKEFILE.read_text(encoding="utf-8")
    in_check = False
    commands: list[str] = []
    for line in text.splitlines():
        if re.match(r"^check:", line):
            in_check = True
            continue
        if in_check:
            if line and not line[0].isspace():
                break
            stripped = line.strip()
            if stripped.startswith("python3 "):
                commands.append(stripped)
    return commands


def check_makefile(_snapshot: Snapshot, spec: dict) -> CheckResult:
    errors: list[str] = []
    makefile_commands = _extract_makefile_check_commands()

    required_commands = spec.get("required_makefile_check_commands", [])
    missing_required = [cmd for cmd in required_commands if cmd not in makefile_commands]
    if missing_required:
        errors.append(
            "Makefile check target is missing required commands: "
            + ", ".join(missing_required)
        )

    expected_checks = spec["expected_checks_commands"]
    if expected_checks == ["make check"]:
        return CheckResult("makefile", errors)

    expected = [f"python3 scripts/{cmd}" for cmd in expected_checks]
    expected.extend(spec.get("expected_checks_other_commands", []))
    errors.extend(
        _compare_lists(
            "Makefile check commands",
            makefile_commands,
            "spec checks commands",
            expected,
        )
    )
    return CheckResult("makefile", errors)


def _checks() -> dict[str, callable]:
    return {
        "paths": check_paths,
        "jobs": check_jobs,
        "job-contracts": check_job_contracts,
        "step-contracts": check_step_contracts,
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
