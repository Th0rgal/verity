#!/usr/bin/env python3
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "artifacts" / "issue_1060_progress.json"

ROADMAP_ITEMS = [
    "0.1", "0.2",
    "1.1", "1.2", "1.3",
    "2.1", "2.2", "2.3", "2.4", "2.5",
    "3.1", "3.2", "3.3", "3.4", "3.5",
    "4.1", "4.2", "4.3", "4.4", "4.5", "4.6",
]

SEMANTIC_THEOREM_ITEMS = {
    "2.2", "3.2", "3.3", "3.4", "3.5", "4.1", "4.2", "4.3", "4.4"
}

ALLOWED_STATUS = {"open", "in_progress", "partial", "complete"}
WEAKENING_ALLOWED = {"unchanged", "strengthened"}
TRIVIAL_SUMMARY_RE = re.compile(r"\b(rfl|refl|trivial|tautolog|definitional equality)\b", re.IGNORECASE)
RUN_MARKER_RE = re.compile(r"\b(run_id=[^\s\]]+|artifact_sha256=[0-9a-fA-F]{7,64})\b")
SYMBOL_DECL_RE_TEMPLATE = r"\b(?:theorem|lemma|def)\s+{name}\b"


def _err(errors: list[str], msg: str) -> None:
    errors.append(msg)


def _load_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise RuntimeError(f"missing ledger file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"invalid JSON in {path}: {exc}") from exc


def _expect_str(errors: list[str], where: str, value: object) -> None:
    if not isinstance(value, str) or not value.strip():
        _err(errors, f"{where} must be a non-empty string")


def _expect_list(errors: list[str], where: str, value: object) -> list:
    if not isinstance(value, list):
        _err(errors, f"{where} must be a list")
        return []
    return value


def validate(data: dict) -> list[str]:
    errors: list[str] = []
    active_items: list[str] = []
    file_cache: dict[Path, str] = {}

    if not isinstance(data, dict):
        return ["ledger root must be an object"]

    _expect_str(errors, "issue", data.get("issue"))
    _expect_str(errors, "pr", data.get("pr"))

    baseline_sorry = data.get("baseline_sorry")
    if not isinstance(baseline_sorry, int) or baseline_sorry < 0:
        _err(errors, "baseline_sorry must be a non-negative integer")

    items = data.get("items")
    if not isinstance(items, dict):
        _err(errors, "items must be an object keyed by roadmap item id")
        return errors

    for item_id in ROADMAP_ITEMS:
        if item_id not in items:
            _err(errors, f"missing roadmap item in ledger: {item_id}")

    for item_id, entry in items.items():
        if item_id not in ROADMAP_ITEMS:
            _err(errors, f"unknown roadmap item id: {item_id}")
            continue
        if not isinstance(entry, dict):
            _err(errors, f"items.{item_id} must be an object")
            continue

        status = entry.get("status")
        if status not in ALLOWED_STATUS:
            _err(errors, f"items.{item_id}.status must be one of {sorted(ALLOWED_STATUS)}")
        if status in {"partial", "in_progress"}:
            active_items.append(item_id)

        acceptance = _expect_list(errors, f"items.{item_id}.acceptance_criteria", entry.get("acceptance_criteria"))
        files_changed = _expect_list(errors, f"items.{item_id}.files_changed", entry.get("files_changed"))
        verification = _expect_list(errors, f"items.{item_id}.verification_commands", entry.get("verification_commands"))
        verification_results = _expect_list(errors, f"items.{item_id}.verification_results", entry.get("verification_results"))

        evidence = entry.get("evidence")
        if not isinstance(evidence, dict):
            _err(errors, f"items.{item_id}.evidence must be an object")
            evidence = {}

        theorems = _expect_list(errors, f"items.{item_id}.evidence.theorems", evidence.get("theorems", []))
        tests = _expect_list(errors, f"items.{item_id}.evidence.tests", evidence.get("tests", []))

        obligation_delta = entry.get("obligation_delta")
        if not isinstance(obligation_delta, dict):
            _err(errors, f"items.{item_id}.obligation_delta must be an object")
            obligation_delta = {}

        removed_sorries = obligation_delta.get("removed_sorries")
        if not isinstance(removed_sorries, list):
            _err(errors, f"items.{item_id}.obligation_delta.removed_sorries must be a list")
            removed_sorries = []

        for idx, row in enumerate(removed_sorries):
            where = f"items.{item_id}.obligation_delta.removed_sorries[{idx}]"
            if not isinstance(row, dict):
                _err(errors, f"{where} must be an object")
                continue
            _expect_str(errors, f"{where}.old_location", row.get("old_location"))
            _expect_str(errors, f"{where}.new_location", row.get("new_location"))
            strength = row.get("strength_change")
            if strength not in WEAKENING_ALLOWED:
                _err(errors, f"{where}.strength_change must be one of {sorted(WEAKENING_ALLOWED)}")

        # Verify theorem artifacts reference real declarations at HEAD.
        for idx, thm in enumerate(theorems):
            where = f"items.{item_id}.evidence.theorems[{idx}]"
            if not isinstance(thm, dict):
                continue
            name = thm.get("name")
            file_rel = thm.get("file")
            if not isinstance(name, str) or not name.strip():
                continue
            if not isinstance(file_rel, str) or not file_rel.strip():
                continue
            file_path = ROOT / file_rel
            if not file_path.is_file():
                _err(errors, f"{where}.file does not exist in repository: {file_rel}")
                continue
            if file_path not in file_cache:
                file_cache[file_path] = file_path.read_text(encoding="utf-8")
            symbol_re = re.compile(SYMBOL_DECL_RE_TEMPLATE.format(name=re.escape(name)))
            if not symbol_re.search(file_cache[file_path]):
                _err(errors, f"{where}.name not found as theorem/lemma/def in {file_rel}: {name}")

        # Evidence for active/complete runs must include traceable execution markers.
        if status in {"partial", "complete"}:
            if verification and verification_results and len(verification_results) != len(verification):
                _err(
                    errors,
                    f"items.{item_id} has mismatched verification_commands ({len(verification)}) "
                    f"and verification_results ({len(verification_results)})",
                )
            if verification_results:
                for idx, result in enumerate(verification_results):
                    if not isinstance(result, str):
                        _err(errors, f"items.{item_id}.verification_results[{idx}] must be a string")
                        continue
                    if not RUN_MARKER_RE.search(result):
                        _err(
                            errors,
                            f"items.{item_id}.verification_results[{idx}] must include "
                            "run_id=<...> or artifact_sha256=<...>",
                        )

        if status == "complete":
            if not acceptance:
                _err(errors, f"items.{item_id} is complete but has empty acceptance_criteria")
            if not files_changed:
                _err(errors, f"items.{item_id} is complete but has no files_changed")
            if not verification:
                _err(errors, f"items.{item_id} is complete but has no verification_commands")
            if not verification_results:
                _err(errors, f"items.{item_id} is complete but has no verification_results")
            if not any("lake build" in str(cmd) for cmd in verification):
                _err(errors, f"items.{item_id} is complete but verification_commands has no lake build")
            if not tests:
                _err(errors, f"items.{item_id} is complete but has no test evidence")

            if item_id in SEMANTIC_THEOREM_ITEMS:
                if not theorems:
                    _err(errors, f"items.{item_id} is complete but has no theorem evidence")
                for idx, thm in enumerate(theorems):
                    where = f"items.{item_id}.evidence.theorems[{idx}]"
                    if not isinstance(thm, dict):
                        _err(errors, f"{where} must be an object")
                        continue
                    _expect_str(errors, f"{where}.name", thm.get("name"))
                    _expect_str(errors, f"{where}.file", thm.get("file"))
                    summary = thm.get("statement_summary")
                    _expect_str(errors, f"{where}.statement_summary", summary)
                    if isinstance(summary, str) and TRIVIAL_SUMMARY_RE.search(summary):
                        _err(errors, f"{where}.statement_summary looks trivial; provide semantic content")

    if len(active_items) > 1:
        _err(
            errors,
            "at most one roadmap item may be active (status in {in_progress, partial}); "
            f"found {len(active_items)}: {', '.join(active_items)}",
        )

    return errors


def main() -> int:
    try:
        data = _load_json(LEDGER)
    except RuntimeError as exc:
        print(f"issue #1060 integrity check failed: {exc}", file=sys.stderr)
        return 1

    errors = validate(data)
    if errors:
        print("issue #1060 integrity check failed:", file=sys.stderr)
        for err in errors:
            print(f"- {err}", file=sys.stderr)
        return 1

    print("issue #1060 integrity check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
