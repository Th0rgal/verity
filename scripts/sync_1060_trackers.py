#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "artifacts" / "issue_1060_progress.json"
REPO = "Th0rgal/verity"

ITEM_TITLES = {
    "0.1": "Prompt/integrity guardrails",
    "0.2": "CI and automation hardening",
    "1.1": "Typed IR AST",
    "1.2": "Typed IR interpreter",
    "1.3": "Typed IR golden tests (Counter + SimpleStorage)",
    "2.1": "SSA compiler to TBlock",
    "2.2": "Generic compilation correctness theorem",
    "2.3": "TBlock -> Yul lowering",
    "2.4": "End-to-end Counter through typed IR pipeline",
    "2.5": "End-to-end SimpleStorage through full pipeline",
    "3.1": "Separate Env from ContractState",
    "3.2": "Counter bridge theorem generation",
    "3.3": "SimpleStorage + Owned bridge theorems",
    "3.4": "SafeCounter + OwnedCounter bridge theorems",
    "3.5": "Mapping support (Ledger + SimpleToken)",
    "4.1": "ERC20",
    "4.2": "ERC721",
    "4.3": "External call oracle model",
    "4.4": "Eliminate all sorry",
    "4.5": "Golden + differential tests",
    "4.6": "Docs + cleanup",
}

START = "<!-- issue-1060-tracker:start -->"
END = "<!-- issue-1060-tracker:end -->"


def sh(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def render_tracker(items: dict[str, dict]) -> str:
    lines = [
        START,
        "## Item tracker (generated from `artifacts/issue_1060_progress.json`)",
    ]
    for item_id in ITEM_TITLES:
        status = str(items.get(item_id, {}).get("status", "open"))
        checked = "x" if status == "complete" else " "
        suffix = ""
        if status in {"partial", "in_progress"}:
            suffix = f" *(status: {status})*"
        lines.append(f"- [{checked}] {item_id} {ITEM_TITLES[item_id]}{suffix}")
    lines.append(END)
    return "\n".join(lines)


def upsert_tracker(body: str, tracker: str, *, prune_legacy_item_tracker: bool) -> str:
    if START in body and END in body:
        return re.sub(
            re.escape(START) + r".*?" + re.escape(END),
            tracker,
            body,
            flags=re.DOTALL,
        )

    updated = body
    if prune_legacy_item_tracker:
        updated = re.sub(
            r"\n## Item tracker\n(?:.|\n)*?(?=\n## |\Z)",
            "\n",
            updated,
            flags=re.MULTILINE,
        )

    updated = updated.rstrip() + "\n\n" + tracker + "\n"
    return updated


def write_temp_and_edit(kind: str, number: int, new_body: str, dry_run: bool) -> None:
    if dry_run:
        print(f"[{kind} #{number}] dry run body preview:\n")
        print(new_body)
        return

    with tempfile.NamedTemporaryFile("w", delete=False, encoding="utf-8") as tmp:
        tmp.write(new_body)
        tmp_path = tmp.name

    try:
        if kind == "pr":
            subprocess.check_call(["gh", "pr", "edit", str(number), "--repo", REPO, "--body-file", tmp_path])
        else:
            subprocess.check_call(["gh", "issue", "edit", str(number), "--repo", REPO, "--body-file", tmp_path])
    finally:
        Path(tmp_path).unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description="Sync issue/pr roadmap trackers from issue_1060_progress.json")
    parser.add_argument("--pr", type=int, default=1065)
    parser.add_argument("--issue", type=int, default=1060)
    parser.add_argument("--skip-pr", action="store_true")
    parser.add_argument("--skip-issue", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    items = data.get("items", {})
    tracker = render_tracker(items)

    if not args.skip_pr:
        pr_body = sh("gh", "pr", "view", str(args.pr), "--repo", REPO, "--json", "body", "--jq", ".body")
        new_pr_body = upsert_tracker(pr_body, tracker, prune_legacy_item_tracker=True)
        write_temp_and_edit("pr", args.pr, new_pr_body, args.dry_run)
        print(f"Synced PR #{args.pr} tracker")

    if not args.skip_issue:
        issue_body = sh("gh", "issue", "view", str(args.issue), "--repo", REPO, "--json", "body", "--jq", ".body")
        new_issue_body = upsert_tracker(issue_body, tracker, prune_legacy_item_tracker=False)
        write_temp_and_edit("issue", args.issue, new_issue_body, args.dry_run)
        print(f"Synced issue #{args.issue} tracker")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
