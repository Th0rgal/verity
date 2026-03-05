#!/usr/bin/env python3
"""Detect placeholder/template-only GitHub issue submissions."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

PLACEHOLDER_TITLES = {
    "[Compiler Enhancement]",
    "[Trust Reduction]",
    "[Property Coverage]",
    "[Layer 3] Prove <STATEMENT_TYPE> equivalence",
}

PLACEHOLDER_SNIPPETS = {
    "<What compiler feature or improvement>",
    "<what compiler cannot do today>",
    "<real scenario this enables>",
    "<High-level approach>",
    "<example>",
    "<expected>",
    "<Component 1>",
    "<changes>",
    "<hours/weeks>",
    "<STATEMENT_TYPE>",
    "<STATEMENT_SYNTAX>",
    "<THEOREM_NAME>_equiv",
    "<DESCRIPTION>",
    "<STRATEGY_DESCRIPTION>",
    "<LOW|MEDIUM|HIGH>",
    "<TIME_ESTIMATE>",
    "<DEPENDENCIES>",
    "<LINE_NUMBER>",
}

CI_LOG_MARKERS = (
    "Current runner version:",
    "##[group]Runner Image Provisioner",
    "Downloading action repository",
    "##[error]The operation was canceled.",
)

TIMESTAMP_RE = re.compile(r"\b20\d{2}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}")
MIN_TIMESTAMP_LINES_FOR_LOG_DUMP = 8


def _normalize(text: str) -> str:
    return text.strip()


def detect_invalid_issue(title: str, body: str) -> list[str]:
    findings: list[str] = []
    title_norm = _normalize(title)

    if title_norm in PLACEHOLDER_TITLES:
        findings.append("title matches an unresolved template placeholder")

    body_norm = _normalize(body)
    if not body_norm:
        findings.append("body is empty")

    placeholder_hits = sorted(token for token in PLACEHOLDER_SNIPPETS if token in body_norm)
    if placeholder_hits:
        findings.append(
            "body contains unresolved template placeholders: " + ", ".join(placeholder_hits[:6])
        )

    marker_hits = [marker for marker in CI_LOG_MARKERS if marker in body_norm]
    timestamp_hits = len(TIMESTAMP_RE.findall(body_norm))
    if marker_hits or timestamp_hits >= MIN_TIMESTAMP_LINES_FOR_LOG_DUMP:
        findings.append("body appears to contain pasted CI/GitHub Actions logs")

    return findings


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--title", required=True, help="Issue title")
    parser.add_argument(
        "--body-file",
        type=Path,
        required=True,
        help="Path to a UTF-8 text file containing the issue body",
    )
    parser.add_argument(
        "--format",
        choices=("plain", "github"),
        default="plain",
        help="Output format for findings",
    )
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    body = args.body_file.read_text(encoding="utf-8")
    findings = detect_invalid_issue(args.title, body)

    if not findings:
        print("issue submission looks valid")
        return 0

    if args.format == "github":
        print("This issue appears to be a template placeholder/log dump and is being closed automatically.")
        print("")
        print("Findings:")
        for finding in findings:
            print(f"- {finding}")
        print("")
        print("Please open a new issue and fill every required field with concrete details.")
    else:
        print("issue submission validation failed:", file=sys.stderr)
        for finding in findings:
            print(f"- {finding}", file=sys.stderr)

    return 1


if __name__ == "__main__":
    raise SystemExit(main())
