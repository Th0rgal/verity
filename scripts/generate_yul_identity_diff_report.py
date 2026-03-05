#!/usr/bin/env python3
"""Generate a deterministic machine-readable Yul identity diff report.

Compares Verity-generated Yul files against solc-generated Yul files and emits a
stable JSON report with mismatch localization to function/subtree paths.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = ROOT / "artifacts" / "yul_identity_diff_report.json"

FUNC_RE = re.compile(r"^\s*function\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*\(")


@dataclass(frozen=True)
class NormLine:
    depth: int
    text: str


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verity-dir", required=True, help="Directory containing Verity Yul files")
    parser.add_argument("--solc-dir", required=True, help="Directory containing solc Yul files")
    parser.add_argument(
        "--output",
        default=str(DEFAULT_OUTPUT),
        help=f"Output JSON path (default: {DEFAULT_OUTPUT.relative_to(ROOT)})",
    )
    parser.add_argument(
        "--fail-on-mismatch",
        action="store_true",
        help="Exit non-zero when non-identical output is detected",
    )
    return parser.parse_args(argv)


def _strip_line_comment(line: str) -> str:
    return line.split("//", 1)[0]


def _normalize_line(line: str) -> str:
    line = _strip_line_comment(line).strip()
    if not line:
        return ""
    return " ".join(line.split())


def _collect_yul_files(base: Path) -> Dict[str, Path]:
    result: Dict[str, Path] = {}
    if not base.exists():
        return result
    for path in sorted(base.rglob("*.yul")):
        rel = path.relative_to(base).as_posix()
        result[rel] = path
    return result


def _extract_scoped_lines(text: str) -> Dict[str, List[NormLine]]:
    scoped: Dict[str, List[NormLine]] = {"<toplevel>": []}
    current_scope = "<toplevel>"
    function_depth: int | None = None
    depth = 0

    for raw in text.splitlines():
        line = _normalize_line(raw)
        if not line:
            depth += raw.count("{")
            depth -= raw.count("}")
            continue

        match = FUNC_RE.match(line)
        if match:
            current_scope = f"function:{match.group(1)}"
            scoped.setdefault(current_scope, [])
            function_depth = depth

        scoped.setdefault(current_scope, []).append(NormLine(depth=max(depth, 0), text=line))

        depth += raw.count("{")
        depth -= raw.count("}")

        if function_depth is not None and depth <= function_depth:
            current_scope = "<toplevel>"
            function_depth = None

    return scoped


def _compare_sequences(
    rel_path: str,
    scope: str,
    lhs: List[NormLine],
    rhs: List[NormLine],
) -> List[dict]:
    mismatches: List[dict] = []
    max_len = max(len(lhs), len(rhs))
    for idx in range(max_len):
        left = lhs[idx] if idx < len(lhs) else None
        right = rhs[idx] if idx < len(rhs) else None
        if left is None:
            mismatches.append(
                {
                    "file": rel_path,
                    "path": f"{scope}/line:{idx + 1}",
                    "kind": "missing_in_verity",
                    "verity": None,
                    "solc": right.text,
                }
            )
            continue
        if right is None:
            mismatches.append(
                {
                    "file": rel_path,
                    "path": f"{scope}/line:{idx + 1}",
                    "kind": "missing_in_solc",
                    "verity": left.text,
                    "solc": None,
                }
            )
            continue
        if left.text != right.text:
            mismatches.append(
                {
                    "file": rel_path,
                    "path": f"{scope}/depth:{left.depth}/line:{idx + 1}",
                    "kind": "line_mismatch",
                    "verity": left.text,
                    "solc": right.text,
                }
            )
    return mismatches


def _compare_file(rel_path: str, verity_text: str, solc_text: str) -> List[dict]:
    mismatches: List[dict] = []
    v_scopes = _extract_scoped_lines(verity_text)
    s_scopes = _extract_scoped_lines(solc_text)

    all_scopes = sorted(set(v_scopes.keys()) | set(s_scopes.keys()))
    for scope in all_scopes:
        v_seq = v_scopes.get(scope)
        s_seq = s_scopes.get(scope)
        if v_seq is None:
            mismatches.append(
                {
                    "file": rel_path,
                    "path": scope,
                    "kind": "scope_missing_in_verity",
                    "verity": None,
                    "solc": "present",
                }
            )
            continue
        if s_seq is None:
            mismatches.append(
                {
                    "file": rel_path,
                    "path": scope,
                    "kind": "scope_missing_in_solc",
                    "verity": "present",
                    "solc": None,
                }
            )
            continue
        mismatches.extend(_compare_sequences(rel_path, scope, v_seq, s_seq))

    return mismatches


def build_report(verity_dir: Path, solc_dir: Path) -> dict:
    verity_files = _collect_yul_files(verity_dir)
    solc_files = _collect_yul_files(solc_dir)

    all_files = sorted(set(verity_files.keys()) | set(solc_files.keys()))
    mismatches: List[dict] = []

    for rel in all_files:
        v_path = verity_files.get(rel)
        s_path = solc_files.get(rel)
        if v_path is None:
            mismatches.append(
                {
                    "file": rel,
                    "path": "<file>",
                    "kind": "file_missing_in_verity",
                    "verity": None,
                    "solc": "present",
                }
            )
            continue
        if s_path is None:
            mismatches.append(
                {
                    "file": rel,
                    "path": "<file>",
                    "kind": "file_missing_in_solc",
                    "verity": "present",
                    "solc": None,
                }
            )
            continue
        mismatches.extend(_compare_file(rel, v_path.read_text(encoding="utf-8"), s_path.read_text(encoding="utf-8")))

    summary: Dict[str, int] = {}
    for mismatch in mismatches:
        kind = mismatch["kind"]
        summary[kind] = summary.get(kind, 0) + 1

    return {
        "tool": {"name": "generate_yul_identity_diff_report", "schemaVersion": 1},
        "inputs": {"verityDir": str(verity_dir), "solcDir": str(solc_dir)},
        "status": "identical" if not mismatches else "non_identical",
        "summary": {
            "filesCompared": len(all_files),
            "totalMismatches": len(mismatches),
            "byKind": dict(sorted(summary.items())),
        },
        "mismatches": mismatches,
    }


def write_report(report: dict, output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    report = build_report(Path(args.verity_dir), Path(args.solc_dir))
    write_report(report, Path(args.output))
    print(f"Wrote Yul identity report: {args.output}")
    print(f"Status: {report['status']} ({report['summary']['totalMismatches']} mismatches)")
    if args.fail_on_mismatch and report["status"] != "identical":
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
