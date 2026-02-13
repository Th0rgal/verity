#!/usr/bin/env python3
import argparse
import sys
import unicodedata
from pathlib import Path

BIDI_CONTROLS = {
    "LRE",
    "RLE",
    "LRO",
    "RLO",
    "PDF",
    "LRI",
    "RLI",
    "FSI",
    "PDI",
}


def scan_file(path: Path) -> list[tuple[int, int, str, str, str]]:
    text = path.read_text(encoding="utf-8")
    issues: list[tuple[int, int, str, str, str]] = []
    line = 1
    col = 0
    for ch in text:
        if ch == "\n":
            line += 1
            col = 0
            continue
        col += 1
        bidi = unicodedata.bidirectional(ch)
        category = unicodedata.category(ch)
        if bidi in BIDI_CONTROLS or category == "Cf":
            name = unicodedata.name(ch, "UNKNOWN")
            issues.append((line, col, f"U+{ord(ch):04X}", name, category))
    return issues


def collect_paths(root: Path) -> list[Path]:
    if root.is_file():
        return [root]
    paths = []
    for ext in ("*.md", "*.mdx"):
        paths.extend(root.rglob(ext))
    return paths


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="+", help="Files or directories to scan")
    args = parser.parse_args()

    had_issue = False
    for raw in args.paths:
        root = Path(raw)
        for path in sorted(collect_paths(root)):
            issues = scan_file(path)
            if not issues:
                continue
            had_issue = True
            for line, col, code, name, category in issues:
                print(f"{path}:{line}:{col}: {code} {name} ({category})")
    if had_issue:
        print("\nERROR: Remove Unicode control characters from documentation files.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
