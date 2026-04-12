#!/usr/bin/env python3
"""Update hardcoded numbers in documentation files from verification_status.json.

Replaces the block between <!-- BEGIN GENERATED STATS --> and <!-- END GENERATED STATS -->
in README.md, and the quick-facts block in docs-site/public/llms.txt.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "artifacts" / "verification_status.json"


def load_artifact() -> dict:
    with open(ARTIFACT) as f:
        return json.load(f)


def update_readme(data: dict) -> bool:
    readme = ROOT / "README.md"
    text = readme.read_text(encoding="utf-8")

    theorems = data["theorems"]
    proofs = data["proofs"]
    tests = data["tests"]
    codebase = data["codebase"]
    toolchain = data["toolchain"]

    lean_version = toolchain["lean"].split(":")[-1].lstrip("v")
    contract_count = len(theorems["per_contract"])

    block = (
        "<!-- BEGIN GENERATED STATS -->\n"
        "| Metric | Value |\n"
        "|--------|-------|\n"
        f"| Theorems | {theorems['total']} ({theorems['proven']} proven, {proofs['sorry']} sorry) |\n"
        f"| Axioms | {proofs['axioms']} |\n"
        f"| Foundry tests | {tests['foundry_functions']} ({tests['property_functions']} property) |\n"
        f"| Verified contracts | {contract_count} |\n"
        f"| Core EDSL | {codebase['core_lines']} lines |\n"
        f"| Lean | {lean_version} |\n"
        "<!-- END GENERATED STATS -->"
    )

    pattern = re.compile(
        r"<!-- BEGIN GENERATED STATS -->.*?<!-- END GENERATED STATS -->",
        re.DOTALL,
    )
    if not pattern.search(text):
        print("WARNING: README.md missing GENERATED STATS markers", file=sys.stderr)
        return False

    new_text = pattern.sub(block, text)
    if new_text != text:
        readme.write_text(new_text, encoding="utf-8")
        return True
    return False


def update_llms_txt(data: dict) -> bool:
    llms = ROOT / "docs-site" / "public" / "llms.txt"
    if not llms.exists():
        return False

    text = llms.read_text(encoding="utf-8")

    theorems = data["theorems"]
    proofs = data["proofs"]
    tests = data["tests"]
    codebase = data["codebase"]
    toolchain = data["toolchain"]

    lean_version = toolchain["lean"].split(":")[-1].lstrip("v")
    contract_count = len(theorems["per_contract"])

    block = (
        "<!-- BEGIN GENERATED QUICK FACTS -->\n"
        f"- **Language**: Lean {lean_version}\n"
        f"- **Core Size**: {codebase['core_lines']} lines\n"
        f"- **Verified Contracts**: {contract_count} ({', '.join(theorems['per_contract'].keys())})\n"
        f"- **Theorems**: {theorems['total']} across {theorems['categories']} categories, "
        f"{theorems['proven']} fully proven\n"
        f"- **Axioms**: {proofs['axioms']} documented Lean axioms (see AXIOMS.md)\n"
        f"- **Tests**: {tests['foundry_functions']} Foundry tests, "
        f"{tests['property_functions']} property tests\n"
        f"- **Build**: `lake build` verifies all proofs\n"
        f"- **Repository**: https://github.com/lfglabs-dev/verity\n"
        "<!-- END GENERATED QUICK FACTS -->"
    )

    pattern = re.compile(
        r"<!-- BEGIN GENERATED QUICK FACTS -->.*?<!-- END GENERATED QUICK FACTS -->",
        re.DOTALL,
    )
    if not pattern.search(text):
        print("WARNING: llms.txt missing GENERATED QUICK FACTS markers", file=sys.stderr)
        return False

    new_text = pattern.sub(block, text)
    if new_text != text:
        llms.write_text(new_text, encoding="utf-8")
        return True
    return False


def main() -> None:
    if not ARTIFACT.exists():
        print(f"Missing artifact: {ARTIFACT}", file=sys.stderr)
        raise SystemExit(1)

    data = load_artifact()

    check_mode = "--check" in sys.argv

    if check_mode:
        errors: list[str] = []

        # Check README
        readme = ROOT / "README.md"
        text = readme.read_text(encoding="utf-8")
        pattern = re.compile(
            r"<!-- BEGIN GENERATED STATS -->.*?<!-- END GENERATED STATS -->",
            re.DOTALL,
        )
        match = pattern.search(text)
        if not match:
            errors.append("README.md: missing GENERATED STATS markers")
        else:
            block = match.group(0)
            total = data["theorems"]["total"]
            if f"| Theorems | {total} " not in block:
                errors.append(f"README.md: theorem count mismatch (expected {total})")
            axioms = data["proofs"]["axioms"]
            if f"| Axioms | {axioms} |" not in block:
                errors.append(f"README.md: axiom count mismatch (expected {axioms})")

        # Check llms.txt
        llms = ROOT / "docs-site" / "public" / "llms.txt"
        if llms.exists():
            text = llms.read_text(encoding="utf-8")
            pattern = re.compile(
                r"<!-- BEGIN GENERATED QUICK FACTS -->.*?<!-- END GENERATED QUICK FACTS -->",
                re.DOTALL,
            )
            match = pattern.search(text)
            if not match:
                errors.append("llms.txt: missing GENERATED QUICK FACTS markers")
            else:
                block = match.group(0)
                total = data["theorems"]["total"]
                if f"**Theorems**: {total} " not in block:
                    errors.append(f"llms.txt: theorem count mismatch (expected {total})")

        if errors:
            for e in errors:
                print(e, file=sys.stderr)
            raise SystemExit(1)
        print("update_doc_numbers: all generated blocks are in sync")
    else:
        changed = []
        if update_readme(data):
            changed.append("README.md")
        if update_llms_txt(data):
            changed.append("llms.txt")
        if changed:
            print(f"Updated: {', '.join(changed)}")
        else:
            print("No changes needed")


if __name__ == "__main__":
    main()
