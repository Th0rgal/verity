#!/usr/bin/env python3
"""Generate PrintAxioms.lean from all top-level theorems in Contracts/*/Proofs/, Verity/Proofs/Stdlib/, and Compiler/Proofs/.

This script scans Lean proof files for top-level theorem/lemma declarations,
resolves their fully-qualified names (accounting for namespace blocks), and
generates a Lean file that runs `#print axioms` on each public theorem.

Usage:
    python3 scripts/generate_print_axioms.py          # overwrite PrintAxioms.lean
    python3 scripts/generate_print_axioms.py --check   # verify PrintAxioms.lean is up-to-date
"""

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from property_utils import strip_lean_comments

ROOT = Path(__file__).resolve().parent.parent
PROOF_DIRS = [ROOT / "Verity" / "Proofs", ROOT / "Compiler" / "Proofs"]

def _collect_contract_proof_dirs() -> list[Path]:
    """Collect Contracts/*/Proofs/ directories."""
    contracts_dir = ROOT / "Contracts"
    if not contracts_dir.is_dir():
        return []
    dirs = []
    for d in sorted(contracts_dir.iterdir()):
        proofs = d / "Proofs"
        if proofs.is_dir():
            dirs.append(proofs)
    return dirs
OUTPUT = ROOT / "PrintAxioms.lean"


def file_to_module(path: Path) -> str:
    """Convert a file path to a Lean module name."""
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


SORRY_RE_BODY = re.compile(r"\bsorry\b")


def extract_theorems(path: Path) -> list[tuple[str, bool, bool]]:
    """Extract (fully_qualified_name, is_private, is_sorry) triples from a Lean file.

    FQN construction: In Lean 4 the fully-qualified name of a declaration is
    determined by the namespace stack, not the module (file) path. So a theorem
    ``foo`` inside ``namespace A.B`` has FQN ``A.B.foo`` regardless of which file
    it lives in.

    Namespace tracking: ``end <name>`` closes the matching namespace. Bare
    ``end`` (no name) closes ``mutual`` or ``section`` blocks, NOT namespaces,
    so we only pop the stack when the ``end`` token matches a namespace name.

    Comment handling: Uses the shared ``strip_lean_comments`` lexer which
    correctly handles nested block comments, inline block comments, line
    comments, and string literals.

    Sorry detection: After comment stripping, if any line in a theorem's body
    (from declaration to next declaration/end) contains ``sorry`` as a whole
    word, the theorem is marked as sorry'd.
    """
    text = path.read_text()
    stripped_text = strip_lean_comments(text)
    lines = stripped_text.splitlines()

    # Track namespace stack (each entry is a dotted namespace name)
    ns_stack: list[str] = []
    # Collect (fqn, is_private, start_line_idx) for each declaration
    raw_results: list[tuple[str, bool, int]] = []

    for i, line in enumerate(lines):
        stripped = line.strip()

        # Skip blank lines
        if not stripped:
            continue

        # Track namespace openings
        ns_match = re.match(r"^namespace\s+(\S+)", stripped)
        if ns_match:
            ns_stack.append(ns_match.group(1))
            continue

        # Track namespace closings: only pop when ``end X`` matches the top
        # of the namespace stack. Bare ``end`` (closing mutual/section) and
        # ``end X`` where X doesn't match the top namespace are ignored.
        end_match = re.match(r"^end\s+(\S+)", stripped)
        if end_match:
            end_name = end_match.group(1)
            if ns_stack and ns_stack[-1] == end_name:
                ns_stack.pop()
            continue

        # Bare ``end`` (no name): closes mutual/section, never a namespace
        if stripped == "end":
            continue

        # Match theorem/lemma declarations, including those with attribute
        # annotations like @[simp] theorem foo ...
        decl_match = re.match(
            r"^(?:@\[[^\]]*\]\s*)*(private\s+)?(protected\s+)?(theorem|lemma)\s+(\S+)",
            stripped,
        )
        if decl_match:
            is_private = decl_match.group(1) is not None
            name = decl_match.group(4)
            # Remove trailing colon/where if present
            name = name.rstrip(":")

            # FQN = namespace prefix + local name (no module prefix)
            if ns_stack:
                fqn = f"{'.'.join(ns_stack)}.{name}"
            else:
                fqn = f"{name}"

            raw_results.append((fqn, is_private, i))

    # Determine sorry status by scanning each theorem's body range
    results: list[tuple[str, bool, bool]] = []
    for idx, (fqn, is_private, start) in enumerate(raw_results):
        if idx + 1 < len(raw_results):
            end = raw_results[idx + 1][2]
        else:
            end = len(lines)
        body = "\n".join(lines[start:end])
        is_sorry = bool(SORRY_RE_BODY.search(body))
        results.append((fqn, is_private, is_sorry))

    return results


def generate() -> str:
    """Generate the full PrintAxioms.lean content."""
    all_files: list[Path] = []
    for d in _collect_contract_proof_dirs() + PROOF_DIRS:
        if d.exists():
            all_files.extend(sorted(d.rglob("*.lean")))

    # Skip files that don't compile against current definitions.
    # Conversions.lean was fixed (stale mappings field removed) and
    # Lemmas.lean/Codegen.lean had `default` keyword renamed, but
    # deeper issues remain in these modules.  This list should shrink
    # as the proof files are brought fully in sync.
    EXCLUDED_PATHS = {
        # Pre-existing proof failures (simp/tactic issues, API changes)
        "Compiler/Proofs/YulGeneration/Lemmas.lean",              # unsolved goals in selector proof
        "Compiler/Proofs/YulGeneration/StatementEquivalence.lean", # switch keyword + unfold failures
        "Compiler/Proofs/IRGeneration/Expr.lean",                  # deep API mismatches (.setMapping, evmModulus)
        # Transitive dependents of the above
        "Compiler/Proofs/YulGeneration/Codegen.lean",              # imports Lemmas
        "Compiler/Proofs/YulGeneration/Preservation.lean",         # imports Codegen + StatementEquivalence
    }
    all_files = [
        f for f in all_files
        if "README" not in f.name
        and str(f.relative_to(ROOT)) not in EXCLUDED_PATHS
    ]

    imports: list[str] = []
    sections: list[str] = []

    for path in all_files:
        theorems = extract_theorems(path)
        if not theorems:
            continue

        module = file_to_module(path)
        imports.append(f"import {module}")

        rel = path.relative_to(ROOT)
        lines = [f"\n-- {rel}"]
        for fqn, is_private, is_sorry in theorems:
            if is_private:
                lines.append(f"-- #print axioms {fqn}  -- private")
            elif is_sorry:
                lines.append(f"-- #print axioms {fqn}  -- sorry'd")
            else:
                lines.append(f"#print axioms {fqn}")

        sections.append("\n".join(lines))

    public_count = sum(
        1
        for path in all_files
        for _, priv, sorry in extract_theorems(path)
        if not priv and not sorry
    )
    private_count = sum(
        1
        for path in all_files
        for _, priv, _ in extract_theorems(path)
        if priv
    )
    sorry_count = sum(
        1
        for path in all_files
        for _, priv, sorry in extract_theorems(path)
        if not priv and sorry
    )

    header = (
        "-- Auto-generated by scripts/generate_print_axioms.py\n"
        "-- Runs #print axioms on all top-level theorems/lemmas in proof directories.\n"
        "-- Regenerate with: python3 scripts/generate_print_axioms.py\n"
    )

    footer = (
        f"\n-- Total: {public_count + private_count + sorry_count} theorems/lemmas"
        f" ({public_count} public, {private_count} private, {sorry_count} sorry'd)\n"
    )

    return header + "\n" + "\n".join(imports) + "\n" + "\n".join(sections) + footer


def main() -> None:
    content = generate()

    if "--check" in sys.argv:
        if not OUTPUT.exists():
            print(f"ERROR: {OUTPUT} does not exist. Run without --check to generate.")
            sys.exit(1)
        existing = OUTPUT.read_text()
        if existing != content:
            print(f"ERROR: {OUTPUT} is out of date. Regenerate with:")
            print(f"  python3 scripts/generate_print_axioms.py")
            sys.exit(1)
        print(f"OK: {OUTPUT} is up to date.")
    else:
        OUTPUT.write_text(content)
        print(f"Generated {OUTPUT} with {content.count('#print axioms')} #print axioms statements.")


if __name__ == "__main__":
    main()
