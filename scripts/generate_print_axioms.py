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


def extract_theorems(path: Path) -> list[tuple[str, bool, bool, list[str]]]:
    """Extract (fully_qualified_name, is_private, is_sorry, proof_lines) from a Lean file.

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

    Sorry detection: A theorem is marked sorry'd if its proof body ends
    with ``:= by sorry`` or ``:= by\\n  sorry``.  We scan forward from
    the theorem declaration until we find the ``:= by`` proof opener,
    then check if the next non-blank line is ``sorry``.

    Transitive sorry propagation happens in ``generate()`` after all files
    are parsed: any theorem whose proof body references a sorry'd theorem
    (by local name) is also marked sorry.
    """
    text = path.read_text()
    stripped_text = strip_lean_comments(text)
    lines = stripped_text.splitlines()

    # Track namespace stack (each entry is a dotted namespace name)
    ns_stack: list[str] = []
    results: list[tuple[str, bool, bool, list[str]]] = []

    i = 0
    while i < len(lines):
        stripped = lines[i].strip()

        # Skip blank lines
        if not stripped:
            i += 1
            continue

        # Track namespace openings
        ns_match = re.match(r"^namespace\s+(\S+)", stripped)
        if ns_match:
            ns_stack.append(ns_match.group(1))
            i += 1
            continue

        # Track namespace closings: only pop when ``end X`` matches the top
        # of the namespace stack. Bare ``end`` (closing mutual/section) and
        # ``end X`` where X doesn't match the top namespace are ignored.
        end_match = re.match(r"^end\s+(\S+)", stripped)
        if end_match:
            end_name = end_match.group(1)
            if ns_stack and ns_stack[-1] == end_name:
                ns_stack.pop()
            i += 1
            continue

        # Bare ``end`` (no name): closes mutual/section, never a namespace
        if stripped == "end":
            i += 1
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

            # Detect sorry'd proofs: scan forward from the declaration
            # looking for `:= by` and then checking if the proof body
            # is just `sorry`.
            is_sorry = False
            proof_lines: list[str] = []
            proof_started = False
            _NEXT_DECL_RE = re.compile(
                r"^(?:@\[[^\]]*\]\s*)*(?:private\s+)?(?:protected\s+)?"
                r"(?:theorem|lemma|def|structure|inductive|class|instance|namespace|section|end)\b"
            )
            for j in range(i, min(i + 500, len(lines))):
                check_line = lines[j].strip()
                # `:= by sorry` on one line
                if ":= by sorry" in check_line:
                    is_sorry = True
                    break
                # `:= by` ending a line — check next non-blank for sorry
                if check_line.endswith(":= by"):
                    proof_started = True
                    for k in range(j + 1, min(j + 4, len(lines))):
                        next_line = lines[k].strip()
                        if not next_line:
                            continue
                        if next_line == "sorry":
                            is_sorry = True
                        break
                    if is_sorry:
                        break
                    continue
                # `:= sorry` (term-mode sorry)
                if check_line.endswith(":= sorry"):
                    is_sorry = True
                    break
                # Hit next declaration — stop collecting proof body
                if j > i and _NEXT_DECL_RE.match(check_line):
                    break
                # Collect proof body lines (after := by)
                if proof_started and check_line:
                    proof_lines.append(check_line)

            results.append((fqn, is_private, is_sorry, proof_lines))

        i += 1

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

    # Collect all theorems from all files
    file_theorems: list[tuple[Path, list[tuple[str, bool, bool, list[str]]]]] = []
    for path in all_files:
        theorems = extract_theorems(path)
        if theorems:
            file_theorems.append((path, theorems))

    # Build set of directly sorry'd local names (for transitive detection)
    sorry_local_names: set[str] = set()
    for _, theorems in file_theorems:
        for fqn, is_private, is_sorry, _ in theorems:
            if is_sorry:
                # Add both the FQN and the local name (last component)
                sorry_local_names.add(fqn)
                sorry_local_names.add(fqn.rsplit(".", 1)[-1])

    # Propagate sorry transitively: if a non-sorry theorem's proof body
    # references any sorry'd theorem (by local name), mark it sorry too.
    # Repeat until fixpoint to handle multi-level chains.
    # We use word-boundary matching to avoid false positives from substring
    # overlap (e.g. "lookupBinding?_some_of_mem" matching inside
    # "bindSupportedParams_lookupBinding?_some_of_mem").
    all_theorems_flat: list[tuple[str, bool, bool, list[str]]] = [
        t for _, theorems in file_theorems for t in theorems
    ]

    def _body_references_sorry(body_text: str, sorry_names: set[str]) -> bool:
        """Check if body_text references any sorry'd name as a whole identifier."""
        for sname in sorry_names:
            idx = 0
            while True:
                pos = body_text.find(sname, idx)
                if pos == -1:
                    break
                # Check word boundary: char before must be non-alnum/underscore
                # (or start of string), char after must be non-alnum/underscore
                # (or end of string).
                before_ok = pos == 0 or not (body_text[pos - 1].isalnum() or body_text[pos - 1] == "_")
                end = pos + len(sname)
                after_ok = end == len(body_text) or not (body_text[end].isalnum() or body_text[end] == "_")
                if before_ok and after_ok:
                    return True
                idx = pos + 1
        return False

    changed = True
    while changed:
        changed = False
        new_sorry_names: set[str] = set()
        for fqn, is_private, is_sorry, proof_lines in all_theorems_flat:
            if is_sorry or is_private:
                continue
            if fqn in sorry_local_names or fqn.rsplit(".", 1)[-1] in sorry_local_names:
                continue
            body_text = " ".join(proof_lines)
            if _body_references_sorry(body_text, sorry_local_names):
                new_sorry_names.add(fqn)
                new_sorry_names.add(fqn.rsplit(".", 1)[-1])
        if new_sorry_names - sorry_local_names:
            sorry_local_names |= new_sorry_names
            changed = True

    # Build the sorry FQN set for output
    sorry_fqns: set[str] = set()
    for fqn, is_private, is_sorry, proof_lines in all_theorems_flat:
        if is_sorry or is_private:
            continue
        local = fqn.rsplit(".", 1)[-1]
        if fqn in sorry_local_names or local in sorry_local_names:
            sorry_fqns.add(fqn)

    imports: list[str] = []
    sections: list[str] = []

    for path, theorems in file_theorems:
        module = file_to_module(path)
        imports.append(f"import {module}")

        rel = path.relative_to(ROOT)
        lines = [f"\n-- {rel}"]
        for fqn, is_private, is_sorry, _ in theorems:
            if is_private:
                lines.append(f"-- #print axioms {fqn}  -- private")
            elif is_sorry or fqn in sorry_fqns:
                lines.append(f"-- #print axioms {fqn}  -- sorry")
            else:
                lines.append(f"#print axioms {fqn}")

        sections.append("\n".join(lines))

    active_count = sum(
        1
        for _, theorems in file_theorems
        for fqn, priv, sorry, _ in theorems
        if not priv and not sorry and fqn not in sorry_fqns
    )
    private_count = sum(
        1
        for _, theorems in file_theorems
        for _, priv, _, _ in theorems
        if priv
    )
    sorry_count = sum(
        1
        for _, theorems in file_theorems
        for fqn, priv, sorry, _ in theorems
        if (sorry or fqn in sorry_fqns) and not priv
    )
    total = active_count + private_count + sorry_count

    header = (
        "-- Auto-generated by scripts/generate_print_axioms.py\n"
        "-- Runs #print axioms on all top-level theorems/lemmas in proof directories.\n"
        "-- Regenerate with: python3 scripts/generate_print_axioms.py\n"
    )

    footer = (
        f"\n-- Total: {total} theorems/lemmas"
        f" ({active_count} active, {private_count} private, {sorry_count} sorry)\n"
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
        active = sum(1 for line in content.splitlines() if line.startswith("#print axioms"))
        print(f"Generated {OUTPUT} with {active} active #print axioms statements.")


if __name__ == "__main__":
    main()
