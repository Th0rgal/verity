#!/usr/bin/env python3
"""Check for Lean code hygiene issues.

Validates:
1. No debug commands (#eval, #check, #print, #reduce) in proof files
2. Exactly 1 allowUnsafeReducibility (documented trust assumption)
3. Zero sorry in Lean code after scrubbing comments/strings
4. No native_decide in proof files outside smoke tests (kernel bypass)

Usage:
    python3 scripts/check_lean_hygiene.py
"""

from __future__ import annotations

import re

from property_utils import ROOT, report_errors, scrub_lean_code

SORRY_RE = re.compile(r"\bsorry\b")
THEOREM_RE = re.compile(
    r"(?:private\s+)?(?:theorem|lemma|def)\s+([A-Za-z_][A-Za-z0-9_.']*)(?![A-Za-z0-9_.'])"
)
# Declaration-boundary keywords that start a new scope.  If the backward
# scan from a sorry hits one of these before finding a theorem/lemma/def,
# the sorry is outside any allowlisted declaration (e.g. in an example
# block) and should not be attributed to the prior theorem.
BOUNDARY_RE = re.compile(
    r"^\s*(?:example|instance|abbrev|opaque|structure|class|inductive|section|namespace|end)\b"
    r"|^\s*#"
)


def _find_enclosing_theorem(lines: list[str], sorry_idx: int) -> str | None:
    """Scan backwards from *sorry_idx* to find the enclosing theorem name.

    Stops at declaration boundaries (``example``, ``instance``, ``#``-commands,
    etc.) so that a ``sorry`` in a later block is not misattributed to a prior
    pinned theorem.
    """
    for j in range(sorry_idx, -1, -1):
        m = THEOREM_RE.search(lines[j])
        if m:
            return m.group(1)
        if BOUNDARY_RE.match(lines[j]):
            return None
    return None


def line_starts_with_command(line: str, cmd: str) -> bool:
    stripped = line.lstrip()
    return stripped == cmd or stripped.startswith(cmd + " ")


def main() -> None:
    errors: list[str] = []

    # Check 1: No debug commands in proof files
    debug_commands = ["#eval", "#check", "#print", "#reduce"]
    proof_dirs = [ROOT / "Compiler" / "Proofs", ROOT / "Verity" / "Proofs", ROOT / "Contracts"]
    for proof_dir in proof_dirs:
        for lean_file in proof_dir.rglob("*.lean"):
            rel = lean_file.relative_to(ROOT)
            scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
            for i, line in enumerate(scrubbed_lines, 1):
                for cmd in debug_commands:
                    if line_starts_with_command(line, cmd):
                        errors.append(
                            f"{rel}:{i}: found {cmd} in proof file "
                            f"(debug command that slows builds)"
                        )

    # Check 2: Exactly 1 allowUnsafeReducibility
    expected_unsafe = 1
    unsafe_count = 0
    unsafe_locations: list[str] = []
    for lean_file in ROOT.rglob("*.lean"):
        if ".lake" in str(lean_file):
            continue
        rel = lean_file.relative_to(ROOT)
        scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
        for i, line in enumerate(scrubbed_lines, 1):
            if "allowUnsafeReducibility" in line:
                unsafe_count += 1
                unsafe_locations.append(f"{rel}:{i}")

    if unsafe_count != expected_unsafe:
        errors.append(
            f"Expected {expected_unsafe} allowUnsafeReducibility, "
            f"found {unsafe_count}: {unsafe_locations}"
        )

    # Check 3: Fixed sorry baseline after the merged proof-reduction pass.
    # Each allowed sorry is pinned to a specific theorem with an explicit
    # per-theorem limit so redistributing obligations between pinned theorems
    # still fails even if the file-level total stays constant.
    ALLOWED_SORRY_THEOREMS: dict[str, dict[str, int]] = {
        "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean": {
            "exp_natModPow_eq_uint256Exp": 1,
            "sdiv_int256_eq_uint256Sdiv": 1,
            "smod_int256_eq_uint256Smod": 1,
            "sar_int256_eq_uint256Sar": 1,
            "signextend_uint256_eq": 1,
        },
    }
    sorry_count = 0
    sorry_locations: list[str] = []
    unexpected_sorry_locations: list[str] = []
    sorry_per_file: dict[str, int] = {}
    sorry_counts_per_theorem: dict[str, dict[str, int]] = {}
    for lean_file in ROOT.rglob("*.lean"):
        if ".lake" in str(lean_file):
            continue
        rel = lean_file.relative_to(ROOT)
        rel_str = str(rel)
        scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
        for i, line in enumerate(scrubbed_lines, 1):
            if SORRY_RE.search(line):
                sorry_count += 1
                loc = f"{rel}:{i}"
                sorry_locations.append(loc)
                if rel_str not in ALLOWED_SORRY_THEOREMS:
                    unexpected_sorry_locations.append(loc)
                else:
                    sorry_per_file[rel_str] = sorry_per_file.get(rel_str, 0) + 1
                    thm = _find_enclosing_theorem(scrubbed_lines, i - 1)
                    if thm:
                        theorem_counts = sorry_counts_per_theorem.setdefault(rel_str, {})
                        theorem_counts[thm] = theorem_counts.get(thm, 0) + 1
                    else:
                        # sorry not inside any theorem/lemma/def — flag it
                        unexpected_sorry_locations.append(loc)

    if unexpected_sorry_locations:
        errors.append(
            f"Found sorry in non-allowlisted files: {unexpected_sorry_locations}"
        )

    for path, allowed_thm_counts in ALLOWED_SORRY_THEOREMS.items():
        actual = sorry_per_file.get(path, 0)
        allowed_total = sum(allowed_thm_counts.values())
        if actual > allowed_total:
            errors.append(
                f"{path}: found {actual} sorry (cap is {allowed_total})"
            )
        actual_thm_counts = sorry_counts_per_theorem.get(path, {})
        unexpected_thms = set(actual_thm_counts) - set(allowed_thm_counts)
        if unexpected_thms:
            errors.append(
                f"{path}: sorry in non-pinned theorems: "
                f"{sorted(unexpected_thms)} "
                f"(allowed: {sorted(allowed_thm_counts)})"
            )
        over_limit_thms = {
            theorem: count
            for theorem, count in actual_thm_counts.items()
            if count > allowed_thm_counts.get(theorem, 0)
        }
        if over_limit_thms:
            errors.append(
                f"{path}: sorry count exceeds pinned limit: "
                f"{sorted(over_limit_thms.items())} "
                f"(allowed: {sorted(allowed_thm_counts.items())})"
            )

    # Check 4: No native_decide in proof files (except tests/profiles)
    # native_decide bypasses the kernel and is acceptable in:
    #   - Smoke tests (string comparisons against generated code)
    #   - Feature/bridge tests (decidable equality checks across systems)
    #   - Arithmetic profiles (cross-system constant agreement)
    # It is NOT acceptable in mathematical preservation/correctness proofs.
    native_decide_count = 0
    for proof_dir in proof_dirs:
        for lean_file in proof_dir.rglob("*.lean"):
            rel = lean_file.relative_to(ROOT)
            stem = lean_file.stem
            if "Test" in stem or "Profile" in stem:
                continue
            scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
            for i, line in enumerate(scrubbed_lines, 1):
                if "native_decide" in line:
                    native_decide_count += 1
                    errors.append(
                        f"{rel}:{i}: found native_decide in proof file "
                        f"(bypasses kernel — use decide or other tactics)"
                    )

    report_errors(errors, "Lean hygiene check failed")
    print(
        f"Lean hygiene check passed "
        f"(0 debug commands in proofs, {unsafe_count} allowUnsafeReducibility, "
        f"{sorry_count} sorry ({sorry_count - len(unexpected_sorry_locations)} allowed, {len(unexpected_sorry_locations)} unexpected), "
        f"0 native_decide in proofs)."
    )


if __name__ == "__main__":
    main()
