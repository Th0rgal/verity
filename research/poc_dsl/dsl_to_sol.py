#!/usr/bin/env python3
"""Minimal DSL -> Solidity skeleton (POC).

This parser is intentionally small and only supports the demo DSL in specs/token.dc.
"""
from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional


@dataclass
class Spec:
    name: str
    args: List[str]
    requires: List[str]
    ensures: List[str]


@dataclass
class Invariant:
    name: str
    lines: List[str]


def parse_dsl(text: str):
    lines = text.splitlines()
    invariants: List[Invariant] = []
    specs: List[Spec] = []
    i = 0
    while i < len(lines):
        line = lines[i].rstrip("\n")
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            i += 1
            continue
        if stripped.startswith("invariant "):
            name = stripped[len("invariant "):].rstrip(":")
            i += 1
            body: List[str] = []
            while i < len(lines) and lines[i].startswith("  "):
                body.append(lines[i].strip())
                i += 1
            invariants.append(Invariant(name=name, lines=body))
            continue
        if stripped.startswith("spec "):
            header = stripped[len("spec "):].rstrip(":")
            m = re.match(r"([A-Za-z_][A-Za-z0-9_]*)\((.*)\)", header)
            if not m:
                raise ValueError(f"Invalid spec header: {header}")
            name = m.group(1)
            args = [a.strip() for a in m.group(2).split(",") if a.strip()]
            requires: List[str] = []
            ensures: List[str] = []
            mode: Optional[str] = None
            i += 1
            while i < len(lines):
                raw = lines[i]
                if not raw.strip():
                    i += 1
                    continue
                if raw.strip().startswith("spec ") or raw.strip().startswith("invariant "):
                    break
                if raw.strip().startswith("require:"):
                    mode = "require"
                    i += 1
                    continue
                if raw.strip().startswith("ensure:"):
                    mode = "ensure"
                    i += 1
                    continue
                if raw.startswith("  ") and mode == "require":
                    requires.append(raw.strip())
                    i += 1
                    continue
                if raw.startswith("  ") and mode == "ensure":
                    ensures.append(raw.strip())
                    i += 1
                    continue
                i += 1
            specs.append(Spec(name=name, args=args, requires=requires, ensures=ensures))
            continue
        i += 1
    return invariants, specs


def translate_ensure(expr: str) -> Optional[str]:
    if expr.startswith("forall "):
        return None
    replacements = {
        "old(balance[from])": "old_balance_from",
        "old(balance[to])": "old_balance_to",
        "old(totalSupply)": "old_totalSupply",
    }
    for src, dst in replacements.items():
        expr = expr.replace(src, dst)
    return expr


def render_solidity(invariants: List[Invariant], specs: List[Spec]) -> str:
    lines: List[str] = []
    lines.append("// SPDX-License-Identifier: UNLICENSED")
    lines.append("pragma solidity ^0.8.24;")
    lines.append("")
    lines.append("// AUTO-GENERATED POC: DO NOT USE IN PRODUCTION")
    lines.append("contract DumbTokenSpec {")
    lines.append("    mapping(address => uint256) public balance;")
    lines.append("    uint256 public totalSupply;")
    lines.append("")
    if invariants:
        lines.append("    // Invariants (not enforced on-chain in this POC):")
        for inv in invariants:
            joined = " ".join(inv.lines)
            lines.append(f"    // - {inv.name}: {joined}")
        lines.append("")

    for spec in specs:
        args = ["address from", "address to", "uint256 amount"]
        if spec.args:
            args = []
            for arg in spec.args:
                if arg in {"from", "to"}:
                    args.append(f"address {arg}")
                else:
                    args.append(f"uint256 {arg}")
        signature = ", ".join(args)
        lines.append(f"    function {spec.name}({signature}) external {{")
        lines.append("        uint256 old_balance_from = balance[from];")
        lines.append("        uint256 old_balance_to = balance[to];")
        lines.append("        uint256 old_totalSupply = totalSupply;")
        lines.append("")
        for req in spec.requires:
            lines.append(f"        require({req}, \"require failed\");")
        lines.append("")
        lines.append("        // Implementation hint: apply the minimal state diff")
        lines.append("        balance[from] = old_balance_from - amount;")
        lines.append("        balance[to] = old_balance_to + amount;")
        lines.append("")
        for ens in spec.ensures:
            translated = translate_ensure(ens)
            if translated is None:
                lines.append(f"        // TODO: enforce quantified postcondition: {ens}")
            else:
                lines.append(f"        assert({translated});")
        lines.append("")
        lines.append("        // Reference to preserve supply conservation if applicable")
        lines.append("        assert(totalSupply == old_totalSupply);")
        lines.append("    }")
        lines.append("")

    lines.append("}")
    return "\n".join(lines)


def main() -> int:
    if len(sys.argv) != 3:
        print("Usage: dsl_to_sol.py <input.dc> <output.sol>")
        return 2
    input_path = Path(sys.argv[1])
    output_path = Path(sys.argv[2])
    text = input_path.read_text(encoding="utf-8")
    invariants, specs = parse_dsl(text)
    solidity = render_solidity(invariants, specs)
    output_path.write_text(solidity, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
