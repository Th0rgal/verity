#!/usr/bin/env python3
"""Minimal DSL -> Solidity constraint harness compiler.

Supported syntax (single contract, single spec):

contract Loan

spec update(address user, uint256 newCollateral, uint256 newDebt):
  ensure: debt[user] == 0 || collateral[user] * 1e18 >= debt[user] * minHealthFactor

  Optional:
    constructor(<params>)
    require: <expr>
    ensure: <expr> (may appear multiple times)
    hint: <text>
    invariant Name: <expr>
    forall <witness>: <pre> => <post>
  old(<expr>) in ensure/require/invariant for pre-state values.

Notes:
- Multiple `ensure:` and `invariant` lines are supported.
- `require:` is optional and can appear multiple times.
- `old(<expr>)` is limited to uint256 expressions for now.
- The spec name must match the implementation function name.
- `forall` compiles into a witness-based require/ensure pair (quantifier intent).
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path


@dataclass
class Spec:
    contract: str
    func_name: str
    params: str
    ensures: list[str]
    requires: list[str]
    hints: list[str]
    ctor_params: str
    invariants: list[tuple[str, str]]
    foralls: list[tuple[str, str, str]]
    spec_path: str


CONTRACT_RE = re.compile(r"^contract\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*$")
CTOR_RE = re.compile(r"^constructor\((?P<params>.*)\)\s*$")
SPEC_RE = re.compile(r"^spec\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)\((?P<params>.*)\):\s*$")
ENSURE_RE = re.compile(r"^ensure:\s*(?P<expr>.+)$")
REQUIRE_RE = re.compile(r"^require:\s*(?P<expr>.+)$")
HINT_RE = re.compile(r"^hint:\s*(?P<text>.+)$")
INVARIANT_RE = re.compile(
    r"^invariant\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*:\s*(?P<expr>.+)$"
)
FORALL_RE = re.compile(
    r"^forall\s+(?P<var>[A-Za-z_][A-Za-z0-9_]*)\s*:\s*(?P<pre>.+?)\s*=>\s*(?P<post>.+)$"
)


def parse_spec(text: str, spec_path: str) -> Spec:
    contract = None
    func_name = None
    params = None
    ensures: list[str] = []
    requires: list[str] = []
    hints: list[str] = []
    ctor_params = ""
    invariants: list[tuple[str, str]] = []
    foralls: list[tuple[str, str, str]] = []

    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if contract is None:
            match = CONTRACT_RE.match(line)
            if match:
                contract = match.group("name")
                continue
        match = CTOR_RE.match(line)
        if match:
            ctor_params = match.group("params").strip()
            continue
        match = SPEC_RE.match(line)
        if match:
            func_name = match.group("name")
            params = match.group("params").strip()
            continue
        match = ENSURE_RE.match(line)
        if match:
            ensures.append(match.group("expr").strip())
        match = REQUIRE_RE.match(line)
        if match:
            requires.append(match.group("expr").strip())
        match = HINT_RE.match(line)
        if match:
            hints.append(match.group("text").strip())
        match = INVARIANT_RE.match(line)
        if match:
            invariants.append((match.group("name"), match.group("expr").strip()))
        match = FORALL_RE.match(line)
        if match:
            foralls.append(
                (
                    match.group("var"),
                    match.group("pre").strip(),
                    match.group("post").strip(),
                )
            )

    missing = []
    if contract is None:
        missing.append("contract")
    if func_name is None:
        missing.append("spec")
    if missing:
        raise ValueError(f"Missing required fields: {', '.join(missing)}")
    if not ensures and not invariants and not foralls:
        raise ValueError("Missing required fields: ensure or invariant")

    return Spec(
        contract=contract,
        func_name=func_name,
        params=params or "",
        ensures=ensures,
        requires=requires,
        hints=hints,
        ctor_params=ctor_params,
        invariants=invariants,
        foralls=foralls,
        spec_path=spec_path,
    )


def render(spec: Spec) -> str:
    harness = f"{spec.contract}SpecHarness"
    forall_requires = [pre for _, pre, _ in spec.foralls]
    forall_ensures = [post for _, _, post in spec.foralls]
    forall_hints = [
        f"forall witness {var}: {pre} => {post}" for var, pre, post in spec.foralls
    ]
    all_exprs = (
        spec.requires
        + spec.ensures
        + forall_requires
        + forall_ensures
        + [expr for _, expr in spec.invariants]
    )
    old_map = _old_map(all_exprs)
    requires = [_sub_old(req, old_map) for req in spec.requires + forall_requires]
    ensures = [_sub_old(expr, old_map) for expr in spec.ensures + forall_ensures]
    invariants = [(name, _sub_old(expr, old_map)) for name, expr in spec.invariants]
    old_decls = _render_old_decls(old_map)
    hints = _render_hints(spec.hints + forall_hints)
    ctor_args = ", ".join(_param_names(spec.ctor_params))
    return f"""// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Generated by research/poc_constraints/dsl_to_constraints.py from {spec.spec_path}

import {{{spec.contract}}} from "./{spec.contract}.sol";

contract {harness} is {spec.contract} {{
    constructor({spec.ctor_params}) {spec.contract}({ctor_args}) {{}}

    function {spec.func_name}_spec({spec.params}) external {{
 {old_decls}{_render_requires(requires)}{hints}
        super.{spec.func_name}({', '.join(_param_names(spec.params))});
 {_render_asserts(ensures, invariants)}
    }}
}}
"""


def _param_names(params: str) -> list[str]:
    if not params.strip():
        return []
    parts = [p.strip() for p in params.split(",")]
    names = []
    for part in parts:
        tokens = [t for t in part.split(" ") if t]
        if not tokens:
            continue
        names.append(tokens[-1])
    return names


def _old_map(exprs: list[str]) -> dict[str, str]:
    old_map: dict[str, str] = {}
    for expr in exprs:
        for match in re.finditer(r"old\(([^)]+)\)", expr):
            inner = match.group(1).strip()
            if inner in old_map:
                continue
            sanitized = re.sub(r"[^A-Za-z0-9_]", "_", inner).strip("_")
            if not sanitized:
                sanitized = f"value_{len(old_map)}"
            name = f"old_{sanitized}"
            suffix = 1
            while name in old_map.values():
                suffix += 1
                name = f"old_{sanitized}_{suffix}"
            old_map[inner] = name
    return old_map


def _render_old_decls(old_map: dict[str, str]) -> str:
    if not old_map:
        return ""
    lines = []
    for expr, name in old_map.items():
        lines.append(f"        uint256 {name} = {expr};")
    return "\n".join(lines) + "\n"


def _sub_old(expr: str, old_map: dict[str, str]) -> str:
    def repl(match: re.Match[str]) -> str:
        inner = match.group(1).strip()
        return old_map.get(inner, match.group(0))

    return re.sub(r"old\(([^)]+)\)", repl, expr)


def _render_requires(requires: list[str]) -> str:
    if not requires:
        return ""
    lines = [f"        require({expr});" for expr in requires]
    return "\n".join(lines) + "\n"


def _render_hints(hints: list[str]) -> str:
    if not hints:
        return ""
    lines = [f"        // hint: {text}" for text in hints]
    return "\n".join(lines) + "\n"


def _render_asserts(ensures: list[str], invariants: list[tuple[str, str]]) -> str:
    lines = []
    for expr in ensures:
        lines.append(f"        assert({expr});")
    for name, expr in invariants:
        lines.append(f"        // invariant {name}")
        lines.append(f"        assert({expr});")
    return "\n".join(lines) + ("\n" if lines else "")


def main() -> int:
    if len(sys.argv) != 3:
        print("Usage: dsl_to_constraints.py <spec.dc> <output.sol>")
        return 1

    spec_path = Path(sys.argv[1])
    out_path = Path(sys.argv[2])
    text = spec_path.read_text(encoding="utf-8")

    spec = parse_spec(text, str(spec_path))
    out_path.write_text(render(spec), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
