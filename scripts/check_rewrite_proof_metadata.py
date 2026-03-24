#!/usr/bin/env python3
"""Fail closed when shipped rewrite proof metadata is missing or stale.

Checks:
- Active shipped rewrite rules declare non-empty `proofId`.
- `proofId` may be a string literal, a quoted Lean name, or a def alias.
- Resolved proof refs point at real Lean declarations in the repo.
- Shipped parity packs carry resolvable composition-proof refs that also exist.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT, report_errors, strip_lean_comments

PATCH_RULES_DIR = ROOT / "Compiler" / "Yul" / "PatchRulesCatalog"
PARITY_PACKS_PATH = ROOT / "Compiler" / "ParityPacks.lean"
BUNDLES_TO_CHECK = ["foundationRewriteBundle", "solcCompatRewriteBundle"]
_DEF_STRING_RE = re.compile(r'^\s*def\s+([A-Za-z_][A-Za-z0-9_\']*)\s*:\s*String\s*:=\s*"([^"]*)"', re.MULTILINE)
_DEF_NAME_RE = re.compile(r"^\s*def\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*Lean\.Name\s*:=\s*``([A-Za-z0-9_.']+)", re.MULTILINE)
_DEF_NAME_FROM_HELPER_RE = re.compile(
    r'^\s*def\s+([A-Za-z_][A-Za-z0-9_\']*)\s*:\s*Lean\.Name\s*:=\s*(?:[A-Za-z_][A-Za-z0-9_.\']*\.)?proofRefName\s*"([^"]*)"',
    re.MULTILINE,
)
_DECL_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*"
    r"(?:def|theorem|lemma|abbrev|opaque|axiom)\s+([A-Za-z_][A-Za-z0-9_.']*)\b"
)
_NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$")
_SECTION_RE = re.compile(r"^\s*section(?:\s+[A-Za-z_][A-Za-z0-9_.']*)?\s*$")
_END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_.']*))?\s*$")
_STRUCT_DEF_RE = r"\bdef\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*{type_name}\s*:=\s*\{{"
_LIST_DEF_RE = r"\bdef\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*List\s+{type_name}\s*:="
_RULE_KINDS = {
    "exprRules": "ExprPatchRule",
    "stmtRules": "StmtPatchRule",
    "blockRules": "BlockPatchRule",
    "objectRules": "ObjectPatchRule",
}


def _find_matching_delim(text: str, start: int, open_ch: str, close_ch: str) -> int:
    depth = 0
    i = start
    in_string = False
    escape = False
    while i < len(text):
        ch = text[i]
        if in_string:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if ch == '"':
            in_string = True
            i += 1
            continue
        if ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return i
        i += 1
    raise ValueError(f"Unbalanced delimiters: missing {close_ch!r} for {open_ch!r} at index {start}")


def _extract_rule_proof_tokens(text: str, type_name: str) -> dict[str, str]:
    rules: dict[str, str] = {}
    rule_re = re.compile(_STRUCT_DEF_RE.format(type_name=re.escape(type_name)))
    for match in rule_re.finditer(text):
        rule_name = match.group(1)
        open_brace = text.find("{", match.end() - 1)
        if open_brace < 0:
            raise ValueError(f"Could not locate opening '{{' for {type_name} rule {rule_name}")
        close_brace = _find_matching_delim(text, open_brace, "{", "}")
        block = text[open_brace : close_brace + 1]
        proof_match = re.search(r"\bproofId\s*:=\s*([^,\n]+)", block)
        if proof_match is None:
            rules[rule_name] = ""
            continue
        rules[rule_name] = proof_match.group(1).strip()
    return rules


def _extract_ref_defs(text: str) -> dict[str, str]:
    out = {name: value for name, value in _DEF_STRING_RE.findall(text)}
    out.update({name: value for name, value in _DEF_NAME_RE.findall(text)})
    out.update({name: value for name, value in _DEF_NAME_FROM_HELPER_RE.findall(text)})
    return out


def _extract_bundle_block(text: str, bundle_name: str) -> str:
    start_match = re.search(
        rf"\bdef\s+{re.escape(bundle_name)}\s*:\s*RewriteRuleBundle\s*:=\s*\{{",
        text,
    )
    if start_match is None:
        raise ValueError(f"Missing bundle definition: {bundle_name}")
    open_brace = text.find("{", start_match.end() - 1)
    if open_brace < 0:
        raise ValueError(f"Could not locate opening '{{' for bundle {bundle_name}")
    close_brace = _find_matching_delim(text, open_brace, "{", "}")
    return text[open_brace : close_brace + 1]


def _extract_struct_fields(block: str) -> dict[str, str]:
    if not (block.startswith("{") and block.endswith("}")):
        raise ValueError(f"Expected struct block, got: {block[:32]!r}")

    field_re = re.compile(r"^([A-Za-z_][A-Za-z0-9_']*)\s*:=\s*(.*)$")
    body_lines = block[1:-1].splitlines()
    fields: dict[str, str] = {}
    current_name: str | None = None
    current_parts: list[str] = []
    depth_round = 0
    depth_square = 0
    depth_curly = 0
    in_string = False
    escape = False

    def ingest(text: str) -> None:
        nonlocal depth_round, depth_square, depth_curly, in_string, escape
        for ch in text:
            if in_string:
                if escape:
                    escape = False
                elif ch == "\\":
                    escape = True
                elif ch == '"':
                    in_string = False
                continue
            if ch == '"':
                in_string = True
                continue
            if ch == "(":
                depth_round += 1
            elif ch == ")":
                depth_round = max(0, depth_round - 1)
            elif ch == "[":
                depth_square += 1
            elif ch == "]":
                depth_square = max(0, depth_square - 1)
            elif ch == "{":
                depth_curly += 1
            elif ch == "}":
                depth_curly = max(0, depth_curly - 1)

    for raw_line in body_lines:
        stripped = raw_line.strip()
        if not stripped:
            continue
        next_field = field_re.match(stripped)
        if current_name is None:
            if next_field is None:
                continue
            current_name = next_field.group(1)
            current_parts = [next_field.group(2)]
            depth_round = depth_square = depth_curly = 0
            in_string = False
            escape = False
            ingest(next_field.group(2))
            continue

        if depth_round == 0 and depth_square == 0 and depth_curly == 0 and next_field is not None:
            fields[current_name] = "\n".join(current_parts).strip().rstrip(",")
            current_name = next_field.group(1)
            current_parts = [next_field.group(2)]
            depth_round = depth_square = depth_curly = 0
            in_string = False
            escape = False
            ingest(next_field.group(2))
            continue

        current_parts.append(stripped)
        ingest(stripped)

    if current_name is not None:
        fields[current_name] = "\n".join(current_parts).strip().rstrip(",")
    return fields


def _split_top_level_concat(expr: str) -> list[str]:
    parts: list[str] = []
    depth_round = 0
    depth_square = 0
    depth_curly = 0
    in_string = False
    escape = False
    start = 0
    i = 0
    while i < len(expr):
        ch = expr[i]
        nxt = expr[i + 1] if i + 1 < len(expr) else ""
        if in_string:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if ch == '"':
            in_string = True
            i += 1
            continue
        if ch == "(":
            depth_round += 1
        elif ch == ")":
            depth_round = max(0, depth_round - 1)
        elif ch == "[":
            depth_square += 1
        elif ch == "]":
            depth_square = max(0, depth_square - 1)
        elif ch == "{":
            depth_curly += 1
        elif ch == "}":
            depth_curly = max(0, depth_curly - 1)
        elif (
            ch == "+"
            and nxt == "+"
            and depth_round == 0
            and depth_square == 0
            and depth_curly == 0
        ):
            parts.append(expr[start:i].strip())
            i += 2
            start = i
            continue
        i += 1
    tail = expr[start:].strip()
    if tail:
        parts.append(tail)
    return parts


def _extract_pack_defs(text: str, type_name: str) -> dict[str, str]:
    out: dict[str, str] = {}
    pack_re = re.compile(_LIST_DEF_RE.format(type_name=re.escape(type_name)), re.MULTILINE)
    for match in pack_re.finditer(text):
        name = match.group(1)
        pos = match.end()
        while pos < len(text) and text[pos].isspace():
            pos += 1
        if pos >= len(text):
            raise ValueError(f"Missing value expression for object pack {name}")
        if text[pos] == "[":
            end = _find_matching_delim(text, pos, "[", "]")
            out[name] = text[pos : end + 1].strip()
        else:
            line_end = text.find("\n", pos)
            if line_end == -1:
                line_end = len(text)
            out[name] = text[pos:line_end].strip()
    return out


def _extract_rules_from_expression(
    expr: str,
    pack_defs: dict[str, str],
    *,
    stack: set[str] | None = None,
) -> list[str]:
    names: list[str] = []
    stack = set() if stack is None else stack
    for part in _split_top_level_concat(expr):
        if part.startswith("[") and part.endswith("]"):
            names.extend(re.findall(r"\b([A-Za-z_][A-Za-z0-9_']*)\b", part[1:-1]))
            continue
        ident_match = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_']*)", part)
        if ident_match is None:
            raise ValueError(f"Unsupported rule expression segment: {part!r}")
        ident = ident_match.group(1)
        if ident in pack_defs:
            if ident in stack:
                raise ValueError(f"Cyclic patch pack definition: {ident}")
            nested = _extract_rules_from_expression(pack_defs[ident], pack_defs, stack=stack | {ident})
            names.extend(nested)
        else:
            names.append(ident)
    return names


def _extract_rules_from_bundle(
    bundle_block: str,
    field_name: str,
    pack_defs: dict[str, str],
) -> list[str]:
    fields = _extract_struct_fields(bundle_block)
    expr = fields.get(field_name)
    if expr is None:
        raise ValueError(f"Bundle block missing {field_name} field")
    return _extract_rules_from_expression(expr, pack_defs)


def _resolve_proof_ref(token: str, ref_defs: dict[str, str]) -> str:
    token = token.strip()
    if token == ".anonymous":
        return ""
    helper_match = re.fullmatch(r'(?:[A-Za-z_][A-Za-z0-9_.\']*\.)?proofRefName\s*"([^"]*)"', token)
    if helper_match is not None:
        return helper_match.group(1)
    if token.startswith("``"):
        return token[2:]
    if token.startswith('"') and token.endswith('"') and len(token) >= 2:
        return token[1:-1]
    return ref_defs.get(token, "")


def _collect_decl_names(root: Path) -> set[str]:
    decl_names: set[str] = set()
    if root.is_file():
        lean_paths = [root]
    else:
        lean_paths = sorted(root.rglob("*.lean"))
    for path in lean_paths:
        text = strip_lean_comments(path.read_text(encoding="utf-8"))
        namespaces: list[str] = []
        scopes: list[str] = []
        for line in text.splitlines():
            namespace_match = _NAMESPACE_RE.match(line)
            if namespace_match:
                name = namespace_match.group(1)
                namespaces.append(f"{namespaces[-1]}.{name}" if namespaces else name)
                scopes.append("namespace")
                continue
            if _SECTION_RE.match(line):
                scopes.append("section")
                continue
            end_match = _END_RE.match(line)
            if end_match:
                if scopes:
                    scope = scopes.pop()
                else:
                    scope = ""
                if scope == "namespace" and namespaces:
                    namespaces.pop()
                continue
            decl_match = _DECL_RE.match(line)
            if decl_match is None:
                continue
            name = decl_match.group(1)
            if namespaces and not name.startswith(f"{namespaces[-1]}."):
                decl_names.add(f"{namespaces[-1]}.{name}")
            decl_names.add(name)
    return decl_names


def _read_lean_sources(path: Path) -> str:
    """Read a single .lean file or concatenate all .lean files in a directory."""
    if path.is_file():
        return path.read_text(encoding="utf-8")
    if path.is_dir():
        parts = []
        for p in sorted(path.rglob("*.lean")):
            parts.append(p.read_text(encoding="utf-8"))
        return "\n".join(parts)
    raise ValueError(f"Path does not exist: {path}")


def _check_active_bundle_rule_proofs(path: Path, decl_root: Path) -> list[str]:
    if not path.exists():
        raise ValueError(f"Missing PatchRules path: {path}")

    text = strip_lean_comments(_read_lean_sources(path))
    ref_defs = _extract_ref_defs(text)
    decl_names = _collect_decl_names(decl_root)
    rule_tokens_by_kind = {
        field_name: _extract_rule_proof_tokens(text, type_name)
        for field_name, type_name in _RULE_KINDS.items()
    }
    pack_defs_by_kind = {
        field_name: _extract_pack_defs(text, type_name)
        for field_name, type_name in _RULE_KINDS.items()
    }

    errors: list[str] = []
    for bundle_name in BUNDLES_TO_CHECK:
        bundle_block = _extract_bundle_block(text, bundle_name)
        for field_name, type_name in _RULE_KINDS.items():
            active_rules = _extract_rules_from_bundle(bundle_block, field_name, pack_defs_by_kind[field_name])
            for rule_name in active_rules:
                tokens = rule_tokens_by_kind[field_name]
                if rule_name not in tokens:
                    errors.append(
                        f"{bundle_name}: {field_name} entry {rule_name!r} is not defined as {type_name}"
                    )
                    continue
                token = tokens[rule_name]
                if not token:
                    errors.append(f"{bundle_name}: {rule_name} missing proofId field")
                    continue
                proof_ref = _resolve_proof_ref(token, ref_defs)
                if not proof_ref:
                    errors.append(
                        f"{bundle_name}: {rule_name} has unresolved or empty proofId token {token!r}"
                    )
                    continue
                if proof_ref not in decl_names:
                    errors.append(
                        f"{bundle_name}: {rule_name} references missing proof declaration {proof_ref!r}"
                    )

    return errors


def _extract_parity_pack_blocks(text: str) -> dict[str, str]:
    pack_re = re.compile(_STRUCT_DEF_RE.format(type_name="ParityPack"))
    packs: dict[str, str] = {}
    for match in pack_re.finditer(text):
        pack_name = match.group(1)
        open_brace = text.find("{", match.end() - 1)
        if open_brace < 0:
            raise ValueError(f"Could not locate opening '{{' for parity pack {pack_name}")
        close_brace = _find_matching_delim(text, open_brace, "{", "}")
        packs[pack_name] = text[open_brace : close_brace + 1]
    return packs


def _check_parity_pack_proof_refs(path: Path, decl_root: Path) -> list[str]:
    if not path.exists():
        raise ValueError(f"Missing ParityPacks file: {path}")

    text = strip_lean_comments(path.read_text(encoding="utf-8"))
    ref_defs = _extract_ref_defs(text)
    decl_names = _collect_decl_names(decl_root)

    errors: list[str] = []
    for pack_name, block in _extract_parity_pack_blocks(text).items():
        fields = _extract_struct_fields(block)
        token = fields.get("compositionProofRef", "")
        if not token:
            errors.append(f"{pack_name}: missing compositionProofRef field")
            continue
        proof_ref = _resolve_proof_ref(token, ref_defs)
        if not proof_ref:
            errors.append(f"{pack_name}: unresolved or empty compositionProofRef token {token!r}")
            continue
        if proof_ref not in decl_names:
            errors.append(f"{pack_name}: references missing composition proof declaration {proof_ref!r}")

    return errors


def check_active_object_rule_proofs(path: Path, decl_root: Path = ROOT) -> list[str]:
    return _check_active_bundle_rule_proofs(path, decl_root)


def main() -> int:
    try:
        decl_root = ROOT / "Compiler"
        errors = _check_active_bundle_rule_proofs(PATCH_RULES_DIR, decl_root)
        errors.extend(_check_parity_pack_proof_refs(PARITY_PACKS_PATH, decl_root))
    except ValueError as exc:
        print(f"Rewrite proof metadata check failed: {exc}", file=sys.stderr)
        return 1

    report_errors(errors, "Rewrite proof metadata check failed")
    print("Rewrite proof metadata check passed (shipped proof refs resolve to real Lean declarations).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
