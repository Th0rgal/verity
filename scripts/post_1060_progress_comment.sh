#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

if [[ $# -lt 1 ]]; then
  echo "usage: $0 <item-id> [--dry-run]" >&2
  exit 1
fi

ITEM_ID="$1"
DRY_RUN="false"
if [[ "${2:-}" == "--dry-run" ]]; then
  DRY_RUN="true"
fi

TMP_BODY="$(mktemp)"
python3 - "$ITEM_ID" "$TMP_BODY" <<'PY'
from __future__ import annotations
import json
import sys
from pathlib import Path

item_id = sys.argv[1]
out_path = Path(sys.argv[2])
ledger = Path("artifacts/issue_1060_progress.json")

data = json.loads(ledger.read_text(encoding="utf-8"))
items = data.get("items", {})
entry = items.get(item_id)
if entry is None:
    raise SystemExit(f"unknown item id: {item_id}")

def lines(label: str, values: list[str]) -> str:
    if not values:
        return f"- **{label}**: none"
    text = [f"- **{label}**:"]
    text.extend([f"  - {v}" for v in values])
    return "\n".join(text)

status = str(entry.get("status", "open"))
criteria = [str(x) for x in entry.get("acceptance_criteria", [])]
files_changed = [str(x) for x in entry.get("files_changed", [])]
verify_cmds = [str(x) for x in entry.get("verification_commands", [])]
verify_results = [str(x) for x in entry.get("verification_results", [])]
theorem_names = [str(t.get("name", "")) for t in entry.get("evidence", {}).get("theorems", []) if isinstance(t, dict) and t.get("name")]
test_evidence = [str(x) for x in entry.get("evidence", {}).get("tests", [])]
notes = str(entry.get("notes", "")).strip()

body = []
body.append(f"<!-- issue-1060-progress:{item_id} -->")
body.append(f"### Issue #1060 Progress: Item {item_id} ({status})")
body.append(lines("Acceptance criteria", criteria))
body.append(lines("Files changed", files_changed))
body.append(lines("Verification commands", verify_cmds))
body.append(lines("Verification results", verify_results))
body.append(lines("Theorem evidence", theorem_names))
body.append(lines("Test evidence", test_evidence))
if notes:
    body.append(f"- **Risks/follow-ups**: {notes}")
else:
    body.append("- **Risks/follow-ups**: none recorded")

out_path.write_text("\n\n".join(body) + "\n", encoding="utf-8")
print(str(out_path))
PY

if [[ "$DRY_RUN" == "true" ]]; then
  echo "[post-1060-comment] dry run body:"
  cat "$TMP_BODY"
  rm -f "$TMP_BODY"
  exit 0
fi

gh pr comment 1065 --repo Th0rgal/verity --body-file "$TMP_BODY"
echo "[post-1060-comment] posted comment for item $ITEM_ID"
rm -f "$TMP_BODY"
