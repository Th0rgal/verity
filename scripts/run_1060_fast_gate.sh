#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

WITH_BUILD="false"

if [[ "${1:-}" == "--with-build" ]]; then
  WITH_BUILD="true"
fi

echo "[1060-fast-gate] Refreshing verification artifact"
python3 scripts/generate_verification_status.py

echo "[1060-fast-gate] Validating docs and integrity ledger"
python3 scripts/check_doc_counts.py
python3 scripts/check_issue_1060_integrity.py

echo "[1060-fast-gate] Verifying artifact freshness"
python3 scripts/generate_verification_status.py --check

if [[ "$WITH_BUILD" == "true" ]]; then
  echo "[1060-fast-gate] Running lake build"
  lake build
fi

echo "[1060-fast-gate] Running focused integrity tests"
python3 -m unittest scripts/test_check_issue_1060_integrity.py -v

echo "[1060-fast-gate] PASS"
