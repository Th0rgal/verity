#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[refresh] Regenerating verification status artifact"
python3 scripts/generate_verification_status.py

echo "[refresh] Auto-fixing stale doc counts"
python3 scripts/check_doc_counts.py --fix

echo "[refresh] Validating refreshed artifacts"
python3 scripts/check_doc_counts.py
python3 scripts/generate_verification_status.py --check

echo "[refresh] PASS"
