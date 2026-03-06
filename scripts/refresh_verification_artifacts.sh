#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[refresh] Regenerating verification status artifact"
python3 scripts/generate_verification_status.py

echo "[refresh] Validating refreshed artifacts"
python3 scripts/generate_verification_status.py --check
python3 scripts/check_verification_status_doc.py

echo "[refresh] PASS"
