#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[refresh] Regenerating verification status artifact"
python3 scripts/generate_verification_status.py
python3 scripts/generate_layer2_boundary_catalog.py

echo "[refresh] Validating refreshed artifacts"
python3 scripts/generate_verification_status.py --check
python3 scripts/generate_layer2_boundary_catalog.py --check
python3 scripts/check_verification_status_doc.py
python3 scripts/check_layer2_boundary_catalog_sync.py

echo "[refresh] PASS"
