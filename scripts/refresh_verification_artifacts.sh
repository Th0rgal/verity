#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[refresh] Regenerating all derived artifacts"
python3 scripts/generate_verification_status.py
python3 scripts/generate_layer2_boundary_catalog.py
python3 scripts/generate_verify_sync_spec.py
python3 scripts/generate_evmyullean_capability_report.py
python3 scripts/generate_evmyullean_adapter_report.py
python3 scripts/generate_print_axioms.py

echo "[refresh] Validating refreshed artifacts"
python3 scripts/generate_verification_status.py --check
python3 scripts/generate_layer2_boundary_catalog.py --check
python3 scripts/generate_verify_sync_spec.py --check
python3 scripts/generate_evmyullean_capability_report.py --check
python3 scripts/generate_evmyullean_adapter_report.py --check
python3 scripts/generate_print_axioms.py --check
python3 scripts/check_verification_status_doc.py
python3 scripts/check_layer2_boundary_catalog_sync.py

echo "[refresh] PASS"
