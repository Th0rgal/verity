#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

WITH_BUILD="false"
CHANGED_ONLY="false"
BASE_REF="origin/main"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --with-build)
      WITH_BUILD="true"
      ;;
    --changed-only)
      CHANGED_ONLY="true"
      ;;
    --base-ref)
      BASE_REF="${2:-}"
      shift
      ;;
    *)
      echo "unknown option: $1" >&2
      echo "usage: $0 [--with-build] [--changed-only] [--base-ref <ref>]" >&2
      exit 1
      ;;
  esac
  shift
done

run_doc_checks="true"
run_integrity_tests="true"
run_artifact_refresh="true"

if [[ "$CHANGED_ONLY" == "true" ]]; then
  echo "[1060-fast-gate] changed-only mode against $BASE_REF"
  mapfile -t CHANGED_FILES < <(git diff --name-only "$BASE_REF"...HEAD || true)
  if [[ ${#CHANGED_FILES[@]} -eq 0 ]]; then
    echo "[1060-fast-gate] No changed files detected; running full fast gate for safety."
  else
    run_doc_checks="false"
    run_integrity_tests="false"
    run_artifact_refresh="false"
    for path in "${CHANGED_FILES[@]}"; do
      case "$path" in
        docs/*|docs-site/*|README.md|TRUST_ASSUMPTIONS.md|AXIOMS.md|artifacts/verification_status.json)
          run_doc_checks="true"
          run_artifact_refresh="true"
          ;;
      esac
      case "$path" in
        artifacts/issue_1060_progress.json|scripts/check_issue_1060_integrity.py|scripts/test_check_issue_1060_integrity.py)
          run_integrity_tests="true"
          ;;
      esac
    done
    # Integrity checker must always run for #1060 loop.
    run_integrity_tests="true"
  fi
fi

if [[ "$run_artifact_refresh" == "true" ]]; then
  echo "[1060-fast-gate] Refreshing verification artifact"
  python3 scripts/generate_verification_status.py
else
  echo "[1060-fast-gate] Skipping artifact refresh (no doc/artifact changes)"
fi

if [[ "$run_doc_checks" == "true" ]]; then
  echo "[1060-fast-gate] Validating docs"
  python3 scripts/check_doc_counts.py
else
  echo "[1060-fast-gate] Skipping doc count check (no doc changes)"
fi

echo "[1060-fast-gate] Validating integrity ledger"
python3 scripts/check_issue_1060_integrity.py

if [[ "$run_artifact_refresh" == "true" ]]; then
  echo "[1060-fast-gate] Verifying artifact freshness"
  python3 scripts/generate_verification_status.py --check
fi

if [[ "$WITH_BUILD" == "true" ]]; then
  echo "[1060-fast-gate] Running lake build"
  lake build
fi

if [[ "$run_integrity_tests" == "true" ]]; then
  echo "[1060-fast-gate] Running focused integrity tests"
  python3 -m unittest scripts/test_check_issue_1060_integrity.py -v
fi

echo "[1060-fast-gate] PASS"
