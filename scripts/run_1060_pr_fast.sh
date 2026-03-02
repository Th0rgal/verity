#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[1060-pr-fast] deprecated; forwarding to strict pr-sync"
exec scripts/run_1060_pr_sync.sh "$@"
