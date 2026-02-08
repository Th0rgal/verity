#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="/opt/lean-4.27.0/bin:$PATH"

cd "$ROOT"

lake build
lake exe dumbcontracts
