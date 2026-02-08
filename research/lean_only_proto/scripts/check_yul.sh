#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "usage: $0 <yul-file>" >&2
  exit 2
fi

if ! command -v solc >/dev/null 2>&1; then
  echo "solc not found. Install Solidity compiler and re-run." >&2
  exit 1
fi

solc --strict-assembly "$1"
