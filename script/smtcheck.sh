#!/usr/bin/env bash
set -euo pipefail

IMAGE="ethereum/solc:0.8.20"

if ! command -v docker >/dev/null 2>&1; then
  echo "docker is required to run SMTChecker in this POC" >&2
  exit 1
fi

docker run --rm -v "$PWD":/src -w /src \
  "$IMAGE" \
  --model-checker-engine chc \
  --model-checker-targets assert \
  --model-checker-timeout 0 \
  src/LoanSpecHarness.sol
