#!/usr/bin/env bash
set -euo pipefail

IMAGE="ethereum/solc:0.8.20"

if ! command -v docker >/dev/null 2>&1; then
  echo "docker is required to run SMTChecker in this POC" >&2
  exit 1
fi

if ! docker info >/dev/null 2>&1; then
  echo "docker is installed but the daemon is not running (cannot reach /var/run/docker.sock)" >&2
  exit 1
fi

docker run --rm -v "$PWD":/src -w /src \
  "$IMAGE" \
  --model-checker-engine chc \
  --model-checker-targets assert \
  --model-checker-timeout 0 \
  src/LoanSpecHarness.sol

docker run --rm -v "$PWD":/src -w /src \
  "$IMAGE" \
  --model-checker-engine chc \
  --model-checker-targets assert \
  --model-checker-timeout 0 \
  src/SimpleTokenSpecHarness.sol

docker run --rm -v "$PWD":/src -w /src \
  "$IMAGE" \
  --model-checker-engine chc \
  --model-checker-targets assert \
  --model-checker-timeout 0 \
  src/MintableTokenSpecHarness.sol

docker run --rm -v "$PWD":/src -w /src \
  "$IMAGE" \
  --model-checker-engine chc \
  --model-checker-targets assert \
  --model-checker-timeout 0 \
  src/CappedTokenSpecHarness.sol
