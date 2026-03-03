#!/bin/bash
# Test differential tests with multiple random seeds to detect flakiness
#
# Usage:
#   ./scripts/test_multiple_seeds.sh              # Test with default seeds
#   ./scripts/test_multiple_seeds.sh 1 2 3 4 5    # Test with custom seeds
#
# This script runs the full test suite with different random seeds to detect
# seed-dependent test failures that could indicate flakiness or edge cases.

set -euo pipefail

# Default seeds (same as CI)
DEFAULT_SEEDS=(0 1 42 123 999 12345 67890)

# Use custom seeds if provided, otherwise use defaults
if [ $# -gt 0 ]; then
    SEEDS=("$@")
else
    SEEDS=("${DEFAULT_SEEDS[@]}")
fi

FAILED_SEEDS=()

echo "======================================"
echo "Multi-Seed Differential Testing"
echo "======================================"
echo "Testing with ${#SEEDS[@]} different seeds:"
echo "${SEEDS[*]}"
echo ""

for seed in "${SEEDS[@]}"; do
    echo "--------------------------------------"
    echo "Testing seed: $seed"
    echo "--------------------------------------"

    if FOUNDRY_PROFILE=difftest DIFFTEST_RANDOM_SEED="$seed" DIFFTEST_SHARD_COUNT=1 DIFFTEST_SHARD_INDEX=0 DIFFTEST_RANDOM_SMALL=100 DIFFTEST_RANDOM_LARGE=10000 forge test; then
        echo "✅ Seed $seed: PASSED"
    else
        echo "❌ Seed $seed: FAILED"
        FAILED_SEEDS+=("$seed")
    fi
    echo ""
done

echo "======================================"
echo "Summary"
echo "======================================"
echo "Tested ${#SEEDS[@]} seeds:"
echo "  Passed: $((${#SEEDS[@]} - ${#FAILED_SEEDS[@]}))"
echo "  Failed: ${#FAILED_SEEDS[@]}"

if [ ${#FAILED_SEEDS[@]} -gt 0 ]; then
    echo ""
    echo "❌ Failed seeds: ${FAILED_SEEDS[*]}"
    echo ""
    echo "To reproduce a failure:"
    for failed_seed in "${FAILED_SEEDS[@]}"; do
        echo "  FOUNDRY_PROFILE=difftest DIFFTEST_RANDOM_SEED=$failed_seed DIFFTEST_SHARD_COUNT=1 DIFFTEST_SHARD_INDEX=0 DIFFTEST_RANDOM_SMALL=100 DIFFTEST_RANDOM_LARGE=10000 forge test -vv"
    done
    exit 1
else
    echo ""
    echo "✅ All seeds passed!"
    exit 0
fi
