#!/usr/bin/env bash
set -euo pipefail

python3 research/poc_constraints/dsl_to_constraints.py specs/loan.dc src/LoanSpecHarness.sol
