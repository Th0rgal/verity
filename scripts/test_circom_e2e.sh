#!/usr/bin/env bash
# test_circom_e2e.sh — End-to-end test for the provable intent DSL Circom pipeline.
#
# This script validates the full pipeline:
#   1. Generates Circom circuits from the ERC-20 IntentSpec (via Lean)
#   2. Compiles circuits with the `circom` compiler
#   3. Computes witness inputs (Poseidon commitments) with snarkjs/circomlibjs
#   4. Generates witnesses and verifies R1CS constraint satisfaction
#
# Prerequisites:
#   - circom (https://docs.circom.io/getting-started/installation/)
#   - node + npm
#   - snarkjs (npm install -g snarkjs)
#   - lake (Lean 4 build tool) — for circuit generation from Lean
#
# Usage:
#   ./scripts/test_circom_e2e.sh
#
# The script exits 0 on success, non-zero on any failure.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
WORK_DIR="$(mktemp -d)"

cleanup() { rm -rf "$WORK_DIR"; }
trap cleanup EXIT

echo "=== Provable Intent DSL — Circom End-to-End Test ==="
echo "Working directory: $WORK_DIR"
echo ""

# ---- Step 0: Check prerequisites ----
for cmd in circom node npm snarkjs; do
  if ! command -v "$cmd" &>/dev/null; then
    echo "ERROR: '$cmd' not found in PATH. Please install it first."
    exit 1
  fi
done
echo "✓ Prerequisites: circom, node, npm, snarkjs"

# ---- Step 1: Generate Circom from Lean ----
echo ""
echo "--- Step 1: Generate Circom circuits from Lean ---"
cd "$REPO_DIR"

# Generate circuit output using lake env lean
CIRCOM_OUTPUT="$(PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH" \
  lake env lean Compiler/CircomTest.lean 2>/dev/null)"

# Extract transfer circuit (lines between the two headers)
echo "$CIRCOM_OUTPUT" | awk '
  /^=== Generated Circom for ERC20.transfer ===$/{found=1; next}
  /^=== Generated Circom for ERC20.approve ===$/{found=0}
  found{print}
' > "$WORK_DIR/ERC20_transfer.circom"

# Extract approve circuit (from second header to end)
echo "$CIRCOM_OUTPUT" | awk '
  /^=== Generated Circom for ERC20.approve ===$/{found=1; next}
  found{print}
' > "$WORK_DIR/ERC20_approve.circom"

if [ ! -s "$WORK_DIR/ERC20_transfer.circom" ]; then
  echo "ERROR: Failed to generate transfer circuit"
  exit 1
fi
if [ ! -s "$WORK_DIR/ERC20_approve.circom" ]; then
  echo "ERROR: Failed to generate approve circuit"
  exit 1
fi

echo "✓ Generated ERC20_transfer.circom ($(wc -l < "$WORK_DIR/ERC20_transfer.circom") lines)"
echo "✓ Generated ERC20_approve.circom ($(wc -l < "$WORK_DIR/ERC20_approve.circom") lines)"

# ---- Step 2: Install circomlib and compile circuits ----
echo ""
echo "--- Step 2: Compile circuits with circom ---"
cd "$WORK_DIR"
npm init -y > /dev/null 2>&1
npm install --save circomlib circomlibjs > /dev/null 2>&1

circom ERC20_transfer.circom --r1cs --wasm --sym -l node_modules 2>&1 | grep -E "constraints|okay|Error"
TRANSFER_NL=$(circom ERC20_transfer.circom --r1cs -l node_modules 2>&1 | grep "non-linear" | awk '{print $NF}')
echo "✓ Transfer circuit compiled: ${TRANSFER_NL} non-linear constraints"

circom ERC20_approve.circom --r1cs --wasm --sym -l node_modules 2>&1 | grep -E "constraints|okay|Error"
APPROVE_NL=$(circom ERC20_approve.circom --r1cs -l node_modules 2>&1 | grep "non-linear" | awk '{print $NF}')
echo "✓ Approve circuit compiled: ${APPROVE_NL} non-linear constraints"

# ---- Step 3: Compute witness inputs ----
echo ""
echo "--- Step 3: Compute witness inputs (Poseidon commitments) ---"

cat > compute_inputs.js << 'JSEOF'
const { buildPoseidon } = require("circomlibjs");
const fs = require("fs");

async function main() {
  const poseidon = await buildPoseidon();
  const F = poseidon.F;

  // ---------- Transfer test cases ----------

  // Case 1: transfer(to=0xdead, amount=1000) — specific amount (else branch)
  {
    const selector = BigInt("2835717307");  // 0xa9059cbb
    const to = BigInt("0xdead");
    const amount_lo = BigInt(1000);
    const amount_hi = BigInt(0);

    const cdHash = F.toObject(poseidon([selector, to, amount_lo, amount_hi]));
    // amount != MAX → isMaxUint false → templateId = 1 (else branch)
    const templateId = BigInt(1);
    const outHash = F.toObject(poseidon([templateId, amount_lo, amount_hi, to]));

    const input = {
      selector: selector.toString(),
      calldataCommitment: cdHash.toString(),
      outputCommitment: outHash.toString(),
      to: to.toString(),
      amount_lo: amount_lo.toString(),
      amount_hi: amount_hi.toString()
    };
    fs.writeFileSync("transfer_1000_input.json", JSON.stringify(input, null, 2));
    console.log("✓ Wrote transfer_1000_input.json (amount=1000, templateId=1)");
  }

  // Case 2: transfer(to=0xdead, amount=MAX_UINT256) — all tokens (then branch)
  {
    const selector = BigInt("2835717307");
    const to = BigInt("0xdead");
    const max128 = (BigInt(1) << BigInt(128)) - BigInt(1);

    const cdHash = F.toObject(poseidon([selector, to, max128, max128]));
    // amount == MAX → isMaxUint true → templateId = 0 (then branch)
    const templateId = BigInt(0);
    const outHash = F.toObject(poseidon([templateId, max128, max128, to]));

    const input = {
      selector: selector.toString(),
      calldataCommitment: cdHash.toString(),
      outputCommitment: outHash.toString(),
      to: to.toString(),
      amount_lo: max128.toString(),
      amount_hi: max128.toString()
    };
    fs.writeFileSync("transfer_max_input.json", JSON.stringify(input, null, 2));
    console.log("✓ Wrote transfer_max_input.json (amount=MAX, templateId=0)");
  }

  // ---------- Approve test case ----------

  // Case 3: approve(spender=0xbeef, amount=500) — specific amount
  {
    const selector = BigInt("157198259");  // 0x095ea7b3
    const spender = BigInt("0xbeef");
    const amount_lo = BigInt(500);
    const amount_hi = BigInt(0);

    const cdHash = F.toObject(poseidon([selector, spender, amount_lo, amount_hi]));
    const templateId = BigInt(1);  // else branch
    const outHash = F.toObject(poseidon([templateId, spender, amount_lo, amount_hi]));

    const input = {
      selector: selector.toString(),
      calldataCommitment: cdHash.toString(),
      outputCommitment: outHash.toString(),
      spender: spender.toString(),
      amount_lo: amount_lo.toString(),
      amount_hi: amount_hi.toString()
    };
    fs.writeFileSync("approve_500_input.json", JSON.stringify(input, null, 2));
    console.log("✓ Wrote approve_500_input.json (amount=500, templateId=1)");
  }
}

main().catch(e => { console.error(e); process.exit(1); });
JSEOF

node compute_inputs.js

# ---- Step 4: Generate witnesses and verify constraints ----
echo ""
echo "--- Step 4: Generate witnesses and verify R1CS constraints ---"

PASS=0
FAIL=0

run_witness_test() {
  local name="$1"
  local circuit="$2"
  local input="$3"

  echo -n "  $name ... "

  local wasm_dir="${circuit%.circom}_js"
  local wasm_file="$wasm_dir/${circuit%.circom}.wasm"
  local wtns_file="${name}.wtns"

  if ! node "$wasm_dir/generate_witness.js" "$wasm_file" "$input" "$wtns_file" 2>/dev/null; then
    echo "FAIL (witness generation)"
    FAIL=$((FAIL + 1))
    return
  fi

  local check_output
  check_output=$(snarkjs wchk "${circuit%.circom}.r1cs" "$wtns_file" 2>&1)
  if echo "$check_output" | grep -q "WITNESS IS CORRECT"; then
    echo "PASS"
    PASS=$((PASS + 1))
  else
    echo "FAIL (constraint check)"
    echo "$check_output"
    FAIL=$((FAIL + 1))
  fi
}

run_witness_test "transfer_amount_1000" "ERC20_transfer.circom" "transfer_1000_input.json"
run_witness_test "transfer_amount_max"  "ERC20_transfer.circom" "transfer_max_input.json"
run_witness_test "approve_amount_500"   "ERC20_approve.circom"  "approve_500_input.json"

# ---- Summary ----
echo ""
echo "=== Results ==="
echo "Passed: $PASS"
echo "Failed: $FAIL"

if [ "$FAIL" -eq 0 ]; then
  echo ""
  echo "✓ All end-to-end Circom tests passed!"
  echo ""
  echo "Circuit stats:"
  echo "  Transfer: ${TRANSFER_NL} non-linear constraints"
  echo "  Approve:  ${APPROVE_NL} non-linear constraints"
  exit 0
else
  echo ""
  echo "✗ Some tests failed"
  exit 1
fi
