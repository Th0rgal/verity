#!/usr/bin/env bash
# test_circom_e2e.sh — End-to-end test for the provable intent DSL Circom pipeline.
#
# This script validates the full pipeline:
#   1. Generates Circom circuits from the ERC-20, Ledger, and ERC-721 IntentSpecs (via Lean)
#   2. Compiles circuits with the `circom` compiler
#   3. Computes witness inputs (Poseidon commitments) with snarkjs/circomlibjs
#   4. Generates witnesses and verifies R1CS constraint satisfaction
#   5. Generates Groth16 proofs and verifies them (trusted setup → prove → verify)
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

# Extract transfer circuit (between transfer and approve headers)
echo "$CIRCOM_OUTPUT" | awk '
  /^=== Generated Circom for ERC20.transfer ===$/{found=1; next}
  /^=== Generated Circom for ERC20.approve ===$/{found=0}
  found{print}
' > "$WORK_DIR/ERC20_transfer.circom"

# Extract approve circuit (between approve and transferFrom headers)
echo "$CIRCOM_OUTPUT" | awk '
  /^=== Generated Circom for ERC20.approve ===$/{found=1; next}
  /^=== Generated Circom for ERC20.transferFrom ===$/{found=0}
  found{print}
' > "$WORK_DIR/ERC20_approve.circom"

# Extract transferFrom circuit (between transferFrom and Ledger.deposit headers)
echo "$CIRCOM_OUTPUT" | awk '
  /^=== Generated Circom for ERC20.transferFrom ===$/{found=1; next}
  /^=== Generated Circom for Ledger.deposit ===$/{found=0}
  found{print}
' > "$WORK_DIR/ERC20_transferFrom.circom"

# Extract Ledger deposit circuit (between deposit and withdraw headers)
echo "$CIRCOM_OUTPUT" | awk '
  /^=== Generated Circom for Ledger.deposit ===$/{found=1; next}
  /^=== Generated Circom for Ledger.withdraw ===$/{found=0}
  found{print}
' > "$WORK_DIR/Ledger_deposit.circom"

# Extract Ledger withdraw circuit (between withdraw and Ledger.transfer headers)
echo "$CIRCOM_OUTPUT" | awk '
  /^=== Generated Circom for Ledger.withdraw ===$/{found=1; next}
  /^=== Generated Circom for Ledger.transfer ===$/{found=0}
  found{print}
' > "$WORK_DIR/Ledger_withdraw.circom"

# Extract Ledger transfer circuit (between Ledger.transfer and ERC721.approve headers)
echo "$CIRCOM_OUTPUT" | awk '
  /^=== Generated Circom for Ledger.transfer ===$/{found=1; next}
  /^=== Generated Circom for ERC721.approve ===$/{found=0}
  found{print}
' > "$WORK_DIR/Ledger_transfer.circom"

# Extract ERC721 approve circuit (between ERC721.approve and ERC721.setApprovalForAll headers)
echo "$CIRCOM_OUTPUT" | awk '
  /^=== Generated Circom for ERC721.approve ===$/{found=1; next}
  /^=== Generated Circom for ERC721.setApprovalForAll ===$/{found=0}
  found{print}
' > "$WORK_DIR/ERC721_approve.circom"

# Extract ERC721 setApprovalForAll circuit (between setApprovalForAll and transferFrom headers)
echo "$CIRCOM_OUTPUT" | awk '
  /^=== Generated Circom for ERC721.setApprovalForAll ===$/{found=1; next}
  /^=== Generated Circom for ERC721.transferFrom ===$/{found=0}
  found{print}
' > "$WORK_DIR/ERC721_setApprovalForAll.circom"

# Extract ERC721 transferFrom circuit (from ERC721.transferFrom header to EOF)
echo "$CIRCOM_OUTPUT" | awk '
  /^=== Generated Circom for ERC721.transferFrom ===$/{found=1; next}
  found{print}
' > "$WORK_DIR/ERC721_transferFrom.circom"

for f in ERC20_transfer ERC20_approve ERC20_transferFrom Ledger_deposit Ledger_withdraw Ledger_transfer ERC721_approve ERC721_setApprovalForAll ERC721_transferFrom; do
  if [ ! -s "$WORK_DIR/${f}.circom" ]; then
    echo "ERROR: Failed to generate ${f} circuit"
    exit 1
  fi
  echo "✓ Generated ${f}.circom ($(wc -l < "$WORK_DIR/${f}.circom") lines)"
done

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

circom ERC20_transferFrom.circom --r1cs --wasm --sym -l node_modules 2>&1 | grep -E "constraints|okay|Error"
TRANSFER_FROM_NL=$(circom ERC20_transferFrom.circom --r1cs -l node_modules 2>&1 | grep "non-linear" | awk '{print $NF}')
echo "✓ TransferFrom circuit compiled: ${TRANSFER_FROM_NL} non-linear constraints"

circom Ledger_deposit.circom --r1cs --wasm --sym -l node_modules 2>&1 | grep -E "constraints|okay|Error"
DEPOSIT_NL=$(circom Ledger_deposit.circom --r1cs -l node_modules 2>&1 | grep "non-linear" | awk '{print $NF}')
echo "✓ Deposit circuit compiled: ${DEPOSIT_NL} non-linear constraints"

circom Ledger_withdraw.circom --r1cs --wasm --sym -l node_modules 2>&1 | grep -E "constraints|okay|Error"
WITHDRAW_NL=$(circom Ledger_withdraw.circom --r1cs -l node_modules 2>&1 | grep "non-linear" | awk '{print $NF}')
echo "✓ Withdraw circuit compiled: ${WITHDRAW_NL} non-linear constraints"

circom Ledger_transfer.circom --r1cs --wasm --sym -l node_modules 2>&1 | grep -E "constraints|okay|Error"
LEDGER_TRANSFER_NL=$(circom Ledger_transfer.circom --r1cs -l node_modules 2>&1 | grep "non-linear" | awk '{print $NF}')
echo "✓ Ledger Transfer circuit compiled: ${LEDGER_TRANSFER_NL} non-linear constraints"

circom ERC721_approve.circom --r1cs --wasm --sym -l node_modules 2>&1 | grep -E "constraints|okay|Error"
ERC721_APPROVE_NL=$(circom ERC721_approve.circom --r1cs -l node_modules 2>&1 | grep "non-linear" | awk '{print $NF}')
echo "✓ ERC721 Approve circuit compiled: ${ERC721_APPROVE_NL} non-linear constraints"

circom ERC721_setApprovalForAll.circom --r1cs --wasm --sym -l node_modules 2>&1 | grep -E "constraints|okay|Error"
SET_APPROVAL_NL=$(circom ERC721_setApprovalForAll.circom --r1cs -l node_modules 2>&1 | grep "non-linear" | awk '{print $NF}')
echo "✓ SetApprovalForAll circuit compiled: ${SET_APPROVAL_NL} non-linear constraints"

circom ERC721_transferFrom.circom --r1cs --wasm --sym -l node_modules 2>&1 | grep -E "constraints|okay|Error"
ERC721_TRANSFER_FROM_NL=$(circom ERC721_transferFrom.circom --r1cs -l node_modules 2>&1 | grep "non-linear" | awk '{print $NF}')
echo "✓ ERC721 TransferFrom circuit compiled: ${ERC721_TRANSFER_FROM_NL} non-linear constraints"

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

  // ---------- TransferFrom test cases ----------

  // Case 4: transferFrom(fromAddr=0xcafe, to=0xdead, amount=2000) — specific amount (else branch)
  {
    const selector = BigInt("599290589");  // 0x23b872dd
    const fromAddr = BigInt("0xcafe");
    const to = BigInt("0xdead");
    const amount_lo = BigInt(2000);
    const amount_hi = BigInt(0);

    // cdHash: Poseidon(selector, fromAddr, to, amount_lo, amount_hi) — 5 inputs
    const cdHash = F.toObject(poseidon([selector, fromAddr, to, amount_lo, amount_hi]));
    // amount != MAX → isMaxUint false → templateId = 1 (else branch)
    const templateId = BigInt(1);
    // outHash: Poseidon(templateId, amount_lo, amount_hi, fromAddr, to) — deduped hole order
    const outHash = F.toObject(poseidon([templateId, amount_lo, amount_hi, fromAddr, to]));

    const input = {
      selector: selector.toString(),
      calldataCommitment: cdHash.toString(),
      outputCommitment: outHash.toString(),
      fromAddr: fromAddr.toString(),
      to: to.toString(),
      amount_lo: amount_lo.toString(),
      amount_hi: amount_hi.toString()
    };
    fs.writeFileSync("transferFrom_2000_input.json", JSON.stringify(input, null, 2));
    console.log("✓ Wrote transferFrom_2000_input.json (amount=2000, templateId=1)");
  }

  // Case 5: transferFrom(fromAddr=0xcafe, to=0xdead, amount=MAX_UINT256) — all tokens (then branch)
  {
    const selector = BigInt("599290589");  // 0x23b872dd
    const fromAddr = BigInt("0xcafe");
    const to = BigInt("0xdead");
    const max128 = (BigInt(1) << BigInt(128)) - BigInt(1);

    const cdHash = F.toObject(poseidon([selector, fromAddr, to, max128, max128]));
    // amount == MAX → isMaxUint true → templateId = 0 (then branch)
    const templateId = BigInt(0);
    const outHash = F.toObject(poseidon([templateId, max128, max128, fromAddr, to]));

    const input = {
      selector: selector.toString(),
      calldataCommitment: cdHash.toString(),
      outputCommitment: outHash.toString(),
      fromAddr: fromAddr.toString(),
      to: to.toString(),
      amount_lo: max128.toString(),
      amount_hi: max128.toString()
    };
    fs.writeFileSync("transferFrom_max_input.json", JSON.stringify(input, null, 2));
    console.log("✓ Wrote transferFrom_max_input.json (amount=MAX, templateId=0)");
  }

  // ---------- Ledger deposit test case ----------

  // Case 6: deposit(amount=5000) — single template (unconditional)
  {
    const selector = BigInt("3065339685");  // 0xb6b55f25
    const amount_lo = BigInt(5000);
    const amount_hi = BigInt(0);

    // cdHash: Poseidon(selector, amount_lo, amount_hi) — 3 inputs
    const cdHash = F.toObject(poseidon([selector, amount_lo, amount_hi]));
    // Single template (unconditional) → templateId = 0
    const templateId = BigInt(0);
    // outHash: Poseidon(templateId, amount_lo, amount_hi) — 3 inputs
    const outHash = F.toObject(poseidon([templateId, amount_lo, amount_hi]));

    const input = {
      selector: selector.toString(),
      calldataCommitment: cdHash.toString(),
      outputCommitment: outHash.toString(),
      amount_lo: amount_lo.toString(),
      amount_hi: amount_hi.toString()
    };
    fs.writeFileSync("deposit_5000_input.json", JSON.stringify(input, null, 2));
    console.log("✓ Wrote deposit_5000_input.json (amount=5000, templateId=0)");
  }

  // ---------- Ledger withdraw test case ----------

  // Case 7: withdraw(amount=3000) — single template (unconditional)
  {
    const selector = BigInt("773487949");  // 0x2e1a7d4d
    const amount_lo = BigInt(3000);
    const amount_hi = BigInt(0);

    const cdHash = F.toObject(poseidon([selector, amount_lo, amount_hi]));
    const templateId = BigInt(0);
    const outHash = F.toObject(poseidon([templateId, amount_lo, amount_hi]));

    const input = {
      selector: selector.toString(),
      calldataCommitment: cdHash.toString(),
      outputCommitment: outHash.toString(),
      amount_lo: amount_lo.toString(),
      amount_hi: amount_hi.toString()
    };
    fs.writeFileSync("withdraw_3000_input.json", JSON.stringify(input, null, 2));
    console.log("✓ Wrote withdraw_3000_input.json (amount=3000, templateId=0)");
  }

  // ---------- Ledger transfer test cases ----------

  // Case 8: ledger transfer(to=0xdead, amount=2000) — specific amount (else branch)
  {
    const selector = BigInt("2835717307");  // 0xa9059cbb
    const to = BigInt("0xdead");
    const amount_lo = BigInt(2000);
    const amount_hi = BigInt(0);

    const cdHash = F.toObject(poseidon([selector, to, amount_lo, amount_hi]));
    const templateId = BigInt(1);  // else branch
    const outHash = F.toObject(poseidon([templateId, amount_lo, amount_hi, to]));

    const input = {
      selector: selector.toString(),
      calldataCommitment: cdHash.toString(),
      outputCommitment: outHash.toString(),
      to: to.toString(),
      amount_lo: amount_lo.toString(),
      amount_hi: amount_hi.toString()
    };
    fs.writeFileSync("ledger_transfer_2000_input.json", JSON.stringify(input, null, 2));
    console.log("✓ Wrote ledger_transfer_2000_input.json (amount=2000, templateId=1)");
  }

  // Case 9: ledger transfer(to=0xdead, amount=MAX) — all tokens (then branch)
  {
    const selector = BigInt("2835717307");  // 0xa9059cbb
    const to = BigInt("0xdead");
    const max128 = (BigInt(1) << BigInt(128)) - BigInt(1);

    const cdHash = F.toObject(poseidon([selector, to, max128, max128]));
    const templateId = BigInt(0);  // then branch
    const outHash = F.toObject(poseidon([templateId, max128, max128, to]));

    const input = {
      selector: selector.toString(),
      calldataCommitment: cdHash.toString(),
      outputCommitment: outHash.toString(),
      to: to.toString(),
      amount_lo: max128.toString(),
      amount_hi: max128.toString()
    };
    fs.writeFileSync("ledger_transfer_max_input.json", JSON.stringify(input, null, 2));
    console.log("✓ Wrote ledger_transfer_max_input.json (amount=MAX, templateId=0)");
  }

  // ---------- ERC-721 setApprovalForAll test cases (bool parameter) ----------

  // Case 10: setApprovalForAll(operator=0xbeef, approved=true) — then branch
  {
    const selector = BigInt("2720838757");  // 0xa22cb465
    const operator = BigInt("0xbeef");
    const approved = BigInt(1);  // true

    // cdHash: Poseidon(selector, operator, approved) — 3 inputs
    const cdHash = F.toObject(poseidon([selector, operator, approved]));
    // approved == true → then branch → templateId = 0
    const templateId = BigInt(0);
    // outHash: Poseidon(templateId, operator) — 2 inputs (only operator in holes)
    const outHash = F.toObject(poseidon([templateId, operator]));

    const input = {
      selector: selector.toString(),
      calldataCommitment: cdHash.toString(),
      outputCommitment: outHash.toString(),
      operator: operator.toString(),
      approved: approved.toString()
    };
    fs.writeFileSync("setApproval_true_input.json", JSON.stringify(input, null, 2));
    console.log("✓ Wrote setApproval_true_input.json (approved=true, templateId=0)");
  }

  // Case 11: setApprovalForAll(operator=0xbeef, approved=false) — else branch
  {
    const selector = BigInt("2720838757");  // 0xa22cb465
    const operator = BigInt("0xbeef");
    const approved = BigInt(0);  // false

    const cdHash = F.toObject(poseidon([selector, operator, approved]));
    // approved == false → else branch → templateId = 1
    const templateId = BigInt(1);
    const outHash = F.toObject(poseidon([templateId, operator]));

    const input = {
      selector: selector.toString(),
      calldataCommitment: cdHash.toString(),
      outputCommitment: outHash.toString(),
      operator: operator.toString(),
      approved: approved.toString()
    };
    fs.writeFileSync("setApproval_false_input.json", JSON.stringify(input, null, 2));
    console.log("✓ Wrote setApproval_false_input.json (approved=false, templateId=1)");
  }

  // ---------- ERC-721 approve test case ----------

  // Case 12: approve(approved=0xbeef, tokenId=42) — unconditional
  {
    const selector = BigInt("157198259");  // 0x095ea7b3
    const approved = BigInt("0xbeef");
    const tokenId_lo = BigInt(42);
    const tokenId_hi = BigInt(0);

    // cdHash: Poseidon(selector, approved, tokenId_lo, tokenId_hi) — 4 inputs
    const cdHash = F.toObject(poseidon([selector, approved, tokenId_lo, tokenId_hi]));
    // Unconditional → templateId = 0
    const templateId = BigInt(0);
    // outHash: Poseidon(templateId, approved, tokenId_lo, tokenId_hi) — hole order from emit
    const outHash = F.toObject(poseidon([templateId, approved, tokenId_lo, tokenId_hi]));

    const input = {
      selector: selector.toString(),
      calldataCommitment: cdHash.toString(),
      outputCommitment: outHash.toString(),
      approved: approved.toString(),
      tokenId_lo: tokenId_lo.toString(),
      tokenId_hi: tokenId_hi.toString()
    };
    fs.writeFileSync("erc721_approve_42_input.json", JSON.stringify(input, null, 2));
    console.log("✓ Wrote erc721_approve_42_input.json (tokenId=42, templateId=0)");
  }

  // ---------- ERC-721 transferFrom test case ----------

  // Case 13: transferFrom(fromAddr=0xcafe, to=0xdead, tokenId=99) — unconditional
  {
    const selector = BigInt("599290589");  // 0x23b872dd
    const fromAddr = BigInt("0xcafe");
    const to = BigInt("0xdead");
    const tokenId_lo = BigInt(99);
    const tokenId_hi = BigInt(0);

    // cdHash: Poseidon(selector, fromAddr, to, tokenId_lo, tokenId_hi) — 5 inputs
    const cdHash = F.toObject(poseidon([selector, fromAddr, to, tokenId_lo, tokenId_hi]));
    // Unconditional → templateId = 0
    const templateId = BigInt(0);
    // outHash: Poseidon(templateId, tokenId_lo, tokenId_hi, fromAddr, to) — hole order from emit
    const outHash = F.toObject(poseidon([templateId, tokenId_lo, tokenId_hi, fromAddr, to]));

    const input = {
      selector: selector.toString(),
      calldataCommitment: cdHash.toString(),
      outputCommitment: outHash.toString(),
      fromAddr: fromAddr.toString(),
      to: to.toString(),
      tokenId_lo: tokenId_lo.toString(),
      tokenId_hi: tokenId_hi.toString()
    };
    fs.writeFileSync("erc721_transferFrom_99_input.json", JSON.stringify(input, null, 2));
    console.log("✓ Wrote erc721_transferFrom_99_input.json (tokenId=99, templateId=0)");
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

run_witness_test "transfer_amount_1000"     "ERC20_transfer.circom"     "transfer_1000_input.json"
run_witness_test "transfer_amount_max"      "ERC20_transfer.circom"     "transfer_max_input.json"
run_witness_test "approve_amount_500"       "ERC20_approve.circom"      "approve_500_input.json"
run_witness_test "transferFrom_amount_2000" "ERC20_transferFrom.circom" "transferFrom_2000_input.json"
run_witness_test "transferFrom_amount_max"  "ERC20_transferFrom.circom" "transferFrom_max_input.json"
run_witness_test "deposit_amount_5000"      "Ledger_deposit.circom"     "deposit_5000_input.json"
run_witness_test "withdraw_amount_3000"     "Ledger_withdraw.circom"    "withdraw_3000_input.json"
run_witness_test "ledger_transfer_2000"     "Ledger_transfer.circom"    "ledger_transfer_2000_input.json"
run_witness_test "ledger_transfer_max"      "Ledger_transfer.circom"    "ledger_transfer_max_input.json"
run_witness_test "erc721_approve_42"        "ERC721_approve.circom"          "erc721_approve_42_input.json"
run_witness_test "setApproval_true"         "ERC721_setApprovalForAll.circom" "setApproval_true_input.json"
run_witness_test "setApproval_false"        "ERC721_setApprovalForAll.circom" "setApproval_false_input.json"
run_witness_test "erc721_transferFrom_99"   "ERC721_transferFrom.circom"     "erc721_transferFrom_99_input.json"

# ---- Step 5: Groth16 proof generation and verification ----
echo ""
echo "--- Step 5: Groth16 proof generation and verification ---"

# Powers of tau ceremony (2^12 = 4096 > 605 constraints)
echo -n "  Powers of tau ceremony ... "
snarkjs powersoftau new bn128 12 pot12_0000.ptau 2>/dev/null
snarkjs powersoftau contribute pot12_0000.ptau pot12_0001.ptau \
  --name="E2E test" -e="verity-intent-dsl-e2e-entropy" 2>/dev/null
snarkjs powersoftau prepare phase2 pot12_0001.ptau pot12_final.ptau 2>/dev/null
echo "done"

run_proof_test() {
  local name="$1"
  local circuit="$2"
  local wtns_file="$3"
  local circuit_base="${circuit%.circom}"

  echo -n "  $name ... "

  # Groth16 setup
  if ! snarkjs groth16 setup "${circuit_base}.r1cs" pot12_final.ptau "${name}_0000.zkey" 2>/dev/null; then
    echo "FAIL (groth16 setup)"
    FAIL=$((FAIL + 1))
    return
  fi

  # Contribute to ceremony
  if ! snarkjs zkey contribute "${name}_0000.zkey" "${name}_final.zkey" \
      --name="E2E test" -e="verity-proof-test-${name}" 2>/dev/null; then
    echo "FAIL (zkey contribute)"
    FAIL=$((FAIL + 1))
    return
  fi

  # Export verification key
  if ! snarkjs zkey export verificationkey "${name}_final.zkey" "${name}_vkey.json" 2>/dev/null; then
    echo "FAIL (export vkey)"
    FAIL=$((FAIL + 1))
    return
  fi

  # Generate proof
  if ! snarkjs groth16 prove "${name}_final.zkey" "$wtns_file" "${name}_proof.json" "${name}_public.json" 2>/dev/null; then
    echo "FAIL (prove)"
    FAIL=$((FAIL + 1))
    return
  fi

  # Verify proof
  local verify_output
  verify_output=$(snarkjs groth16 verify "${name}_vkey.json" "${name}_public.json" "${name}_proof.json" 2>&1)
  if echo "$verify_output" | grep -q "OK"; then
    echo "PASS (proof verified)"
    PASS=$((PASS + 1))
  else
    echo "FAIL (verification)"
    echo "$verify_output"
    FAIL=$((FAIL + 1))
  fi
}

run_proof_test "transfer_1000_proof"     "ERC20_transfer.circom"     "transfer_amount_1000.wtns"
run_proof_test "transfer_max_proof"      "ERC20_transfer.circom"     "transfer_amount_max.wtns"
run_proof_test "approve_500_proof"       "ERC20_approve.circom"      "approve_amount_500.wtns"
run_proof_test "transferFrom_2000_proof" "ERC20_transferFrom.circom" "transferFrom_amount_2000.wtns"
run_proof_test "transferFrom_max_proof"  "ERC20_transferFrom.circom" "transferFrom_amount_max.wtns"
run_proof_test "deposit_5000_proof"      "Ledger_deposit.circom"     "deposit_amount_5000.wtns"
run_proof_test "withdraw_3000_proof"     "Ledger_withdraw.circom"    "withdraw_amount_3000.wtns"
run_proof_test "ledger_transfer_2000_proof" "Ledger_transfer.circom" "ledger_transfer_2000.wtns"
run_proof_test "ledger_transfer_max_proof"  "Ledger_transfer.circom" "ledger_transfer_max.wtns"
run_proof_test "erc721_approve_42_proof"       "ERC721_approve.circom"          "erc721_approve_42.wtns"
run_proof_test "setApproval_true_proof"        "ERC721_setApprovalForAll.circom" "setApproval_true.wtns"
run_proof_test "setApproval_false_proof"       "ERC721_setApprovalForAll.circom" "setApproval_false.wtns"
run_proof_test "erc721_transferFrom_99_proof"  "ERC721_transferFrom.circom"     "erc721_transferFrom_99.wtns"

# ---- Summary ----
echo ""
echo "=== Results ==="
echo "Passed: $PASS / $((PASS + FAIL))"
echo "Failed: $FAIL"

if [ "$FAIL" -eq 0 ]; then
  echo ""
  echo "✓ All end-to-end tests passed!"
  echo ""
  echo "Pipeline validated:"
  echo "  1. Lean IntentSpec → Circom circuit generation"
  echo "  2. Circom compilation → R1CS + WASM"
  echo "  3. Poseidon commitment computation"
  echo "  4. Witness generation + R1CS constraint verification"
  echo "  5. Groth16 proof generation + verification"
  echo ""
  echo "Circuit stats (ERC20):"
  echo "  Transfer:     ${TRANSFER_NL} non-linear constraints"
  echo "  Approve:      ${APPROVE_NL} non-linear constraints"
  echo "  TransferFrom: ${TRANSFER_FROM_NL} non-linear constraints"
  echo "Circuit stats (Ledger):"
  echo "  Deposit:      ${DEPOSIT_NL} non-linear constraints"
  echo "  Withdraw:     ${WITHDRAW_NL} non-linear constraints"
  echo "  Transfer:     ${LEDGER_TRANSFER_NL} non-linear constraints"
  echo "Circuit stats (ERC721):"
  echo "  Approve:           ${ERC721_APPROVE_NL} non-linear constraints"
  echo "  SetApprovalForAll: ${SET_APPROVAL_NL} non-linear constraints"
  echo "  TransferFrom:      ${ERC721_TRANSFER_FROM_NL} non-linear constraints"
  exit 0
else
  echo ""
  echo "✗ Some tests failed"
  exit 1
fi
