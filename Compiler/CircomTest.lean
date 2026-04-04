/-
  Compiler.CircomTest: Regression tests for the Circom circuit generator.

  Uses the ERC-20 example IntentSpec to generate Circom circuits and verify
  key structural properties at build time. These tests catch regressions
  in the circuit generator without requiring external tools (circom, snarkjs).

  IMPORTANT: The full Circom output is printed with header markers, because
  `scripts/test_circom_e2e.sh` parses this output to extract `.circom` files
  for external compilation and witness verification. The headers are:
    === Generated Circom for ERC20.transfer ===
    === Generated Circom for ERC20.approve ===
    === Generated Circom for ERC20.transferFrom ===
    === Generated Circom for Ledger.deposit ===
    === Generated Circom for Ledger.withdraw ===
    === Generated Circom for Ledger.transfer ===
    === Generated Circom for ERC721.approve ===
    === Generated Circom for ERC721.setApprovalForAll ===
    === Generated Circom for ERC721.transferFrom ===
  No other text may appear between a header and the next header (or EOF).
  All assertion messages are printed BEFORE the first header.
-/
import Compiler.Circom
import Verity.Intent.Example
import Contracts.Ledger.Display
import Contracts.ERC721.Display

namespace Compiler.CircomTest

open Verity.Intent
open Verity.Intent.Example

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- Verify structural properties of the transfer Circom circuit. -/
private def assertTransferStructure (circom : String) : IO Unit := do
  unless hasSubstr circom "template TransferIntent()" do
    throw (IO.userError "missing template TransferIntent()")
  unless hasSubstr circom "selector === 0xa9059cbb" do
    throw (IO.userError "missing selector check")
  unless hasSubstr circom "signal input selector" do
    throw (IO.userError "missing selector input")
  unless hasSubstr circom "signal input calldataCommitment" do
    throw (IO.userError "missing calldataCommitment input")
  unless hasSubstr circom "signal input outputCommitment" do
    throw (IO.userError "missing outputCommitment input")
  unless hasSubstr circom "signal input to" do
    throw (IO.userError "missing 'to' input")
  unless hasSubstr circom "signal input amount_lo" do
    throw (IO.userError "missing 'amount_lo' input")
  unless hasSubstr circom "signal input amount_hi" do
    throw (IO.userError "missing 'amount_hi' input")
  unless hasSubstr circom "component cdHash = Poseidon(4)" do
    throw (IO.userError "missing calldata Poseidon(4)")
  unless hasSubstr circom "component outHash = Poseidon(4)" do
    throw (IO.userError "missing output Poseidon(4)")
  unless hasSubstr circom "IsEqual()" do
    throw (IO.userError "missing IsEqual for uint256 comparison")
  unless hasSubstr circom "signal templateId" do
    throw (IO.userError "missing templateId signal")
  unless hasSubstr circom "component main {public [selector, calldataCommitment, outputCommitment]}" do
    throw (IO.userError "missing main component declaration")

/-- Verify structural properties of the approve Circom circuit. -/
private def assertApproveStructure (circom : String) : IO Unit := do
  unless hasSubstr circom "template ApproveIntent()" do
    throw (IO.userError "missing template ApproveIntent()")
  unless hasSubstr circom "selector === 0x095ea7b3" do
    throw (IO.userError "missing selector check")
  unless hasSubstr circom "signal input spender" do
    throw (IO.userError "missing 'spender' input")
  unless hasSubstr circom "signal input amount_lo" do
    throw (IO.userError "missing 'amount_lo' input")
  unless hasSubstr circom "component cdHash = Poseidon(4)" do
    throw (IO.userError "missing calldata Poseidon(4)")
  unless hasSubstr circom "component outHash = Poseidon(4)" do
    throw (IO.userError "missing output Poseidon(4)")
  unless hasSubstr circom "component main" do
    throw (IO.userError "missing main component")

/-- Verify structural properties of the transferFrom Circom circuit.
    3-parameter function (fromAddr: address, to: address, amount: uint256)
    maps to 4 signals (fromAddr, to, amount_lo, amount_hi) → Poseidon(5) for calldata. -/
private def assertTransferFromStructure (circom : String) : IO Unit := do
  unless hasSubstr circom "template TransferFromIntent()" do
    throw (IO.userError "missing template TransferFromIntent()")
  unless hasSubstr circom "selector === 0x23b872dd" do
    throw (IO.userError "missing selector check")
  unless hasSubstr circom "signal input fromAddr" do
    throw (IO.userError "missing 'fromAddr' input")
  unless hasSubstr circom "signal input to" do
    throw (IO.userError "missing 'to' input")
  unless hasSubstr circom "signal input amount_lo" do
    throw (IO.userError "missing 'amount_lo' input")
  unless hasSubstr circom "signal input amount_hi" do
    throw (IO.userError "missing 'amount_hi' input")
  -- 1 (selector) + 4 (fromAddr, to, amount_lo, amount_hi) = 5 inputs
  unless hasSubstr circom "component cdHash = Poseidon(5)" do
    throw (IO.userError "missing calldata Poseidon(5)")
  -- 1 (templateId) + 4 hole signals (amount_lo, amount_hi, fromAddr, to) = 5 outputs
  unless hasSubstr circom "component outHash = Poseidon(5)" do
    throw (IO.userError "missing output Poseidon(5)")
  unless hasSubstr circom "IsEqual()" do
    throw (IO.userError "missing IsEqual for uint256 comparison")
  unless hasSubstr circom "signal templateId" do
    throw (IO.userError "missing templateId signal")
  unless hasSubstr circom "component main {public [selector, calldataCommitment, outputCommitment]}" do
    throw (IO.userError "missing main component declaration")

/-- Verify structural properties of the Ledger deposit Circom circuit.
    Single-parameter function (amount: uint256) → unconditional single template.
    1 param → 2 signals (amount_lo, amount_hi) → Poseidon(3) for calldata/output. -/
private def assertDepositStructure (circom : String) : IO Unit := do
  unless hasSubstr circom "template DepositIntent()" do
    throw (IO.userError "missing template DepositIntent()")
  unless hasSubstr circom "selector === 0xb6b55f25" do
    throw (IO.userError "missing selector check")
  unless hasSubstr circom "signal input amount_lo" do
    throw (IO.userError "missing 'amount_lo' input")
  unless hasSubstr circom "signal input amount_hi" do
    throw (IO.userError "missing 'amount_hi' input")
  -- 1 (selector) + 2 (amount_lo, amount_hi) = 3
  unless hasSubstr circom "component cdHash = Poseidon(3)" do
    throw (IO.userError "missing calldata Poseidon(3)")
  -- 1 (templateId) + 2 (amount_lo, amount_hi) = 3
  unless hasSubstr circom "component outHash = Poseidon(3)" do
    throw (IO.userError "missing output Poseidon(3)")
  unless hasSubstr circom "signal templateId" do
    throw (IO.userError "missing templateId signal")
  unless hasSubstr circom "component main {public [selector, calldataCommitment, outputCommitment]}" do
    throw (IO.userError "missing main component declaration")

/-- Verify structural properties of the Ledger withdraw Circom circuit.
    Same structure as deposit: single uint256 param, unconditional. -/
private def assertWithdrawStructure (circom : String) : IO Unit := do
  unless hasSubstr circom "template WithdrawIntent()" do
    throw (IO.userError "missing template WithdrawIntent()")
  unless hasSubstr circom "selector === 0x2e1a7d4d" do
    throw (IO.userError "missing selector check")
  unless hasSubstr circom "signal input amount_lo" do
    throw (IO.userError "missing 'amount_lo' input")
  unless hasSubstr circom "signal input amount_hi" do
    throw (IO.userError "missing 'amount_hi' input")
  unless hasSubstr circom "component cdHash = Poseidon(3)" do
    throw (IO.userError "missing calldata Poseidon(3)")
  unless hasSubstr circom "component outHash = Poseidon(3)" do
    throw (IO.userError "missing output Poseidon(3)")
  unless hasSubstr circom "signal templateId" do
    throw (IO.userError "missing templateId signal")
  unless hasSubstr circom "component main {public [selector, calldataCommitment, outputCommitment]}" do
    throw (IO.userError "missing main component declaration")

/-- Verify structural properties of the Ledger transfer Circom circuit.
    Same as ERC20 transfer: (to: address, amount: uint256), conditional. -/
private def assertLedgerTransferStructure (circom : String) : IO Unit := do
  unless hasSubstr circom "template TransferIntent()" do
    throw (IO.userError "missing template TransferIntent()")
  unless hasSubstr circom "selector === 0xa9059cbb" do
    throw (IO.userError "missing selector check")
  unless hasSubstr circom "signal input to" do
    throw (IO.userError "missing 'to' input")
  unless hasSubstr circom "signal input amount_lo" do
    throw (IO.userError "missing 'amount_lo' input")
  unless hasSubstr circom "signal input amount_hi" do
    throw (IO.userError "missing 'amount_hi' input")
  unless hasSubstr circom "component cdHash = Poseidon(4)" do
    throw (IO.userError "missing calldata Poseidon(4)")
  unless hasSubstr circom "component outHash = Poseidon(4)" do
    throw (IO.userError "missing output Poseidon(4)")
  unless hasSubstr circom "IsEqual()" do
    throw (IO.userError "missing IsEqual for uint256 comparison")
  unless hasSubstr circom "signal templateId" do
    throw (IO.userError "missing templateId signal")
  unless hasSubstr circom "component main {public [selector, calldataCommitment, outputCommitment]}" do
    throw (IO.userError "missing main component declaration")

/-- Verify structural properties of the ERC-721 approve Circom circuit.
    2-parameter function (approved: address, tokenId: uint256), unconditional.
    1 (selector) + 3 (approved, tokenId_lo, tokenId_hi) = 4 inputs for calldata Poseidon.
    1 (templateId) + 3 (tokenId_lo, tokenId_hi, approved) = 4 inputs for output Poseidon. -/
private def assertERC721ApproveStructure (circom : String) : IO Unit := do
  unless hasSubstr circom "template ApproveIntent()" do
    throw (IO.userError "missing template ApproveIntent()")
  unless hasSubstr circom "selector === 0x095ea7b3" do
    throw (IO.userError "missing selector check")
  unless hasSubstr circom "signal input approved" do
    throw (IO.userError "missing 'approved' input")
  unless hasSubstr circom "signal input tokenId_lo" do
    throw (IO.userError "missing 'tokenId_lo' input")
  unless hasSubstr circom "signal input tokenId_hi" do
    throw (IO.userError "missing 'tokenId_hi' input")
  -- 1 (selector) + 3 (approved, tokenId_lo, tokenId_hi) = 4
  unless hasSubstr circom "component cdHash = Poseidon(4)" do
    throw (IO.userError "missing calldata Poseidon(4)")
  unless hasSubstr circom "signal templateId" do
    throw (IO.userError "missing templateId signal")
  unless hasSubstr circom "component main {public [selector, calldataCommitment, outputCommitment]}" do
    throw (IO.userError "missing main component declaration")

/-- Verify structural properties of the ERC-721 transferFrom Circom circuit.
    3-parameter function (fromAddr: address, to: address, tokenId: uint256), unconditional.
    1 (selector) + 4 (fromAddr, to, tokenId_lo, tokenId_hi) = 5 inputs for calldata Poseidon. -/
private def assertERC721TransferFromStructure (circom : String) : IO Unit := do
  unless hasSubstr circom "template TransferFromIntent()" do
    throw (IO.userError "missing template TransferFromIntent()")
  unless hasSubstr circom "selector === 0x23b872dd" do
    throw (IO.userError "missing selector check")
  unless hasSubstr circom "signal input fromAddr" do
    throw (IO.userError "missing 'fromAddr' input")
  unless hasSubstr circom "signal input to" do
    throw (IO.userError "missing 'to' input")
  unless hasSubstr circom "signal input tokenId_lo" do
    throw (IO.userError "missing 'tokenId_lo' input")
  unless hasSubstr circom "signal input tokenId_hi" do
    throw (IO.userError "missing 'tokenId_hi' input")
  -- 1 (selector) + 4 (fromAddr, to, tokenId_lo, tokenId_hi) = 5
  unless hasSubstr circom "component cdHash = Poseidon(5)" do
    throw (IO.userError "missing calldata Poseidon(5)")
  unless hasSubstr circom "signal templateId" do
    throw (IO.userError "missing templateId signal")
  unless hasSubstr circom "component main {public [selector, calldataCommitment, outputCommitment]}" do
    throw (IO.userError "missing main component declaration")

/-- Verify structural properties of the ERC-721 setApprovalForAll Circom circuit.
    2-parameter function (operator: address, approved: bool), conditional on bool.
    1 (selector) + 2 (operator, approved) = 3 inputs for calldata Poseidon.
    1 (templateId) + 1 (operator) = 2 inputs for output Poseidon. -/
private def assertSetApprovalForAllStructure (circom : String) : IO Unit := do
  unless hasSubstr circom "template SetApprovalForAllIntent()" do
    throw (IO.userError "missing template SetApprovalForAllIntent()")
  unless hasSubstr circom "selector === 0xa22cb465" do
    throw (IO.userError "missing selector check")
  unless hasSubstr circom "signal input operator" do
    throw (IO.userError "missing 'operator' input")
  unless hasSubstr circom "signal input approved" do
    throw (IO.userError "missing 'approved' input")
  -- 1 (selector) + 2 (operator, approved) = 3
  unless hasSubstr circom "component cdHash = Poseidon(3)" do
    throw (IO.userError "missing calldata Poseidon(3)")
  -- 1 (templateId) + 1 (operator) = 2
  unless hasSubstr circom "component outHash = Poseidon(2)" do
    throw (IO.userError "missing output Poseidon(2)")
  unless hasSubstr circom "signal templateId" do
    throw (IO.userError "missing templateId signal")
  unless hasSubstr circom "component main {public [selector, calldataCommitment, outputCommitment]}" do
    throw (IO.userError "missing main component declaration")

-- Single #eval block: run all assertions, then print structured output.
-- All assertion/status messages come before headers so the E2E script's
-- awk extraction gets clean circom source between headers (and to EOF).
#eval do
  let spec := erc20IntentSpec

  -- Generate transfer circuit
  let transferBinding ← match getBinding spec 0 with
    | some b => pure b
    | none => throw (IO.userError "transfer binding not found")
  let transferCircom ← match Compiler.Circom.emitCircom spec transferBinding "0xa9059cbb" with
    | some c => pure c
    | none => throw (IO.userError "Circom generation failed for transfer")
  assertTransferStructure transferCircom

  -- Generate approve circuit
  let approveBinding ← match getBinding spec 1 with
    | some b => pure b
    | none => throw (IO.userError "approve binding not found")
  let approveCircom ← match Compiler.Circom.emitCircom spec approveBinding "0x095ea7b3" with
    | some c => pure c
    | none => throw (IO.userError "Circom generation failed for approve")
  assertApproveStructure approveCircom

  -- Generate transferFrom circuit (3-parameter: address, address, uint256)
  let transferFromBinding ← match getBinding spec 2 with
    | some b => pure b
    | none => throw (IO.userError "transferFrom binding not found")
  let transferFromCircom ← match Compiler.Circom.emitCircom spec transferFromBinding "0x23b872dd" with
    | some c => pure c
    | none => throw (IO.userError "Circom generation failed for transferFrom")
  assertTransferFromStructure transferFromCircom

  -- Verify emitCircom returns none for invalid bindings
  let badBinding : IntentBinding := { functionName := "fake", intentFn := "nonexistent" }
  match Compiler.Circom.emitCircom spec badBinding "0x00000000" with
  | some _ => throw (IO.userError "expected none for invalid binding")
  | none => pure ()

  -- === Ledger Contract ===
  let ledgerSpec := Contracts.Ledger.intentSpec

  -- Generate deposit circuit (single uint256 param, unconditional)
  let depositBinding ← match getBinding ledgerSpec 0 with
    | some b => pure b
    | none => throw (IO.userError "deposit binding not found")
  let depositCircom ← match Compiler.Circom.emitCircom ledgerSpec depositBinding "0xb6b55f25" with
    | some c => pure c
    | none => throw (IO.userError "Circom generation failed for deposit")
  assertDepositStructure depositCircom

  -- Generate withdraw circuit (single uint256 param, unconditional)
  let withdrawBinding ← match getBinding ledgerSpec 1 with
    | some b => pure b
    | none => throw (IO.userError "withdraw binding not found")
  let withdrawCircom ← match Compiler.Circom.emitCircom ledgerSpec withdrawBinding "0x2e1a7d4d" with
    | some c => pure c
    | none => throw (IO.userError "Circom generation failed for withdraw")
  assertWithdrawStructure withdrawCircom

  -- Generate Ledger transfer circuit (address + uint256, conditional)
  let ledgerTransferBinding ← match getBinding ledgerSpec 2 with
    | some b => pure b
    | none => throw (IO.userError "ledger transfer binding not found")
  let ledgerTransferCircom ← match Compiler.Circom.emitCircom ledgerSpec ledgerTransferBinding "0xa9059cbb" with
    | some c => pure c
    | none => throw (IO.userError "Circom generation failed for ledger transfer")
  assertLedgerTransferStructure ledgerTransferCircom

  -- === ERC-721 (production intentSpec) ===
  let erc721Spec := Contracts.ERC721.intentSpec

  -- Generate approve circuit (address + uint256, unconditional)
  let erc721ApproveBinding ← match getBinding erc721Spec 0 with
    | some b => pure b
    | none => throw (IO.userError "ERC-721 approve binding not found")
  let erc721ApproveCircom ← match Compiler.Circom.emitCircom erc721Spec erc721ApproveBinding "0x095ea7b3" with
    | some c => pure c
    | none => throw (IO.userError "Circom generation failed for ERC-721 approve")
  assertERC721ApproveStructure erc721ApproveCircom

  -- Generate setApprovalForAll circuit (address + bool, conditional)
  let setApprovalBinding ← match getBinding erc721Spec 1 with
    | some b => pure b
    | none => throw (IO.userError "setApprovalForAll binding not found")
  let setApprovalCircom ← match Compiler.Circom.emitCircom erc721Spec setApprovalBinding "0xa22cb465" with
    | some c => pure c
    | none => throw (IO.userError "Circom generation failed for setApprovalForAll")
  assertSetApprovalForAllStructure setApprovalCircom

  -- Generate transferFrom circuit (address + address + uint256, unconditional)
  let erc721TransferFromBinding ← match getBinding erc721Spec 2 with
    | some b => pure b
    | none => throw (IO.userError "ERC-721 transferFrom binding not found")
  let erc721TransferFromCircom ← match Compiler.Circom.emitCircom erc721Spec erc721TransferFromBinding "0x23b872dd" with
    | some c => pure c
    | none => throw (IO.userError "Circom generation failed for ERC-721 transferFrom")
  assertERC721TransferFromStructure erc721TransferFromCircom

  -- All assertions passed. Print status messages first, then headers+circom.
  IO.println "✓ TransferIntent: all structural checks pass"
  IO.println "✓ ApproveIntent: all structural checks pass"
  IO.println "✓ TransferFromIntent: all structural checks pass"
  IO.println "✓ Invalid binding correctly returns none"
  IO.println "✓ DepositIntent: all structural checks pass"
  IO.println "✓ WithdrawIntent: all structural checks pass"
  IO.println "✓ Ledger TransferIntent: all structural checks pass"
  IO.println "✓ ERC-721 ApproveIntent: all structural checks pass"
  IO.println "✓ SetApprovalForAllIntent: all structural checks pass"
  IO.println "✓ ERC-721 TransferFromIntent: all structural checks pass"
  IO.println "=== Generated Circom for ERC20.transfer ==="
  IO.println transferCircom
  IO.println "=== Generated Circom for ERC20.approve ==="
  IO.println approveCircom
  IO.println "=== Generated Circom for ERC20.transferFrom ==="
  IO.println transferFromCircom
  IO.println "=== Generated Circom for Ledger.deposit ==="
  IO.println depositCircom
  IO.println "=== Generated Circom for Ledger.withdraw ==="
  IO.println withdrawCircom
  IO.println "=== Generated Circom for Ledger.transfer ==="
  IO.println ledgerTransferCircom
  IO.println "=== Generated Circom for ERC721.approve ==="
  IO.println erc721ApproveCircom
  IO.println "=== Generated Circom for ERC721.setApprovalForAll ==="
  IO.println setApprovalCircom
  IO.println "=== Generated Circom for ERC721.transferFrom ==="
  IO.println erc721TransferFromCircom

end Compiler.CircomTest
