/-
  Compiler.ERC7730Test: Regression tests for the ERC-7730 JSON generator.

  Uses the ERC-20, Ledger, and ERC-721 example IntentSpecs to generate
  ERC-7730 clear-signing JSON and verify key structural properties at build time.
  These tests catch regressions in the JSON generator without requiring
  external tools.
-/
import Compiler.ERC7730
import Verity.Intent.Example
import Contracts.Ledger.Display

namespace Compiler.ERC7730Test

open Verity.Intent
open Verity.Intent.Example

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- Verify structural properties of the ERC-20 ERC-7730 JSON. -/
private def assertERC20Structure (json : String) : IO Unit := do
  unless hasSubstr json "\"$schema\"" do
    throw (IO.userError "missing $schema field")
  unless hasSubstr json "erc7730-v1.schema.json" do
    throw (IO.userError "missing schema URL")
  unless hasSubstr json "\"display\"" do
    throw (IO.userError "missing display section")
  unless hasSubstr json "\"formats\"" do
    throw (IO.userError "missing formats section")
  -- Check selectors are present
  unless hasSubstr json "0xa9059cbb" do
    throw (IO.userError "missing transfer selector 0xa9059cbb")
  unless hasSubstr json "0x095ea7b3" do
    throw (IO.userError "missing approve selector 0x095ea7b3")
  unless hasSubstr json "0x23b872dd" do
    throw (IO.userError "missing transferFrom selector 0x23b872dd")
  -- Check intent strings
  unless hasSubstr json "Send all tokens to {to}" do
    throw (IO.userError "missing transfer intent text")
  unless hasSubstr json "Approve {spender}" do
    throw (IO.userError "missing approve intent text")
  -- Check field format types
  unless hasSubstr json "\"tokenAmount\"" do
    throw (IO.userError "missing tokenAmount format")
  unless hasSubstr json "\"addressName\"" do
    throw (IO.userError "missing addressName format")
  -- Check $id fields
  unless hasSubstr json "\"transfer\"" do
    throw (IO.userError "missing transfer $id")
  unless hasSubstr json "\"approve\"" do
    throw (IO.userError "missing approve $id")
  unless hasSubstr json "\"transferFrom\"" do
    throw (IO.userError "missing transferFrom $id")
  -- Check metadata
  unless hasSubstr json "\"ERC20\"" do
    throw (IO.userError "missing contract name in metadata")

/-- Verify structural properties of the Ledger ERC-7730 JSON. -/
private def assertLedgerStructure (json : String) : IO Unit := do
  unless hasSubstr json "\"$schema\"" do
    throw (IO.userError "missing $schema field")
  unless hasSubstr json "\"display\"" do
    throw (IO.userError "missing display section")
  -- Check function $id entries
  unless hasSubstr json "\"deposit\"" do
    throw (IO.userError "missing deposit $id")
  unless hasSubstr json "\"withdraw\"" do
    throw (IO.userError "missing withdraw $id")
  -- Check intent strings
  unless hasSubstr json "Deposit {amount} tokens" do
    throw (IO.userError "missing deposit intent text")
  unless hasSubstr json "Withdraw {amount} tokens" do
    throw (IO.userError "missing withdraw intent text")
  unless hasSubstr json "\"Ledger\"" do
    throw (IO.userError "missing contract name in metadata")

/-- Verify structural properties of the ERC-721 ERC-7730 JSON. -/
private def assertERC721Structure (json : String) : IO Unit := do
  unless hasSubstr json "\"$schema\"" do
    throw (IO.userError "missing $schema field")
  unless hasSubstr json "\"display\"" do
    throw (IO.userError "missing display section")
  unless hasSubstr json "0xa22cb465" do
    throw (IO.userError "missing setApprovalForAll selector 0xa22cb465")
  unless hasSubstr json "\"setApprovalForAll\"" do
    throw (IO.userError "missing setApprovalForAll $id")
  unless hasSubstr json "\"addressName\"" do
    throw (IO.userError "missing addressName format for operator")

-- Test selectors matching the existing test matrix
private def erc20Selectors : List (String × String) :=
  [("transfer", "a9059cbb"), ("approve", "095ea7b3"), ("transferFrom", "23b872dd")]

private def ledgerSelectors : List (String × String) :=
  [("deposit", "b6b55f25"), ("withdraw", "2e1a7d4d"), ("transfer", "a9059cbb")]

private def erc721Selectors : List (String × String) :=
  [("setApprovalForAll", "a22cb465")]

#eval do
  -- === ERC-20 ===
  let erc20Json := Compiler.ERC7730.emitERC7730Json erc20IntentSpec erc20Selectors
  assertERC20Structure erc20Json

  -- === Ledger ===
  let ledgerSpec := Contracts.Ledger.intentSpec
  let ledgerJson := Compiler.ERC7730.emitERC7730Json ledgerSpec ledgerSelectors
  assertLedgerStructure ledgerJson

  -- === ERC-721 ===
  let erc721Json := Compiler.ERC7730.emitERC7730Json boolIntentSpec erc721Selectors
  assertERC721Structure erc721Json

  -- Verify empty selectors produce valid JSON (graceful degradation)
  let emptyJson := Compiler.ERC7730.emitERC7730Json erc20IntentSpec []
  unless hasSubstr emptyJson "\"formats\"" do
    throw (IO.userError "empty selectors should still produce formats key")

  IO.println "✓ ERC-20 ERC-7730: all structural checks pass"
  IO.println "✓ Ledger ERC-7730: all structural checks pass"
  IO.println "✓ ERC-721 ERC-7730: all structural checks pass"
  IO.println "✓ Empty selectors: graceful degradation pass"
  IO.println ""
  IO.println "=== Generated ERC-7730 for ERC20 ==="
  IO.println erc20Json
  IO.println "=== Generated ERC-7730 for Ledger ==="
  IO.println ledgerJson
  IO.println "=== Generated ERC-7730 for ERC721 ==="
  IO.println erc721Json

end Compiler.ERC7730Test
