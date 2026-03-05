import Compiler.ABI
import Compiler.Selector
import Compiler.Hex
import Contracts.MacroContracts.Core
import Contracts.MacroContracts.Tokens
import Contracts.MacroContracts.Smoke

namespace Compiler.MacroTranslateInvariantTest

open Compiler
open Compiler.CompilationModel
open Compiler.Hex

private def contains (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then true
  else
    let rec go : List Char → Bool
      | [] => false
      | c :: cs =>
        if (c :: cs).take n.length == n then true
        else go cs
    go h

private def countOccurrences (haystack needle : String) : Nat :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then 0
  else
    let rec go : List Char → Nat
      | [] => 0
      | c :: cs =>
        if (c :: cs).take n.length == n then
          1 + go cs
        else
          go cs
    go h

private def expectTrue (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"✗ {label}")
  IO.println s!"✓ {label}"

private def allDistinct [DecidableEq α] (xs : List α) : Bool :=
  xs.length == xs.eraseDups.length

private def externalFunctions (spec : CompilationModel) : List FunctionSpec :=
  spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)

private def canonicalFieldSlots (spec : CompilationModel) : List Nat :=
  let indexed := List.zip (List.range spec.fields.length) spec.fields
  indexed.map (fun (idx, field) => field.slot.getD idx)

private def writeSlots (spec : CompilationModel) : List Nat :=
  let indexed := List.zip (List.range spec.fields.length) spec.fields
  indexed.flatMap (fun (idx, field) => field.slot.getD idx :: field.aliasSlots)

private def macroSpecs : List CompilationModel :=
  [ Contracts.MacroContracts.SimpleStorage.spec
  , Contracts.MacroContracts.Counter.spec
  , Contracts.MacroContracts.Owned.spec
  , Contracts.MacroContracts.Ledger.spec
  , Contracts.MacroContracts.SafeCounter.spec
  , Contracts.MacroContracts.OwnedCounter.spec
  , Contracts.MacroContracts.SimpleToken.spec
  , Contracts.MacroContracts.ERC20.spec
  , Contracts.MacroContracts.ERC721.spec
  , Contracts.MacroContracts.UintMapSmoke.spec
  , Contracts.MacroContracts.Bytes32Smoke.spec
  , Contracts.MacroContracts.MappingWordSmoke.spec
  , Contracts.MacroContracts.StorageWordsSmoke.spec
  , Contracts.MacroContracts.TupleSmoke.spec
  , Contracts.MacroContracts.Uint8Smoke.spec
  ]

private def functionSignature (fn : FunctionSpec) : String :=
  let params := fn.params.map (fun p => paramTypeToSolidityString p.ty)
  let paramStr := String.intercalate "," params
  s!"{fn.name}({paramStr})"

private def expectedExternalSignatures : List (String × List String) :=
  [ ("SimpleStorage", ["store(uint256)", "retrieve()"])
  , ("Counter", ["increment()", "decrement()", "getCount()", "previewAddTwice(uint256)",
      "previewOps(uint256,uint256,uint256)", "previewEnvOps(uint256,uint256)",
      "previewLowLevel(uint256,uint256)"])
  , ("Owned", ["transferOwnership(address)", "getOwner()"])
  , ("Ledger", ["deposit(uint256)", "withdraw(uint256)", "transfer(address,uint256)", "getBalance(address)"])
  , ("SafeCounter", ["increment()", "decrement()", "getCount()"])
  , ("OwnedCounter", ["increment()", "decrement()", "getCount()", "getOwner()", "transferOwnership(address)"])
  , ("SimpleToken", ["mint(address,uint256)", "transfer(address,uint256)", "balanceOf(address)", "totalSupply()",
      "owner()"])
  , ("ERC20", ["mint(address,uint256)", "transfer(address,uint256)", "approve(address,uint256)",
      "transferFrom(address,address,uint256)", "balanceOf(address)", "allowanceOf(address,address)",
      "totalSupply()", "owner()"])
  , ("ERC721", ["ownerOf(uint256)", "getApproved(uint256)", "approve(uint256,uint256)", "mint(uint256)",
      "transferFrom(uint256,uint256,uint256)"])
  , ("UintMapSmoke", ["setValue(uint256,uint256)", "getValue(uint256)"])
  , ("Bytes32Smoke", ["setDigest(bytes32)", "getDigest()"])
  , ("MappingWordSmoke", ["setWord1(uint256,uint256)", "getWord1(uint256)", "isWord1NonZero(uint256)"])
  , ("StorageWordsSmoke", ["extSloadsLike(bytes32[])"])
  , ("TupleSmoke", ["setFromPair((uint256,uint256))", "getPair(uint256)", "processConfig((address,address,uint256))"])
  , ("Uint8Smoke", ["acceptSig((uint8,bytes32,bytes32))", "sigV()"])
  ]

private def expectedExternalSelectors : List (String × List String) :=
  [ ("SimpleStorage", ["0x6057361d", "0x2e64cec1"])
  , ("Counter", ["0xd09de08a", "0x2baeceb7", "0xa87d942c", "0x04a34e04", "0x8022f026", "0x0a7486d3", "0x9d4825af"])
  , ("Owned", ["0xf2fde38b", "0x893d20e8"])
  , ("Ledger", ["0xb6b55f25", "0x2e1a7d4d", "0xa9059cbb", "0xf8b2cb4f"])
  , ("SafeCounter", ["0xd09de08a", "0x2baeceb7", "0xa87d942c"])
  , ("OwnedCounter", ["0xd09de08a", "0x2baeceb7", "0xa87d942c", "0x893d20e8", "0xf2fde38b"])
  , ("SimpleToken", ["0x40c10f19", "0xa9059cbb", "0x70a08231", "0x18160ddd", "0x8da5cb5b"])
  , ("ERC20", ["0x40c10f19", "0xa9059cbb", "0x095ea7b3", "0x23b872dd", "0x70a08231", "0x1a46ec82", "0x18160ddd",
      "0x8da5cb5b"])
  , ("ERC721", ["0x6352211e", "0x081812fc", "0x5d35a3d9", "0xa0712d68", "0x310ed7f0"])
  , ("UintMapSmoke", ["0x7b8d56e3", "0x0ff4c916"])
  , ("Bytes32Smoke", ["0xed9fdc05", "0xae0d3e27"])
  , ("MappingWordSmoke", ["0x60ab11c4", "0x8f8a322f", "0xea3aded7"])
  , ("StorageWordsSmoke", ["0x764fa434"])
  , ("TupleSmoke", ["0x712ea680", "0xbdf391cc", "0x01b427d2"])
  , ("Uint8Smoke", ["0xc233eaa7", "0x62fc458b"])
  ]

private def expectedFor
    (table : List (String × List String)) (contractName : String) : Option (List String) :=
  (table.find? (fun entry => entry.1 == contractName)).map (·.2)

-- Regression: `verity_contract` elaboration emits field-level findIdx simp lemmas.
#check Contracts.MacroContracts.OwnedCounter.findIdx_owner_OwnedCounter
#check Contracts.MacroContracts.OwnedCounter.findIdx_owner_OwnedCounter_decide
#check Contracts.MacroContracts.SimpleToken.findIdx_balancesSlot_SimpleToken
#check Contracts.MacroContracts.SimpleToken.findIdx_balancesSlot_SimpleToken_decide
-- Regression: `verity_contract` elaboration emits parameter-level findIdx simp lemmas.
#check Contracts.MacroContracts.OwnedCounter.findIdx_param_initialOwner_constructor_OwnedCounter
#check Contracts.MacroContracts.OwnedCounter.findIdx_param_newOwner_transferOwnership_OwnedCounter
#check Contracts.MacroContracts.Ledger.findIdx_param_to_transfer_Ledger
#check Contracts.MacroContracts.Ledger.findIdx_param_amount_transfer_Ledger_decide

private def checkSpec (spec : CompilationModel) : IO Unit := do
  let extFns := externalFunctions spec
  let fnNames := extFns.map (·.name)
  expectTrue s!"{spec.name}: external function names are unique" (allDistinct fnNames)

  let fieldNames := spec.fields.map (·.name)
  expectTrue s!"{spec.name}: field names are unique" (allDistinct fieldNames)

  let slots := canonicalFieldSlots spec
  expectTrue s!"{spec.name}: canonical storage slots are unique" (allDistinct slots)

  let writes := writeSlots spec
  expectTrue s!"{spec.name}: write slots are unique (canonical + alias)" (allDistinct writes)

  let selectors ← Selector.computeSelectors spec
  expectTrue s!"{spec.name}: selectors are unique" (allDistinct selectors)
  expectTrue s!"{spec.name}: selector count matches external function count"
    (selectors.length == extFns.length)

  let signatures := extFns.map functionSignature
  match expectedFor expectedExternalSignatures spec.name with
  | none =>
      throw (IO.userError s!"✗ {spec.name}: missing expected external signature snapshot entry")
  | some expectedSigs =>
      expectTrue s!"{spec.name}: external signatures match pinned snapshot"
        (signatures == expectedSigs)

  let selectorHexes := selectors.map natToHex
  match expectedFor expectedExternalSelectors spec.name with
  | none =>
      throw (IO.userError s!"✗ {spec.name}: missing expected selector snapshot entry")
  | some expectedHexes =>
      expectTrue s!"{spec.name}: selectors match pinned snapshot"
        (selectorHexes == expectedHexes)

  let compileResult ← Selector.compileChecked spec selectors
  match compileResult with
  | .ok ir =>
      IO.println s!"✓ {spec.name}: compileChecked succeeds with canonical selectors"
      let irFns := ir.functions
      let irFnNames := irFns.map (·.name)
      let irSelectors := irFns.map (·.selector)
      expectTrue s!"{spec.name}: IR external function count matches spec external function count"
        (irFns.length == extFns.length)
      expectTrue s!"{spec.name}: IR external function names preserve spec order"
        (irFnNames == fnNames)
      expectTrue s!"{spec.name}: IR selectors preserve canonical selector order"
        (irSelectors == selectors)
  | .error err =>
      throw (IO.userError s!"✗ {spec.name}: compileChecked failed: {err}")

  let abi := ABI.emitContractABIJson spec
  let abiFunctionCount := countOccurrences abi "\"type\": \"function\""
  expectTrue s!"{spec.name}: ABI function count matches external function count"
    (abiFunctionCount == extFns.length)

  -- Sanity-check ABI output contains each external function name.
  let allNamesPresent :=
    fnNames.all (fun fnName => contains abi s!"\"name\": \"{fnName}\"")
  expectTrue s!"{spec.name}: ABI contains every external function name" allNamesPresent

#eval! do
  expectTrue "macro spec count matches pinned signature snapshot"
    (macroSpecs.length == expectedExternalSignatures.length)
  expectTrue "macro spec count matches pinned selector snapshot"
    (macroSpecs.length == expectedExternalSelectors.length)
  for spec in macroSpecs do
    checkSpec spec

end Compiler.MacroTranslateInvariantTest
