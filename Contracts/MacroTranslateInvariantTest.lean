import Compiler.ABI
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.Equivalence
import Compiler.Selector
import Compiler.Hex
import Contracts
import Contracts.Smoke
import Contracts.StringSmoke

namespace Compiler.MacroTranslateInvariantTest

open Compiler
open Compiler.CompilationModel
open Compiler.Hex
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration

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

private def bodyUsesAddressStorageRead (body : List Stmt) : Bool :=
  contains (reprStr body) "Expr.storageAddr"

private def bodyUsesAddressStorageWrite (body : List Stmt) : Bool :=
  contains (reprStr body) "Stmt.setStorageAddr"

private def canonicalFieldSlots (spec : CompilationModel) : List Nat :=
  let indexed := List.zip (List.range spec.fields.length) spec.fields
  indexed.map (fun (idx, field) => field.slot.getD idx)

private def writeSlots (spec : CompilationModel) : List Nat :=
  let indexed := List.zip (List.range spec.fields.length) spec.fields
  indexed.flatMap (fun (idx, field) => field.slot.getD idx :: field.aliasSlots)

private def isMappingLike : FieldType → Bool
  | .mappingTyped _ => true
  | .mappingStruct _ _ => true
  | .mappingStruct2 _ _ _ => true
  | _ => false

private def mappingBaseSlots (spec : CompilationModel) : List Nat :=
  let indexed := List.zip (List.range spec.fields.length) spec.fields
  indexed.filterMap (fun (idx, field) =>
    if isMappingLike field.ty then some (field.slot.getD idx) else none)

private def functionUsesMappingSlot (fn : IRFunction) : Bool :=
  contains (reprStr fn.body) "mappingSlot"

private def seedFromName (name : String) : Nat :=
  name.toList.foldl (fun acc ch => acc * 131 + ch.toNat) 0

private def rngMask : Nat := (2 ^ 64) - 1

private def nextSeed (seed : Nat) : Nat :=
  ((seed * 6364136223846793005) + 1442695040888963407) &&& rngMask

private def randBound (seed bound : Nat) : Nat × Nat :=
  let seed' := nextSeed seed
  if bound = 0 then (0, seed') else (seed' % bound, seed')

private def randWord (seed : Nat) : Nat × Nat :=
  let s1 := nextSeed seed
  let s2 := nextSeed s1
  (((s1 &&& rngMask) <<< 64) + (s2 &&& rngMask), s2)

private def genArgs (count : Nat) (seed : Nat) : List Nat × Nat :=
  match count with
  | 0 => ([], seed)
  | n + 1 =>
      let (v, seed') := randWord seed
      let (rest, seed'') := genArgs n seed'
      (v :: rest, seed'')

private def mkRandomTx (extFns : List FunctionSpec) (selectors : List Nat)
    (seed : Nat) : IRTransaction × Nat :=
  if extFns.isEmpty then
    ({ sender := 0, functionSelector := 0, args := [] }, nextSeed seed)
  else
    let (fnIdx, seed1) := randBound seed extFns.length
    let fn := extFns.getD fnIdx { name := "", params := [], returnType := none, returns := [], body := [] }
    let selector := selectors.getD fnIdx 0
    let (sender, seed2) := randWord seed1
    let (args, seed3) := genArgs fn.params.length seed2
    ({ sender := sender, functionSelector := selector, args := args }, seed3)

private def seededStorage (seed : Nat) (slotIdx : Nat) : Nat :=
  let mix := seed + slotIdx * 0x9e3779b97f4a7c15 + 0xbf58476d1ce4e5b9
  mix % (2 ^ 256)

private def observedSlotsForTx (spec : CompilationModel) (_tx : IRTransaction) : List Nat :=
  (canonicalFieldSlots spec ++ writeSlots spec).eraseDups

private def mappingKeyCandidatesForTx (_spec : CompilationModel) (_tx : IRTransaction) : List (Prod Nat Nat) :=
  []

private def mkIRResultFromExec (rollback : IRState) (r : IRExecResult) : IRResult :=
  match r with
  | .continue s =>
      { success := true
        returnValue := s.returnValue
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .return v s =>
      { success := true
        returnValue := some v
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .stop s =>
      { success := true
        returnValue := none
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .revert _ =>
      { success := false
        returnValue := none
        finalStorage := rollback.storage
        finalMappings := Compiler.Proofs.storageAsMappings rollback.storage
        events := rollback.events }

private def mkYulResultFromExec (rollback : YulState) (r : YulExecResult) : YulResult :=
  match r with
  | .continue s =>
      { success := true
        returnValue := s.returnValue
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .return v s =>
      { success := true
        returnValue := some v
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .stop s =>
      { success := true
        returnValue := none
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .revert _ =>
      { success := false
        returnValue := none
        finalStorage := rollback.storage
        finalMappings := Compiler.Proofs.storageAsMappings rollback.storage
        events := rollback.events }

private def withTxContext (state : IRState) (tx : IRTransaction) : IRState :=
  { state with
    calldata := tx.args
    sender := tx.sender
    msgValue := tx.msgValue
    thisAddress := tx.thisAddress
    blockTimestamp := tx.blockTimestamp
    blockNumber := tx.blockNumber
    chainId := tx.chainId
    selector := tx.functionSelector }

private def execIRFunctionFuelResult (fn : IRFunction) (args : List Nat) (initialState : IRState)
    (fuel : Nat) : IRResult :=
  let stateWithParams := fn.params.zip args |>.foldl (fun s (p, v) => s.setVar p.name v) initialState
  mkIRResultFromExec initialState (execIRStmts fuel stateWithParams fn.body)

private def interpretIRFuelResult (contract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (fuel : Nat) : IRResult :=
  let state := withTxContext initialState tx
  match contract.functions.find? (fun f => f.selector == tx.functionSelector) with
  | some fn => execIRFunctionFuelResult fn tx.args state fuel
  | none =>
      { success := false
        returnValue := none
        finalStorage := state.storage
        finalMappings := Compiler.Proofs.storageAsMappings state.storage
        events := state.events }

private def interpretYulFromIRFuelResult (contract : IRContract) (tx : IRTransaction) (state : IRState)
    (fuel : Nat) : YulResult :=
  let yulTx : YulTransaction := {
    sender := tx.sender
    msgValue := tx.msgValue
    thisAddress := tx.thisAddress
    blockTimestamp := tx.blockTimestamp
    blockNumber := tx.blockNumber
    chainId := tx.chainId
    functionSelector := tx.functionSelector
    args := tx.args
  }
  let yulInit := YulState.initial yulTx state.storage state.events
  mkYulResultFromExec yulInit (execYulStmtsFuel fuel yulInit (Compiler.runtimeCode contract))

private def diffCheckTx (spec : CompilationModel) (ir : IRContract)
    (tx : IRTransaction) (seed : Nat) : Bool :=
  let initState : IRState :=
    { vars := [],
      «storage» := seededStorage seed,
      memory := fun _ => 0,
      calldata := [],
      returnValue := none,
      sender := tx.sender,
      msgValue := tx.msgValue,
      thisAddress := tx.thisAddress,
      blockTimestamp := tx.blockTimestamp,
      blockNumber := tx.blockNumber,
      chainId := tx.chainId,
      selector := 0,
      events := [] }
  let irResult := interpretIRFuelResult ir tx initState 800
  let yulResult := interpretYulFromIRFuelResult ir tx initState 800
  let slots := observedSlotsForTx spec tx
  let mappingKeys := mappingKeyCandidatesForTx spec tx
  resultsMatchOn slots mappingKeys irResult yulResult

private def runRandomDiffChecks (spec : CompilationModel) (ir : IRContract)
    (extFns : List FunctionSpec) (selectors : List Nat) (count : Nat) : IO Unit := do
  let rec loop (remaining : Nat) (seed : Nat) (idx : Nat) : IO Unit := do
    if remaining = 0 then
      pure ()
    else
      let txSeed := mkRandomTx extFns selectors seed
      let tx := txSeed.1
      let seed' := txSeed.2
      let ok := diffCheckTx spec ir tx (seed + idx + 1)
      expectTrue
        s!"{spec.name}: randomized IR↔Yul differential check {idx + 1}/{count}"
        ok
      loop (remaining - 1) seed' (idx + 1)
  loop count (seedFromName spec.name) 0

private def macroSpecs : List CompilationModel :=
  [ Contracts.SimpleStorage.spec
  , Contracts.Counter.spec
  , Contracts.Owned.spec
  , Contracts.Ledger.spec
  , Contracts.Vault.spec
  , Contracts.SafeCounter.spec
  , Contracts.OwnedCounter.spec
  , Contracts.SimpleToken.spec
  , Contracts.ERC20.spec
  , Contracts.ERC721.spec
  , Contracts.Smoke.UintMapSmoke.spec
  , Contracts.Smoke.Bytes32Smoke.spec
  , Contracts.Smoke.MappingWordSmoke.spec
  , Contracts.Smoke.StorageWordsSmoke.spec
  , Contracts.Smoke.CustomErrorSmoke.spec
  , Contracts.Smoke.StatelessSmoke.spec
  , Contracts.Smoke.InitializerSmoke.spec
  , Contracts.Smoke.ConstantSmoke.spec
  , Contracts.Smoke.ImmutableSmoke.spec
  , Contracts.Smoke.TypedImmutableSmoke.spec
  , Contracts.StringSmoke.spec
  , Contracts.Smoke.TupleSmoke.spec
  , Contracts.Smoke.Uint8Smoke.spec
  , Contracts.Smoke.AddressHelpersSmoke.spec
  , Contracts.Smoke.ZeroAddressShadowSmoke.spec
  , Contracts.Smoke.StructMappingSmoke.spec
  , Contracts.Smoke.ExternalCallSmoke.spec
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
  , ("Vault", ["deposit(uint256)", "withdraw(uint256)", "balanceOf(address)", "totalAssets()", "totalSupply()"])
  , ("SafeCounter", ["increment()", "decrement()", "getCount()"])
  , ("OwnedCounter", ["increment()", "decrement()", "getCount()", "getOwner()", "transferOwnership(address)"])
  , ("SimpleToken", ["mint(address,uint256)", "transfer(address,uint256)", "balanceOf(address)", "totalSupply()",
      "owner()"])
  , ("ERC20", ["mint(address,uint256)", "transfer(address,uint256)", "approve(address,uint256)",
      "transferFrom(address,address,uint256)", "balanceOf(address)", "allowanceOf(address,address)",
      "totalSupply()", "owner()"])
  , ("ERC721", ["balanceOf(address)", "ownerOf(uint256)", "getApproved(uint256)",
      "isApprovedForAll(address,address)", "approve(address,uint256)", "setApprovalForAll(address,bool)",
      "mint(address)", "transferFrom(address,address,uint256)"])
  , ("UintMapSmoke", ["setValue(uint256,uint256)", "getValue(uint256)"])
  , ("Bytes32Smoke", ["setDigest(bytes32)", "getDigest()"])
  , ("MappingWordSmoke", ["setWord1(uint256,uint256)", "getWord1(uint256)", "isWord1NonZero(uint256)"])
  , ("StorageWordsSmoke", ["extSloadsLike(bytes32[])"])
  , ("CustomErrorSmoke", ["echo(uint256)"])
  , ("StatelessSmoke", ["echoWord(uint256)", "whoAmI()"])
  , ("InitializerSmoke", ["initOwner(address)", "upgradeToV2()"])
  , ("ConstantSmoke", ["feeOn(uint256)", "treasuryAddr()"])
  , ("ImmutableSmoke", ["supplyCap()", "treasuryAddr()", "shadowed(uint256)"])
  , ("TypedImmutableSmoke", ["isPaused()", "feeScale()", "domainSeparator()"])
  , ("StringSmoke", ["echoString(string)"])
  , ("TupleSmoke", ["setFromPair((uint256,uint256))", "getPair(uint256)", "processConfig((address,address,uint256))"])
  , ("Uint8Smoke", ["acceptSig((uint8,bytes32,bytes32))", "sigV()"])
  , ("AddressHelpersSmoke", ["setDelegate(address,address)", "getDelegate(address)", "clearDelegate(address)",
      "hasDelegate(address)", "isDelegateZero(address)", "setOwnerForId(uint256,address)", "getOwnerForId(uint256)"])
  , ("ZeroAddressShadowSmoke", ["shadowWrite(address)"])
  , ("StructMappingSmoke", ["setPosition(address,uint256,uint256,address)", "totalPositionShares(address)",
      "delegateOf(address)", "setApproval(address,address,uint256,uint256)", "approvalOf(address,address)",
      "approvalNonce(address,address)"])
  , ("ExternalCallSmoke", ["storeEcho(uint256)", "getEchoedValue()"])
  ]

private def expectedExternalSelectors : List (String × List String) :=
  [ ("SimpleStorage", ["0x6057361d", "0x2e64cec1"])
  , ("Counter", ["0xd09de08a", "0x2baeceb7", "0xa87d942c", "0x04a34e04", "0x8022f026", "0x0a7486d3", "0x9d4825af"])
  , ("Owned", ["0xf2fde38b", "0x893d20e8"])
  , ("Ledger", ["0xb6b55f25", "0x2e1a7d4d", "0xa9059cbb", "0xf8b2cb4f"])
  , ("Vault", ["0xb6b55f25", "0x2e1a7d4d", "0x70a08231", "0x01e1d114", "0x18160ddd"])
  , ("SafeCounter", ["0xd09de08a", "0x2baeceb7", "0xa87d942c"])
  , ("OwnedCounter", ["0xd09de08a", "0x2baeceb7", "0xa87d942c", "0x893d20e8", "0xf2fde38b"])
  , ("SimpleToken", ["0x40c10f19", "0xa9059cbb", "0x70a08231", "0x18160ddd", "0x8da5cb5b"])
  , ("ERC20", ["0x40c10f19", "0xa9059cbb", "0x095ea7b3", "0x23b872dd", "0x70a08231", "0x1a46ec82", "0x18160ddd",
      "0x8da5cb5b"])
  , ("ERC721", ["0x70a08231", "0x6352211e", "0x081812fc", "0xe985e9c5", "0x095ea7b3", "0xa22cb465",
      "0x6a627842", "0x23b872dd"])
  , ("UintMapSmoke", ["0x7b8d56e3", "0x0ff4c916"])
  , ("Bytes32Smoke", ["0xed9fdc05", "0xae0d3e27"])
  , ("MappingWordSmoke", ["0x60ab11c4", "0x8f8a322f", "0xea3aded7"])
  , ("StorageWordsSmoke", ["0x764fa434"])
  , ("CustomErrorSmoke", ["0x6279e43c"])
  , ("StatelessSmoke", ["0x26534f53", "0xda91254c"])
  , ("InitializerSmoke", ["0x0d009297", "0xcc01053e"])
  , ("ConstantSmoke", ["0x9c421eb5", "0x30d9a62a"])
  , ("ImmutableSmoke", ["0x8f770ad0", "0x30d9a62a", "0x655b96ec"])
  , ("TypedImmutableSmoke", ["0xb187bd26", "0x95f39ba4", "0xf698da25"])
  , ("StringSmoke", ["0x0d7e2fce"])
  , ("TupleSmoke", ["0x712ea680", "0xbdf391cc", "0x01b427d2"])
  , ("Uint8Smoke", ["0xc233eaa7", "0x62fc458b"])
  , ("AddressHelpersSmoke", ["0x5c873849", "0x544d8564", "0xcc21cc2a", "0x480005cd", "0x67129177",
      "0x0b0126c5", "0x85a9cdd0"])
  , ("ZeroAddressShadowSmoke", ["0xc0aab575"])
  , ("StructMappingSmoke", ["0x468c900e", "0xe7933b6a", "0x8d22ea2a", "0xf4536007", "0xcb01943e",
      "0x6c241120"])
  , ("ExternalCallSmoke", ["0x32fdff86", "0x21209dbd"])
  ]

private def expectedFor
    (table : List (String × List String)) (contractName : String) : Option (List String) :=
  (table.find? (fun entry => entry.1 == contractName)).map (·.2)

-- Regression: `verity_contract` elaboration emits field-level findIdx simp lemmas.
private def _findIdxFieldRegression1 := Contracts.OwnedCounter.findIdx_owner_OwnedCounter
private def _findIdxFieldRegression2 := Contracts.OwnedCounter.findIdx_owner_OwnedCounter_decide
private def _findIdxFieldRegression3 := Contracts.SimpleToken.findIdx_balancesSlot_SimpleToken
private def _findIdxFieldRegression4 := Contracts.SimpleToken.findIdx_balancesSlot_SimpleToken_decide
-- Regression: `verity_contract` elaboration emits parameter-level findIdx simp lemmas.
private def _findIdxParamRegression1 := Contracts.OwnedCounter.findIdx_param_initialOwner_constructor_OwnedCounter
private def _findIdxParamRegression2 := Contracts.OwnedCounter.findIdx_param_newOwner_transferOwnership_OwnedCounter
private def _findIdxParamRegression3 := Contracts.Ledger.findIdx_param_to_transfer_Ledger
private def _findIdxParamRegression4 := Contracts.Ledger.findIdx_param_amount_transfer_Ledger_decide

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
      let indexedFns := List.zip (List.range extFns.length) extFns
      let mappingSafeFns :=
        indexedFns.filterMap (fun (idx, fnSpec) =>
          match irFns[idx]?, selectors[idx]? with
          | some irFn, some sel =>
              if functionUsesMappingSlot irFn then none else some (fnSpec, sel)
          | _, _ => none)
      let mappingSafeExtFns := mappingSafeFns.map Prod.fst
      let mappingSafeSelectors := mappingSafeFns.map Prod.snd
      if (mappingBaseSlots spec).isEmpty then
        expectTrue s!"{spec.name}: all external functions are mapping-slot free"
          (mappingSafeExtFns.length == extFns.length)
        runRandomDiffChecks spec ir extFns selectors 8
      else if mappingSafeExtFns.isEmpty then
        IO.println s!"ℹ {spec.name}: skipping randomized IR↔Yul checks (all external functions touch mappingSlot/keccak path in #eval)"
      else
        IO.println s!"ℹ {spec.name}: randomized IR↔Yul checks use mapping-safe subset {mappingSafeExtFns.length}/{extFns.length}"
        runRandomDiffChecks spec ir mappingSafeExtFns mappingSafeSelectors 8
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

  if spec.name == "CustomErrorSmoke" then
    expectTrue
      "CustomErrorSmoke: macro spec preserves custom error declarations"
      (spec.errors.map (·.name) == ["NonPositive", "AmountTooLarge"])
    expectTrue
      "CustomErrorSmoke: ABI includes declared custom errors"
      (contains abi "\"type\": \"error\"" &&
        contains abi "\"name\": \"NonPositive\"" &&
        contains abi "\"name\": \"AmountTooLarge\"")
  else
    pure ()

#eval! do
  expectTrue "macro spec count matches pinned signature snapshot"
    (macroSpecs.length == expectedExternalSignatures.length)
  expectTrue "macro spec count matches pinned selector snapshot"
    (macroSpecs.length == expectedExternalSelectors.length)
  expectTrue
    "Owned.getOwner keeps address storage reads explicit in macro output"
    (bodyUsesAddressStorageRead Contracts.Owned.getOwner_modelBody)
  expectTrue
    "Owned.transferOwnership keeps address storage writes explicit in macro output"
    (bodyUsesAddressStorageWrite Contracts.Owned.transferOwnership_modelBody)
  for spec in macroSpecs do
    checkSpec spec

end Compiler.MacroTranslateInvariantTest
