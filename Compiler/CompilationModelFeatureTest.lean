import Compiler.CompilationModel
import Compiler.ABI
import Compiler.Codegen
import Compiler.Modules.ERC4626
import Compiler.Modules.ERC20
import Compiler.Modules.Oracle
import Compiler.Modules.Precompiles
import Compiler.Yul.PrettyPrint
import Contracts.Common
import Contracts.Counter.Counter
import Contracts.LocalObligationMacroSmoke.LocalObligationMacroSmoke
import Contracts.ProxyUpgradeabilityMacroSmoke
import Contracts.StringArrayErrorSmoke
import Contracts.StringArrayEventSmoke

namespace Compiler.CompilationModelFeatureTest

open Compiler
open Compiler.CompilationModel

namespace MacroLocalObligationSmoke

open Contracts

def constructorCarriesUncheckedObligation : Bool :=
  match LocalObligationMacroSmoke.spec.constructor with
  | some { localObligations := [{ name := "constructor_storage_layout"
                                  obligation := "Constructor storage aliasing must be checked separately across deployments."
                                  proofStatus := .unchecked }], .. } =>
      true
  | none => false
  | _ => false

example : constructorCarriesUncheckedObligation = true := by native_decide

def unsafeEdgeCarriesAssumedObligation : Bool :=
  match LocalObligationMacroSmoke.unsafeEdge_model with
  | { localObligations := [{ name := "manual_delegatecall_refinement"
                             obligation := "Caller must separately prove the handwritten assembly path refines the intended state transition."
                             proofStatus := .assumed }]
      body := [Stmt.stop], .. } => true
  | _ => false

example : unsafeEdgeCarriesAssumedObligation = true := by native_decide

def dischargedEdgeCarriesProvedObligation : Bool :=
  match LocalObligationMacroSmoke.dischargedEdge_model with
  | { localObligations := [{ name := "checked_patch_pack"
                             obligation := "Patch-pack proof already discharges this handwritten lowering boundary."
                             proofStatus := .proved }]
      body := [Stmt.setStorage "lastValue" (Expr.param "value"), Stmt.return (Expr.param "value")], .. } => true
  | _ => false

example : dischargedEdgeCarriesProvedObligation = true := by native_decide

def dischargedEdgeExecutableStillRuns : Bool :=
  match LocalObligationMacroSmoke.dischargedEdge 77 Verity.defaultState with
  | .success value state => value == 77 && state.storage 1 == 77
  | .revert _ _ => false

example : dischargedEdgeExecutableStillRuns = true := by native_decide

end MacroLocalObligationSmoke

namespace MacroProxyUpgradeabilitySmoke

open Contracts

def initProxyCarriesInitializerObligation : Bool :=
  match ProxyUpgradeabilityMacroSmoke.initProxy_model with
  | { localObligations := [{ name := "implementation_slot_discipline"
                             obligation := "Proxy storage-slot discipline must be validated against the intended implementation layout."
                             proofStatus := .assumed }]
      body := [Stmt.require (Expr.eq (Expr.storage "initializedVersion") (Expr.literal 0)) "initializer already run",
               Stmt.setStorage "initializedVersion" (Expr.literal 1),
               Stmt.setStorageAddr "admin" (Expr.param "seedAdmin"),
               Stmt.setStorageAddr "implementation" (Expr.param "seedImplementation"),
               Stmt.stop], .. } => true
  | _ => false

example : initProxyCarriesInitializerObligation = true := by native_decide

def upgradeToCarriesUpgradeObligations : Bool :=
  match ProxyUpgradeabilityMacroSmoke.upgradeTo_model with
  | { localObligations := [{ name := "upgrade_authorization"
                             obligation := "Caller must separately prove that only the intended admin can authorize upgrades."
                             proofStatus := .assumed },
                           { name := "storage_layout_compatibility"
                             obligation := "Storage-layout compatibility across versions remains a manual proof obligation."
                             proofStatus := .unchecked }]
      body := [Stmt.require (Expr.lt (Expr.storage "initializedVersion") (Expr.literal 2)) "reinitializer(2) already run",
               Stmt.setStorage "initializedVersion" (Expr.literal 2),
               Stmt.setStorageAddr "implementation" (Expr.param "newImplementation"),
               Stmt.stop], .. } => true
  | _ => false

example : upgradeToCarriesUpgradeObligations = true := by native_decide

def forwardCarriesProxyBoundary : Bool :=
  match ProxyUpgradeabilityMacroSmoke.forward_model with
  | { localObligations := [{ name := "delegatecall_refinement"
                             obligation := "Delegatecall fallback behavior must be shown to refine the selected proxy semantics."
                             proofStatus := .assumed }]
      body := body, .. } =>
      body.length == 3
  | _ => false

example : forwardCarriesProxyBoundary = true := by native_decide

def forwardExecutableReadsImplementation : Bool :=
  let seededState :=
    (ProxyUpgradeabilityMacroSmoke.initProxy (Verity.wordToAddress 11) (Verity.wordToAddress 19)).run Verity.defaultState
  match seededState with
  | .success _ state =>
      match ProxyUpgradeabilityMacroSmoke.forward 100 0 32 64 32 state with
      | .success ok nextState =>
          ok == delegatecall 100 19 0 32 64 32 &&
            nextState.storage ProxyUpgradeabilityMacroSmoke.initializedVersion.slot == 1 &&
            nextState.storageAddr ProxyUpgradeabilityMacroSmoke.admin.slot == Verity.wordToAddress 11 &&
            nextState.storageAddr ProxyUpgradeabilityMacroSmoke.implementation.slot == Verity.wordToAddress 19
      | .revert _ _ => false
  | .revert _ _ => false

example : forwardExecutableReadsImplementation = true := by native_decide

end MacroProxyUpgradeabilitySmoke

namespace CounterUnsafeBoundarySmoke

open Contracts

def previewEnvOpsCarriesBoundaryObligation : Bool :=
  match Counter.previewEnvOps_model with
  | { localObligations := [{ name := "env_memory_refinement"
                             obligation := "Caller must separately prove the direct mload-based environment digest path respects the intended memory/refinement boundary."
                             proofStatus := .assumed }]
      body := _, .. } => true
  | _ => false

example : previewEnvOpsCarriesBoundaryObligation = true := by native_decide

def previewLowLevelCarriesBoundaryObligation : Bool :=
  match Counter.previewLowLevel_model with
  | { localObligations := [{ name := "manual_low_level_refinement"
                             obligation := "Caller must separately prove the direct low-level call and returndata choreography refines the intended external-call behavior."
                             proofStatus := .assumed }]
      body := _, .. } => true
  | _ => false

example : previewLowLevelCarriesBoundaryObligation = true := by native_decide

end CounterUnsafeBoundarySmoke

namespace MacroEcrecoverSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroEcrecover where
  storage
    lastSigner : Address := slot 0

  function recoverSigner (digest : Bytes32, v : Uint256, r : Bytes32, s : Bytes32) : Address := do
    let signer ← ecrecover digest v r s
    return signer

def recoverSignerModelUsesEcrecoverEcm : Bool :=
  match MacroEcrecover.recoverSigner_modelBody with
  | [Stmt.ecm mod [Expr.param "digest", Expr.param "v", Expr.param "r", Expr.param "s"],
      Stmt.return (Expr.localVar "signer")] =>
      mod.name == "ecrecover" &&
      mod.resultVars == ["signer"] &&
      mod.axioms == ["evm_ecrecover_precompile"]
  | _ => false

example : recoverSignerModelUsesEcrecoverEcm = true := by native_decide

def recoverSignerExecutableUsesOracle : Bool :=
  match MacroEcrecover.recoverSigner 10 27 30 40 Verity.defaultState with
  | .success signer state =>
      signer == Verity.wordToAddress 107 && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : recoverSignerExecutableUsesOracle = true := by native_decide

end MacroEcrecoverSmoke

namespace MacroKeccakSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroKeccak where
  storage
    lastDigest : Uint256 := slot 0

  function hashSlice (offset : Uint256, size : Uint256) : Uint256 := do
    let digest := keccak256 offset size
    return digest

def hashSliceModelUsesKeccak : Bool :=
  match MacroKeccak.hashSlice_modelBody with
  | [Stmt.letVar "digest" (Expr.keccak256 (Expr.param "offset") (Expr.param "size")),
      Stmt.return (Expr.localVar "digest")] =>
      true
  | _ => false

example : hashSliceModelUsesKeccak = true := by native_decide

def hashSliceExecutableUsesRuntimeStub : Bool :=
  match MacroKeccak.hashSlice 11 64 Verity.defaultState with
  | .success digest state =>
      digest == 75 && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : hashSliceExecutableUsesRuntimeStub = true := by native_decide

end MacroKeccakSmoke

namespace MacroExternalSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroExternal where
  storage
    echoedValue : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function storeEcho (next : Uint256) : Unit := do
    let echoed := externalCall "echo" [next]
    setStorage echoedValue echoed

def storeEchoModelUsesDeclaredExternal : Bool :=
  (match MacroExternal.spec.externals with
    | [{ name := "echo"
         params := [ParamType.uint256]
         returnType := some ParamType.uint256
         returns := [ParamType.uint256]
         proofStatus := Compiler.ProofStatus.assumed
         axiomNames := [] }] => true
    | _ => false) &&
    match MacroExternal.storeEcho_modelBody with
    | [Stmt.letVar "echoed" (Expr.externalCall "echo" [Expr.param "next"]),
        Stmt.setStorage "echoedValue" (Expr.localVar "echoed"),
        Stmt.stop] => true
    | _ => false

example : storeEchoModelUsesDeclaredExternal = true := by native_decide

def storeEchoExecutableUsesStub : Bool :=
  match MacroExternal.storeEcho 33 Verity.defaultState with
  | .success () state =>
      state.storage 0 == 33
  | .revert _ _ => false

example : storeEchoExecutableUsesStub = true := by native_decide

end MacroExternalSmoke

namespace DynamicBytesEqUsageAnalysisSmoke

def rawLogDynamicBytesEqIsDetected : Bool :=
  stmtUsesDynamicBytesEq
    (Stmt.rawLog
      [Expr.dynamicBytesEq "lhs" "rhs"]
      (Expr.literal 0)
      (Expr.literal 32))

example : rawLogDynamicBytesEqIsDetected = true := by native_decide

end DynamicBytesEqUsageAnalysisSmoke

namespace MacroERC20Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroERC20 where
  storage
    lastBalance : Uint256 := slot 0
    lastAllowance : Uint256 := slot 1
    lastSupply : Uint256 := slot 2

  function pushTokens (token : Address, to : Address, amount : Uint256) : Unit := do
    safeTransfer token to amount

  function pullTokens (token : Address, fromAddr : Address, to : Address, amount : Uint256) : Unit := do
    safeTransferFrom token fromAddr to amount

  function approveTokens (token : Address, spender : Address, amount : Uint256) : Unit := do
    safeApprove token spender amount

  function snapshotBalance (token : Address, owner : Address) : Uint256 := do
    let balance ← balanceOf token owner
    setStorage lastBalance balance
    return balance

  function snapshotAllowance (token : Address, owner : Address, spender : Address) : Uint256 := do
    let current ← allowance token owner spender
    setStorage lastAllowance current
    return current

  function snapshotSupply (token : Address) : Uint256 := do
    let supply ← totalSupply token
    setStorage lastSupply supply
    return supply

def pushTokensModelUsesSafeTransfer : Bool :=
  match MacroERC20.pushTokens_modelBody with
  | [Stmt.ecm mod [Expr.param "token", Expr.param "to", Expr.param "amount"], Stmt.stop] =>
      mod.name == "safeTransfer" &&
      mod.resultVars.isEmpty &&
      mod.axioms == ["erc20_transfer_interface"]
  | _ => false

example : pushTokensModelUsesSafeTransfer = true := by native_decide

def pullTokensModelUsesSafeTransferFrom : Bool :=
  match MacroERC20.pullTokens_modelBody with
  | [Stmt.ecm mod [Expr.param "token", Expr.param "fromAddr", Expr.param "to", Expr.param "amount"], Stmt.stop] =>
      mod.name == "safeTransferFrom" &&
      mod.resultVars.isEmpty &&
      mod.axioms == ["erc20_transferFrom_interface"]
  | _ => false

example : pullTokensModelUsesSafeTransferFrom = true := by native_decide

def approveTokensModelUsesSafeApprove : Bool :=
  match MacroERC20.approveTokens_modelBody with
  | [Stmt.ecm mod [Expr.param "token", Expr.param "spender", Expr.param "amount"], Stmt.stop] =>
      mod.name == "safeApprove" &&
      mod.resultVars.isEmpty &&
      mod.axioms == ["erc20_approve_interface"]
  | _ => false

example : approveTokensModelUsesSafeApprove = true := by native_decide

def snapshotBalanceModelUsesBalanceOfModule : Bool :=
  match MacroERC20.snapshotBalance_modelBody with
  | [Stmt.ecm mod [Expr.param "token", Expr.param "owner"],
      Stmt.setStorage "lastBalance" (Expr.localVar "balance"),
      Stmt.return (Expr.localVar "balance")] =>
      mod.name == "balanceOf" &&
      mod.resultVars == ["balance"] &&
      mod.axioms == ["erc20_balanceOf_interface"]
  | _ => false

example : snapshotBalanceModelUsesBalanceOfModule = true := by native_decide

def snapshotAllowanceModelUsesAllowanceModule : Bool :=
  match MacroERC20.snapshotAllowance_modelBody with
  | [Stmt.ecm mod [Expr.param "token", Expr.param "owner", Expr.param "spender"],
      Stmt.setStorage "lastAllowance" (Expr.localVar "current"),
      Stmt.return (Expr.localVar "current")] =>
      mod.name == "allowance" &&
      mod.resultVars == ["current"] &&
      mod.axioms == ["erc20_allowance_interface"]
  | _ => false

example : snapshotAllowanceModelUsesAllowanceModule = true := by native_decide

def snapshotSupplyModelUsesTotalSupplyModule : Bool :=
  match MacroERC20.snapshotSupply_modelBody with
  | [Stmt.ecm mod [Expr.param "token"],
      Stmt.setStorage "lastSupply" (Expr.localVar "supply"),
      Stmt.return (Expr.localVar "supply")] =>
      mod.name == "totalSupply" &&
      mod.resultVars == ["supply"] &&
      mod.axioms == ["erc20_totalSupply_interface"]
  | _ => false

example : snapshotSupplyModelUsesTotalSupplyModule = true := by native_decide

def snapshotBalanceExecutableUsesStub : Bool :=
  let token := Verity.wordToAddress 7
  let owner := Verity.wordToAddress 13
  match Contracts.balanceOf token owner Verity.defaultState,
      MacroERC20.snapshotBalance token owner Verity.defaultState with
  | .success expected _, .success balance state =>
      balance == expected &&
      state.storage 0 == expected &&
      state.storage 1 == 0
  | .revert _ _, _ => false
  | _, .revert _ _ => false

example : snapshotBalanceExecutableUsesStub = true := by native_decide

def snapshotAllowanceExecutableUsesStub : Bool :=
  let token := Verity.wordToAddress 7
  let owner := Verity.wordToAddress 13
  let spender := Verity.wordToAddress 17
  match Contracts.allowance token owner spender Verity.defaultState,
      MacroERC20.snapshotAllowance token owner spender Verity.defaultState with
  | .success expected _, .success current state =>
      current == expected &&
      state.storage 1 == expected &&
      state.storage 0 == 0
  | .revert _ _, _ => false
  | _, .revert _ _ => false

example : snapshotAllowanceExecutableUsesStub = true := by native_decide

def snapshotSupplyExecutableUsesStub : Bool :=
  let token := Verity.wordToAddress 7
  match Contracts.totalSupply token Verity.defaultState,
      MacroERC20.snapshotSupply token Verity.defaultState with
  | .success expected _, .success supply state =>
      supply == expected &&
      state.storage 2 == expected
  | .revert _ _, _ => false
  | _, .revert _ _ => false

example : snapshotSupplyExecutableUsesStub = true := by native_decide

end MacroERC20Smoke

namespace MacroTransientStorageSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroTransientStorage where
  storage

  function warm (key : Uint256, value : Uint256)
    local_obligations [transient_storage_refinement := assumed "Caller must separately prove the direct transient-storage choreography refines the intended warm-slot behavior."]
    : Uint256 := do
    tstore key value
    let current := tload key
    return current

  function peek (key : Uint256)
    local_obligations [transient_storage_read_refinement := assumed "Caller must separately prove the direct transient-storage read refines the intended peek behavior."]
    : Uint256 := do
    let current := tload key
    return current

def warmModelUsesTransientStorage : Bool :=
  match MacroTransientStorage.warm_modelBody with
  | [Stmt.tstore (Expr.param "key") (Expr.param "value"),
      Stmt.letVar "current" (Expr.tload (Expr.param "key")),
      Stmt.return (Expr.localVar "current")] =>
      true
  | _ => false

example : warmModelUsesTransientStorage = true := by native_decide

def warmCarriesTransientStorageObligation : Bool :=
  match MacroTransientStorage.warm_model with
  | { localObligations := [{ name := "transient_storage_refinement"
                             obligation := "Caller must separately prove the direct transient-storage choreography refines the intended warm-slot behavior."
                             proofStatus := .assumed }]
      body := _, .. } => true
  | _ => false

example : warmCarriesTransientStorageObligation = true := by native_decide

def peekModelUsesTransientStorage : Bool :=
  match MacroTransientStorage.peek_modelBody with
  | [Stmt.letVar "current" (Expr.tload (Expr.param "key")),
      Stmt.return (Expr.localVar "current")] =>
      true
  | _ => false

example : peekModelUsesTransientStorage = true := by native_decide

def peekCarriesTransientStorageObligation : Bool :=
  match MacroTransientStorage.peek_model with
  | { localObligations := [{ name := "transient_storage_read_refinement"
                             obligation := "Caller must separately prove the direct transient-storage read refines the intended peek behavior."
                             proofStatus := .assumed }]
      body := _, .. } => true
  | _ => false

example : peekCarriesTransientStorageObligation = true := by native_decide

def warmExecutableWritesTransientStorage : Bool :=
  match MacroTransientStorage.warm 7 99 Verity.defaultState with
  | .success current state =>
      current == 99 &&
      state.transientStorage 7 == 99 &&
      state.storage 7 == 0
  | .revert _ _ => false

example : warmExecutableWritesTransientStorage = true := by native_decide

def transientStoragePersistsAcrossExecutableCalls : Bool :=
  match MacroTransientStorage.warm 7 99 Verity.defaultState with
  | .success _ warmedState =>
      match MacroTransientStorage.peek 7 warmedState with
      | .success current finalState =>
          current == 99 &&
          finalState.transientStorage 7 == 99
      | .revert _ _ => false
  | .revert _ _ => false

example : transientStoragePersistsAcrossExecutableCalls = true := by native_decide

end MacroTransientStorageSmoke

namespace MacroBlobbasefeeSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroBlobbasefee where
  storage

  function currentBlobBaseFee () : Uint256 := do
    return blobbasefee

def modelReturnsBlobbasefeeBuiltin : Bool :=
  match MacroBlobbasefee.currentBlobBaseFee_modelBody with
  | [Stmt.return Expr.blobbasefee] => true
  | _ => false

example : modelReturnsBlobbasefeeBuiltin = true := by native_decide

def executableUsesRuntimeStub : Bool :=
  match MacroBlobbasefee.currentBlobBaseFee Verity.defaultState with
  | .success fee state =>
      fee == 0 && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : executableUsesRuntimeStub = true := by native_decide

end MacroBlobbasefeeSmoke

namespace MacroConstantSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroConstant where
  storage
    storedFee : Uint256 := slot 0

  constants
    basisPoints : Uint256 := 10000
    mintFeeBps : Uint256 := 30
    treasury : Address := (wordToAddress 42)
    treasuryWord : Uint256 := (addressToWord treasury)

  function feeOn (amount : Uint256) : Uint256 := do
    let fee := div (mul amount mintFeeBps) basisPoints
    return fee

  function treasuryAddr () : Address := do
    return treasury

  function treasuryAsWord () : Uint256 := do
    return treasuryWord

  function shadowedConstant (mintFeeBps : Uint256) : Uint256 := do
    let treasuryWord := 9
    return (add mintFeeBps treasuryWord)

def feeOnModelInlinesContractConstants : Bool :=
  match MacroConstant.feeOn_modelBody with
  | [Stmt.letVar "fee"
        (Expr.div
          (Expr.mul (Expr.param "amount") (Expr.literal 30))
          (Expr.literal 10000)),
      Stmt.return (Expr.localVar "fee")] =>
      true
  | _ => false

example : feeOnModelInlinesContractConstants = true := by native_decide

def treasuryAddrModelInlinesAddressConstant : Bool :=
  match MacroConstant.treasuryAddr_modelBody with
  | [Stmt.return (Expr.literal 42)] =>
      true
  | _ => false

example : treasuryAddrModelInlinesAddressConstant = true := by native_decide

def treasuryAsWordModelInlinesNestedConstants : Bool :=
  match MacroConstant.treasuryAsWord_modelBody with
  | [Stmt.return (Expr.literal 42)] =>
      true
  | _ => false

example : treasuryAsWordModelInlinesNestedConstants = true := by native_decide

def shadowedConstantModelPrefersLocalAndParamBindings : Bool :=
  match MacroConstant.shadowedConstant_modelBody with
  | [Stmt.letVar "treasuryWord" (Expr.literal 9),
      Stmt.return (Expr.add (Expr.param "mintFeeBps") (Expr.localVar "treasuryWord"))] =>
      true
  | _ => false

example : shadowedConstantModelPrefersLocalAndParamBindings = true := by native_decide

def treasuryExecutableUsesGeneratedConstantDef : Bool :=
  match MacroConstant.treasuryAddr Verity.defaultState with
  | .success treasury state =>
      treasury == Verity.wordToAddress 42 &&
      state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : treasuryExecutableUsesGeneratedConstantDef = true := by native_decide

end MacroConstantSmoke

namespace MacroTupleDestructuringSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroTupleDestructuring where
  storage
    firstSlot : Uint256 := slot 0
    secondSlot : Uint256 := slot 1

  function helperPair (seed : Uint256) : Tuple [Uint256, Uint256] := do
    return (seed, add seed 1)

  function storePair (pair : Tuple [Uint256, Uint256]) : Unit := do
    let (first, second) := pair
    setStorage firstSlot first
    setStorage secondSlot second

  function storePairTail (pair : Tuple [Uint256, Uint256]) : Unit := do
    let (_, second) := pair
    setStorage secondSlot second

  function storeLiteralPair (seed : Uint256) : Unit := do
    let (first, second) := (seed, add seed 1)
    setStorage firstSlot first
    setStorage secondSlot second

  function echoPair (pair : Tuple [Uint256, Uint256]) : Tuple [Uint256, Uint256] := do
    let (first, second) := pair
    return (first, second)

  function storeHelperPair (seed : Uint256) : Unit := do
    let (first, second) ← helperPair seed
    setStorage firstSlot first
    setStorage secondSlot second

  function storeHelperPairEq (seed : Uint256) : Unit := do
    let (first, second) := helperPair seed
    setStorage firstSlot first
    setStorage secondSlot second

  function storeHelperPairTail (seed : Uint256) : Unit := do
    let (_, second) := helperPair seed
    setStorage secondSlot second

  function storeHelperPairTailNameCollision («__tuple_discard_0» : Uint256, seed : Uint256) : Unit := do
    let (_, second) := helperPair seed
    setStorage firstSlot «__tuple_discard_0»
    setStorage secondSlot second

def storePairModelDestructuresTupleParam : Bool :=
  match MacroTupleDestructuring.storePair_modelBody with
  | [Stmt.letVar "first" (Expr.param "pair_0"),
      Stmt.letVar "second" (Expr.param "pair_1"),
      Stmt.setStorage "firstSlot" (Expr.localVar "first"),
      Stmt.setStorage "secondSlot" (Expr.localVar "second"),
      Stmt.stop] =>
      true
  | _ => false

example : storePairModelDestructuresTupleParam = true := by native_decide

def storePairTailModelSkipsDiscardedBinder : Bool :=
  match MacroTupleDestructuring.storePairTail_modelBody with
  | [Stmt.letVar "second" (Expr.param "pair_1"),
      Stmt.setStorage "secondSlot" (Expr.localVar "second"),
      Stmt.stop] =>
      true
  | _ => false

example : storePairTailModelSkipsDiscardedBinder = true := by native_decide

def helperPairModelReturnsMultipleWords : Bool :=
  match MacroTupleDestructuring.helperPair_modelBody with
  | [Stmt.returnValues [Expr.param "seed", Expr.add (Expr.param "seed") (Expr.literal 1)]] =>
      true
  | _ => false

example : helperPairModelReturnsMultipleWords = true := by native_decide

def storeLiteralPairModelDestructuresTupleExpr : Bool :=
  match MacroTupleDestructuring.storeLiteralPair_modelBody with
  | [Stmt.letVar "first" (Expr.param "seed"),
      Stmt.letVar "second" (Expr.add (Expr.param "seed") (Expr.literal 1)),
      Stmt.setStorage "firstSlot" (Expr.localVar "first"),
      Stmt.setStorage "secondSlot" (Expr.localVar "second"),
      Stmt.stop] =>
      true
  | _ => false

example : storeLiteralPairModelDestructuresTupleExpr = true := by native_decide

def echoPairModelReturnsMultipleWords : Bool :=
  match MacroTupleDestructuring.echoPair_modelBody with
  | [Stmt.letVar "first" (Expr.param "pair_0"),
      Stmt.letVar "second" (Expr.param "pair_1"),
      Stmt.returnValues [Expr.localVar "first", Expr.localVar "second"]] =>
      true
  | _ => false

example : echoPairModelReturnsMultipleWords = true := by native_decide

def storeHelperPairModelUsesInternalCallAssign : Bool :=
  match MacroTupleDestructuring.storeHelperPair_modelBody with
  | [Stmt.internalCallAssign ["first", "second"] "helperPair" [Expr.param "seed"],
      Stmt.setStorage "firstSlot" (Expr.localVar "first"),
      Stmt.setStorage "secondSlot" (Expr.localVar "second"),
      Stmt.stop] =>
      true
  | _ => false

example : storeHelperPairModelUsesInternalCallAssign = true := by native_decide

def storeHelperPairEqModelUsesInternalCallAssign : Bool :=
  match MacroTupleDestructuring.storeHelperPairEq_modelBody with
  | [Stmt.internalCallAssign ["first", "second"] "helperPair" [Expr.param "seed"],
      Stmt.setStorage "firstSlot" (Expr.localVar "first"),
      Stmt.setStorage "secondSlot" (Expr.localVar "second"),
      Stmt.stop] =>
      true
  | _ => false

example : storeHelperPairEqModelUsesInternalCallAssign = true := by native_decide

def storeHelperPairTailModelUsesHiddenDiscardTarget : Bool :=
  match MacroTupleDestructuring.storeHelperPairTail_modelBody with
  | [Stmt.internalCallAssign ["__tuple_discard_0", "second"] "helperPair" [Expr.param "seed"],
      Stmt.setStorage "secondSlot" (Expr.localVar "second"),
      Stmt.stop] =>
      true
  | _ => false

example : storeHelperPairTailModelUsesHiddenDiscardTarget = true := by native_decide

def storeHelperPairTailNameCollisionModelUsesFreshDiscardTarget : Bool :=
  match MacroTupleDestructuring.storeHelperPairTailNameCollision_modelBody with
  | [Stmt.internalCallAssign ["__tuple_discard_0_1", "second"] "helperPair" [Expr.param "seed"],
      Stmt.setStorage "firstSlot" (Expr.param "__tuple_discard_0"),
      Stmt.setStorage "secondSlot" (Expr.localVar "second"),
      Stmt.stop] =>
      true
  | _ => false

example : storeHelperPairTailNameCollisionModelUsesFreshDiscardTarget = true := by native_decide

def echoPairExecutableKeepsTupleShape : Bool :=
  match MacroTupleDestructuring.echoPair (11, 17) Verity.defaultState with
  | .success (first, second) state =>
      first == 11 && second == 17 && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : echoPairExecutableKeepsTupleShape = true := by native_decide

def storeHelperPairExecutableStoresHelperResults : Bool :=
  match MacroTupleDestructuring.storeHelperPair 11 Verity.defaultState with
  | .success () state =>
      state.storage 0 == 11 && state.storage 1 == 12
  | .revert _ _ => false

example : storeHelperPairExecutableStoresHelperResults = true := by native_decide

def storeHelperPairEqExecutableStoresHelperResults : Bool :=
  match MacroTupleDestructuring.storeHelperPairEq 11 Verity.defaultState with
  | .success () state =>
      state.storage 0 == 11 && state.storage 1 == 12
  | .revert _ _ => false

example : storeHelperPairEqExecutableStoresHelperResults = true := by native_decide

def storePairTailExecutableStoresOnlyRequestedValue : Bool :=
  match MacroTupleDestructuring.storePairTail (11, 17) Verity.defaultState with
  | .success () state =>
      state.storage 0 == 0 && state.storage 1 == 17
  | .revert _ _ => false

example : storePairTailExecutableStoresOnlyRequestedValue = true := by native_decide

def storeHelperPairTailExecutableStoresOnlyRequestedValue : Bool :=
  match MacroTupleDestructuring.storeHelperPairTail 11 Verity.defaultState with
  | .success () state =>
      state.storage 0 == 0 && state.storage 1 == 12
  | .revert _ _ => false

example : storeHelperPairTailExecutableStoresOnlyRequestedValue = true := by native_decide

def storeHelperPairTailNameCollisionExecutablePreservesParam : Bool :=
  match MacroTupleDestructuring.storeHelperPairTailNameCollision 33 11 Verity.defaultState with
  | .success () state =>
      state.storage 0 == 33 && state.storage 1 == 12
  | .revert _ _ => false

example : storeHelperPairTailNameCollisionExecutablePreservesParam = true := by native_decide

end MacroTupleDestructuringSmoke

namespace MacroStatelessSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroStateless where
  storage

  function echoWord (value : Uint256) : Uint256 := do
    return value

  function callerEcho () : Address := do
    let sender ← msgSender
    return sender

def specHasNoFields : Bool :=
  MacroStateless.spec.fields.isEmpty

example : specHasNoFields = true := by native_decide

def echoWordModelUsesOnlyParams : Bool :=
  match MacroStateless.echoWord_modelBody with
  | [Stmt.return (Expr.param "value")] => true
  | _ => false

example : echoWordModelUsesOnlyParams = true := by native_decide

def callerEchoExecutableReadsSender : Bool :=
  let state := { Verity.defaultState with sender := Verity.wordToAddress 77 }
  match MacroStateless.callerEcho state with
  | .success sender nextState =>
      sender == Verity.wordToAddress 77 && nextState.sender == state.sender
  | .revert _ _ => false

example : callerEchoExecutableReadsSender = true := by native_decide

end MacroStatelessSmoke

namespace MacroStatelessSectionsSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroStatelessSections where
  storage

  errors
    error BadSeed(Uint256)

  constructor (seed : Uint256) := do
    let same := seed == seed
    require same "seed sanity check"

  function failWith (_seed : Uint256) : Unit := do
    let failingSeed := _seed
    revert BadSeed(failingSeed)

def specKeepsEmptyFieldsWithErrorsAndConstructor : Bool :=
  MacroStatelessSections.spec.fields.isEmpty &&
  MacroStatelessSections.spec.errors.map (·.name) == ["BadSeed"] &&
  match MacroStatelessSections.spec.constructor with
  | some ctor =>
      match ctor.params with
      | [{ name := "seed", ty := ParamType.uint256 }] => true
      | _ => false
  | none => false

example : specKeepsEmptyFieldsWithErrorsAndConstructor = true := by native_decide

def failWithModelUsesDeclaredCustomError : Bool :=
  match MacroStatelessSections.failWith_modelBody with
  | [Stmt.letVar "failingSeed" (Expr.param "_seed"),
      Stmt.revertError "BadSeed" [Expr.localVar "failingSeed"],
      Stmt.stop] => true
  | _ => false

example : failWithModelUsesDeclaredCustomError = true := by native_decide

end MacroStatelessSectionsSmoke

namespace MacroPayableConstructorSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroNonPayableConstructor where
  storage
    owner : Address := slot 0

  constructor (seedOwner : Address) := do
    setStorageAddr owner seedOwner

  function getOwner () : Address := do
    let currentOwner ← getStorageAddr owner
    return currentOwner

verity_contract MacroPayableConstructor where
  storage
    owner : Address := slot 0

  constructor (seedOwner : Address) payable := do
    setStorageAddr owner seedOwner

  function getOwner () : Address := do
    let currentOwner ← getStorageAddr owner
    return currentOwner

def specMarksConstructorPayable : Bool :=
  match MacroPayableConstructor.spec.constructor with
  | some ctor =>
      ctor.isPayable &&
      match ctor.params with
      | [{ name := "seedOwner", ty := ParamType.address }] => true
      | _ => false
  | none => false

example : specMarksConstructorPayable = true := by native_decide

end MacroPayableConstructorSmoke

namespace MacroInitializerSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroInitializer where
  storage
    initializedVersion : Uint256 := slot 0
    owner : Address := slot 1
    paused : Uint256 := slot 2

  function initOwner (seedOwner : Address) initializer(initializedVersion) : Unit := do
    setStorageAddr owner seedOwner

  function initOwnerChecked (seedOwner : Address) initializer(initializedVersion) : Unit := do
    require (seedOwner != zeroAddress) "Invalid owner"
    setStorageAddr owner seedOwner

  function upgradeToV2 () reinitializer(initializedVersion, 2) : Unit := do
    setStorage paused 1

  function ownerAddr () : Address := do
    let currentOwner ← getStorageAddr owner
    return currentOwner

def initializeModelPrependsSingleRunGuard : Bool :=
  match MacroInitializer.initOwner_modelBody with
  | [Stmt.require (Expr.eq (Expr.storage "initializedVersion") (Expr.literal 0)) "initializer already run",
      Stmt.setStorage "initializedVersion" (Expr.literal 1),
      Stmt.setStorageAddr "owner" (Expr.param "seedOwner"),
      Stmt.stop] =>
      true
  | _ => false

example : initializeModelPrependsSingleRunGuard = true := by native_decide

def initializeV2ModelPrependsVersionGuard : Bool :=
  match MacroInitializer.upgradeToV2_modelBody with
  | [Stmt.require (Expr.lt (Expr.storage "initializedVersion") (Expr.literal 2)) "reinitializer(2) already run",
      Stmt.setStorage "initializedVersion" (Expr.literal 2),
      Stmt.setStorage "paused" (Expr.literal 1),
      Stmt.stop] =>
      true
  | _ => false

example : initializeV2ModelPrependsVersionGuard = true := by native_decide

def initializeExecutableRunsOnce : Bool :=
  let seedOwner := wordToAddress 77
  match MacroInitializer.initOwner seedOwner Verity.defaultState with
  | .success () state =>
      state.storage MacroInitializer.initializedVersion.slot == 1 &&
      state.storageAddr MacroInitializer.owner.slot == seedOwner
  | .revert _ _ => false

example : initializeExecutableRunsOnce = true := by native_decide

def initializeExecutableSecondCallReverts : Bool :=
  let seedOwner := wordToAddress 77
  match MacroInitializer.initOwner seedOwner Verity.defaultState with
  | .success () initializedState =>
      match MacroInitializer.initOwner seedOwner initializedState with
      | .revert "initializer already run" revertedState =>
          revertedState.storage MacroInitializer.initializedVersion.slot ==
            initializedState.storage MacroInitializer.initializedVersion.slot &&
          revertedState.storageAddr MacroInitializer.owner.slot ==
            initializedState.storageAddr MacroInitializer.owner.slot
      | _ => false
  | .revert _ _ => false

example : initializeExecutableSecondCallReverts = true := by native_decide

def initializeExecutableBodyRevertRollsBackVersionSlot : Bool :=
  match (MacroInitializer.initOwnerChecked zeroAddress).run Verity.defaultState with
  | .revert "Invalid owner" revertedState =>
      revertedState.storage MacroInitializer.initializedVersion.slot == 0 &&
      revertedState.storageAddr MacroInitializer.owner.slot == zeroAddress
  | _ => false

example : initializeExecutableBodyRevertRollsBackVersionSlot = true := by native_decide

def reinitializerExecutableAdvancesVersion : Bool :=
  let seedOwner := wordToAddress 77
  match MacroInitializer.initOwner seedOwner Verity.defaultState with
  | .success () initializedState =>
      match MacroInitializer.upgradeToV2 initializedState with
      | .success () upgradedState =>
          upgradedState.storage MacroInitializer.initializedVersion.slot == 2 &&
          upgradedState.storage MacroInitializer.paused.slot == 1
      | .revert _ _ => false
  | .revert _ _ => false

example : reinitializerExecutableAdvancesVersion = true := by native_decide

end MacroInitializerSmoke

namespace MacroImmutableSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroImmutable where
  storage
    owner : Address := slot 0

  constants
    offset : Uint256 := 2

  immutables
    seededSupply : Uint256 := (add seed offset)
    treasury : Address := ownerSeed

  constructor (seed : Uint256, ownerSeed : Address) := do
    setStorageAddr owner ownerSeed

  function supplyCap () : Uint256 := do
    return seededSupply

  function treasuryAddr () : Address := do
    return treasury

  function shadowed (seededSupply : Uint256) : Uint256 := do
    return seededSupply

verity_contract MacroImplicitImmutable where
  storage

  immutables
    feeScale : Uint256 := 10000

  function getFeeScale () : Uint256 := do
    return feeScale

verity_contract MacroTypedImmutable where
  storage

  immutables
    paused : Bool := true
    feeBps : Uint8 := 7
    domainTag : Bytes32 := 42

  function isPaused () : Bool := do
    return paused

  function feeScale () : Uint8 := do
    return feeBps

  function domainSeparator () : Bytes32 := do
    return domainTag

def specIncludesInternalImmutableFields : Bool :=
  MacroImmutable.spec.fields.map (·.name) ==
    ["owner", "__immutable_seededSupply", "__immutable_treasury"]

example : specIncludesInternalImmutableFields = true := by native_decide

def constructorSeedsInternalImmutableSlots : Bool :=
  match MacroImmutable.spec.constructor with
  | some ctor =>
      match ctor.body with
      | [Stmt.setStorage "__immutable_seededSupply"
            (Expr.add (Expr.param "seed") (Expr.literal 2)),
          Stmt.setStorageAddr "__immutable_treasury" (Expr.param "ownerSeed"),
          Stmt.setStorageAddr "owner" (Expr.param "ownerSeed")] =>
          true
      | _ => false
  | none => false

example : constructorSeedsInternalImmutableSlots = true := by native_decide

def runtimeFunctionsLoadImmutableValuesFromState : Bool :=
  match MacroImmutable.supplyCap Verity.defaultState, MacroImmutable.treasuryAddr Verity.defaultState with
  | .success 0 _, .success treasury _ => treasury == zeroAddress
  | _, _ => false

example : runtimeFunctionsLoadImmutableValuesFromState = true := by native_decide

def functionParamsStillShadowImmutableNames : Bool :=
  match MacroImmutable.shadowed 91 Verity.defaultState with
  | .success value _ => value == 91
  | _ => false

example : functionParamsStillShadowImmutableNames = true := by native_decide

def implicitConstructorCreatedForImmutableInitializers : Bool :=
  match MacroImplicitImmutable.spec.constructor with
  | some ctor =>
      ctor.params.isEmpty &&
      match ctor.body with
      | [Stmt.setStorage "__immutable_feeScale" (Expr.literal 10000)] => true
      | _ => false
  | none => false

example : implicitConstructorCreatedForImmutableInitializers = true := by native_decide

def implicitImmutableExecutableReadsRuntimeSlot : Bool :=
  match MacroImplicitImmutable.getFeeScale Verity.defaultState with
  | .success value _ => value == 0
  | _ => false

example : implicitImmutableExecutableReadsRuntimeSlot = true := by native_decide

def typedImmutableSpecUsesWordBackedHiddenSlots : Bool :=
  match MacroTypedImmutable.spec.fields.map (fun f => (f.name, f.ty)) with
  | [("__immutable_paused", FieldType.uint256),
      ("__immutable_feeBps", FieldType.uint256),
      ("__immutable_domainTag", FieldType.uint256)] => true
  | _ => false

example : typedImmutableSpecUsesWordBackedHiddenSlots = true := by native_decide

def typedImmutableConstructorSeedsWordSlots : Bool :=
  match MacroTypedImmutable.spec.constructor with
  | some ctor =>
      ctor.params.isEmpty &&
      match ctor.body with
      | [Stmt.setStorage "__immutable_paused" (Expr.literal 1),
          Stmt.setStorage "__immutable_feeBps" (Expr.literal 7),
          Stmt.setStorage "__immutable_domainTag" (Expr.literal 42)] => true
      | _ => false
  | none => false

example : typedImmutableConstructorSeedsWordSlots = true := by native_decide

def typedImmutableExecutableReadsConvertedValues : Bool :=
  match MacroTypedImmutable.isPaused Verity.defaultState,
      MacroTypedImmutable.feeScale Verity.defaultState,
      MacroTypedImmutable.domainSeparator Verity.defaultState with
  | .success paused _, .success feeBps _, .success domainTag _ =>
      paused = false && feeBps == 0 && domainTag == 0
  | _, _, _ => false

example : typedImmutableExecutableReadsConvertedValues = true := by native_decide

end MacroImmutableSmoke

namespace MacroStructDestructuringSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroStructDestructuring where
  storage
    positions : MappingStruct(Address,[
      supplyShares @word 0 packed(0,128),
      borrowShares @word 0 packed(128,128),
      delegate @word 1
    ]) := slot 0
    approvals : MappingStruct2(Address,Address,[
      allowance @word 0 packed(0,128),
      nonce @word 1
    ]) := slot 1

  function loadPosition (user : Address) : Tuple [Uint256, Uint256, Address] := do
    let (supply, borrow, delegate_) := structMembers "positions" user ["supplyShares", "borrowShares", "delegate"]
    return (supply, borrow, delegate_)

  function loadApproval (owner : Address, spender : Address) : Tuple [Uint256, Uint256] := do
    return structMembers2 "approvals" owner spender ["allowance", "nonce"]

def loadPositionModelDestructuresStructMembers : Bool :=
  match MacroStructDestructuring.loadPosition_modelBody with
  | [Stmt.letVar "supply" (Expr.structMember "positions" (Expr.param "user") "supplyShares"),
      Stmt.letVar "borrow" (Expr.structMember "positions" (Expr.param "user") "borrowShares"),
      Stmt.letVar "delegate_" (Expr.structMember "positions" (Expr.param "user") "delegate"),
      Stmt.returnValues [Expr.localVar "supply", Expr.localVar "borrow", Expr.localVar "delegate_"]] =>
      true
  | _ => false

example : loadPositionModelDestructuresStructMembers = true := by native_decide

def loadApprovalModelReturnsStructMembers2 : Bool :=
  match MacroStructDestructuring.loadApproval_modelBody with
  | [Stmt.returnValues
      [Expr.structMember2 "approvals" (Expr.param "owner") (Expr.param "spender") "allowance",
       Expr.structMember2 "approvals" (Expr.param "owner") (Expr.param "spender") "nonce"]] =>
      true
  | _ => false

example : loadApprovalModelReturnsStructMembers2 = true := by native_decide

def loadPositionExecutableKeepsTupleShape : Bool :=
  match MacroStructDestructuring.loadPosition Verity.defaultState.sender Verity.defaultState with
  | .success (supply, (borrow, delegate_)) state =>
      supply == 0 && borrow == 0 && delegate_ == zeroAddress && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : loadPositionExecutableKeepsTupleShape = true := by native_decide

def loadApprovalExecutableKeepsTupleShape : Bool :=
  match MacroStructDestructuring.loadApproval Verity.defaultState.sender Verity.defaultState.sender Verity.defaultState with
  | .success (allowance, nonce) state =>
      allowance == 0 && nonce == 0 && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : loadApprovalExecutableKeepsTupleShape = true := by native_decide

end MacroStructDestructuringSmoke

namespace MacroDynamicArraySmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroDynamicArray where
  storage
    sentinel : Uint256 := slot 0

  function countRecipients (recipients : Array Address) : Uint256 := do
    let count := arrayLength recipients
    return count

  function firstRecipient (recipients : Array Address) : Address := do
    let first := arrayElement recipients 0
    return first

  function echoAmounts (amounts : Array Uint256) : Array Uint256 := do
    returnArray amounts

  function echoRecipients (recipients : Array Address) : Array Address := do
    returnArray recipients

  function echoFlags (flags : Array Bool) : Array Bool := do
    returnArray flags

def countRecipientsModelUsesArrayLength : Bool :=
  match MacroDynamicArray.countRecipients_modelBody with
  | [Stmt.letVar "count" (Expr.arrayLength "recipients"),
      Stmt.return (Expr.localVar "count")] =>
      true
  | _ => false

example : countRecipientsModelUsesArrayLength = true := by native_decide

def firstRecipientModelUsesArrayElement : Bool :=
  match MacroDynamicArray.firstRecipient_modelBody with
  | [Stmt.letVar "first" (Expr.arrayElement "recipients" (Expr.literal 0)),
      Stmt.return (Expr.localVar "first")] =>
      true
  | _ => false

example : firstRecipientModelUsesArrayElement = true := by native_decide

def echoAmountsModelUsesReturnArray : Bool :=
  match MacroDynamicArray.echoAmounts_modelBody with
  | [Stmt.returnArray "amounts"] =>
      true
  | _ => false

example : echoAmountsModelUsesReturnArray = true := by native_decide

def echoRecipientsModelUsesReturnArray : Bool :=
  match MacroDynamicArray.echoRecipients_modelBody with
  | [Stmt.returnArray "recipients"] =>
      true
  | _ => false

example : echoRecipientsModelUsesReturnArray = true := by native_decide

def echoFlagsModelUsesReturnArray : Bool :=
  match MacroDynamicArray.echoFlags_modelBody with
  | [Stmt.returnArray "flags"] =>
      true
  | _ => false

example : echoFlagsModelUsesReturnArray = true := by native_decide

def countRecipientsExecutableUsesRuntimeHelper : Bool :=
  match MacroDynamicArray.countRecipients #[(11 : Address), (17 : Address)] Verity.defaultState with
  | .success count state =>
      count == 2 && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : countRecipientsExecutableUsesRuntimeHelper = true := by native_decide

def firstRecipientExecutableUsesRuntimeHelper : Bool :=
  match MacroDynamicArray.firstRecipient #[(11 : Address), (17 : Address)] Verity.defaultState with
  | .success first state =>
      first == (11 : Address) && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : firstRecipientExecutableUsesRuntimeHelper = true := by native_decide

def firstRecipientExecutableRevertsOutOfRange : Bool :=
  match MacroDynamicArray.firstRecipient #[] Verity.defaultState with
  | .success _ _ => false
  | .revert msg state =>
      msg == "Array index out of bounds" && state.sender == Verity.defaultState.sender

example : firstRecipientExecutableRevertsOutOfRange = true := by native_decide

def echoAmountsExecutableRoundTrips : Bool :=
  match MacroDynamicArray.echoAmounts #[3, 5, 8] Verity.defaultState with
  | .success amounts state =>
      amounts == #[3, 5, 8] && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : echoAmountsExecutableRoundTrips = true := by native_decide

def echoRecipientsExecutableRoundTrips : Bool :=
  match MacroDynamicArray.echoRecipients #[(11 : Address), (17 : Address)] Verity.defaultState with
  | .success recipients state =>
      recipients == #[(11 : Address), (17 : Address)] &&
        state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : echoRecipientsExecutableRoundTrips = true := by native_decide

verity_contract MacroStorageDynamicArray where
  storage
    queue : Array Uint256 := slot 7

  function size () : Uint256 := do
    let size ← getStorageArrayLength queue
    return size

  function firstValue () : Uint256 := do
    let first ← getStorageArrayElement queue 0
    return first

  function pushValue (value : Uint256) : Unit := do
    pushStorageArray queue value

  function setValue0 (value : Uint256) : Unit := do
    setStorageArrayElement queue 0 value

  function popValue () : Unit := do
    popStorageArray queue

def storageDynamicArrayLengthUsesStorageExpr : Bool :=
  match MacroStorageDynamicArray.size_modelBody with
  | [Stmt.letVar "size" (Expr.storageArrayLength "queue"),
      Stmt.return (Expr.localVar "size")] =>
      true
  | _ => false

example : storageDynamicArrayLengthUsesStorageExpr = true := by native_decide

def storageDynamicArrayElementUsesStorageExpr : Bool :=
  match MacroStorageDynamicArray.firstValue_modelBody with
  | [Stmt.letVar "first" (Expr.storageArrayElement "queue" (Expr.literal 0)),
      Stmt.return (Expr.localVar "first")] =>
      true
  | _ => false

example : storageDynamicArrayElementUsesStorageExpr = true := by native_decide

def storageDynamicArrayPushUsesStorageStmt : Bool :=
  match MacroStorageDynamicArray.pushValue_modelBody with
  | [Stmt.storageArrayPush "queue" (Expr.param "value"), Stmt.stop] =>
      true
  | _ => false

example : storageDynamicArrayPushUsesStorageStmt = true := by native_decide

def storageDynamicArraySetUsesStorageStmt : Bool :=
  match MacroStorageDynamicArray.setValue0_modelBody with
  | [Stmt.setStorageArrayElement "queue" (Expr.literal 0) (Expr.param "value"), Stmt.stop] =>
      true
  | _ => false

example : storageDynamicArraySetUsesStorageStmt = true := by native_decide

def storageDynamicArrayPopUsesStorageStmt : Bool :=
  match MacroStorageDynamicArray.popValue_modelBody with
  | [Stmt.storageArrayPop "queue", Stmt.stop] =>
      true
  | _ => false

example : storageDynamicArrayPopUsesStorageStmt = true := by native_decide

def storageDynamicArrayExecutableReadsHead : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == (MacroStorageDynamicArray.queue).slot then [11, 17] else [] }
  match MacroStorageDynamicArray.firstValue seededState with
  | .success value state =>
      value == 11 && state.storageArray (MacroStorageDynamicArray.queue).slot == [11, 17]
  | .revert _ _ => false

example : storageDynamicArrayExecutableReadsHead = true := by native_decide

def storageDynamicArrayExecutableReadRevertsOutOfBounds : Bool :=
  match MacroStorageDynamicArray.firstValue Verity.defaultState with
  | .success _ _ => false
  | .revert msg state =>
      msg == "Storage array index out of bounds" &&
        state.storageArray (MacroStorageDynamicArray.queue).slot == []

example : storageDynamicArrayExecutableReadRevertsOutOfBounds = true := by native_decide

def storageDynamicArrayExecutableSetUpdatesHead : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == (MacroStorageDynamicArray.queue).slot then [11, 17] else [] }
  match MacroStorageDynamicArray.setValue0 29 seededState with
  | .success () state =>
      state.storageArray (MacroStorageDynamicArray.queue).slot == [29, 17]
  | .revert _ _ => false

example : storageDynamicArrayExecutableSetUpdatesHead = true := by native_decide

def storageDynamicArrayExecutableSetRevertsOutOfBounds : Bool :=
  match MacroStorageDynamicArray.setValue0 29 Verity.defaultState with
  | .success _ _ => false
  | .revert msg state =>
      msg == "Storage array index out of bounds" &&
        state.storageArray (MacroStorageDynamicArray.queue).slot == []

example : storageDynamicArrayExecutableSetRevertsOutOfBounds = true := by native_decide

def storageDynamicArrayExecutablePopShrinksLength : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == (MacroStorageDynamicArray.queue).slot then [11, 17] else [] }
  match MacroStorageDynamicArray.popValue seededState with
  | .success () state =>
      state.storageArray (MacroStorageDynamicArray.queue).slot == [11]
  | .revert _ _ => false

example : storageDynamicArrayExecutablePopShrinksLength = true := by native_decide

def storageDynamicArrayExecutablePopRevertsWhenEmpty : Bool :=
  match MacroStorageDynamicArray.popValue Verity.defaultState with
  | .success _ _ => false
  | .revert msg state =>
      msg == "Storage array pop on empty array" &&
        state.storageArray (MacroStorageDynamicArray.queue).slot == []

example : storageDynamicArrayExecutablePopRevertsWhenEmpty = true := by native_decide

end MacroDynamicArraySmoke

namespace MacroEventTraceSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroEventTrace where
  storage

  function emitNamed (amount : Uint256, bonus : Uint256) : Unit := do
    emit "Transfer" [amount, add amount bonus]

  function emitDynamicLog
      (topic0 : Uint256, topic1 : Uint256, dataOffset : Uint256, dataSize : Uint256) : Unit := do
    rawLog [topic0, add topic1 1] dataOffset dataSize

def emitNamedModelUsesStmtEmit : Bool :=
  match MacroEventTrace.emitNamed_modelBody with
  | [Stmt.emit "Transfer" [Expr.param "amount", Expr.add (Expr.param "amount") (Expr.param "bonus")],
      Stmt.stop] =>
      true
  | _ => false

example : emitNamedModelUsesStmtEmit = true := by native_decide

def emitDynamicLogModelUsesStmtRawLog : Bool :=
  match MacroEventTrace.emitDynamicLog_modelBody with
  | [Stmt.rawLog
        [Expr.param "topic0", Expr.add (Expr.param "topic1") (Expr.literal 1)]
        (Expr.param "dataOffset")
        (Expr.param "dataSize"),
      Stmt.stop] =>
      true
  | _ => false

example : emitDynamicLogModelUsesStmtRawLog = true := by native_decide

def emitNamedExecutableAppendsNamedEvent : Bool :=
  match MacroEventTrace.emitNamed 7 5 Verity.defaultState with
  | .success () state =>
      match state.events with
      | [{ name := "Transfer", args := [7, 12], indexedArgs := [] }] =>
          state.sender == Verity.defaultState.sender
      | _ => false
  | .revert _ _ => false

example : emitNamedExecutableAppendsNamedEvent = true := by native_decide

def emitDynamicLogExecutableAppendsLowLevelTrace : Bool :=
  match MacroEventTrace.emitDynamicLog 3 4 64 96 Verity.defaultState with
  | .success () state =>
      match state.events with
      | [{ name := "log2", args := [64, 96], indexedArgs := [3, 5] }] =>
          state.sender == Verity.defaultState.sender
      | _ => false
  | .revert _ _ => false

example : emitDynamicLogExecutableAppendsLowLevelTrace = true := by native_decide

def rawLogExecutableRejectsTooManyTopics : Bool :=
  match rawLog [1, 2, 3, 4, 5] 0 32 Verity.defaultState with
  | .revert msg state =>
      msg == "rawLog supports at most 4 topics, got 5" &&
        match state.events with
        | [] => true
        | _ => false
  | .success _ _ => false

example : rawLogExecutableRejectsTooManyTopics = true := by native_decide

end MacroEventTraceSmoke

private def expectTrue (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"✗ {label}")
  IO.println s!"✓ {label}"

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

private def selectorCount (spec : CompilationModel) : Nat :=
  (spec.functions.filter (fun fn => !fn.isInternal && fn.name != "fallback" && fn.name != "receive")).length

private def selectorsFor (spec : CompilationModel) : List Nat :=
  List.range (selectorCount spec)

private def expectCompileErrorContains (label : String)
    (spec : CompilationModel) (needle : String) : IO Unit := do
  match Compiler.CompilationModel.compile spec (selectorsFor spec) with
  | .ok _ =>
      throw (IO.userError s!"✗ {label}: expected compile failure")
  | .error msg =>
      expectTrue label (contains msg needle)

private def compileToYul (spec : CompilationModel) : Except String String := do
  let contract ← Compiler.CompilationModel.compile spec (selectorsFor spec)
  pure <| Compiler.Yul.render (Compiler.emitYul contract)

private def expectCompile (label : String) (spec : CompilationModel) : IO Compiler.IRContract := do
  match Compiler.CompilationModel.compile spec (selectorsFor spec) with
  | .ok contract => pure contract
  | .error err => throw (IO.userError s!"✗ {label} compile failed:\n{err}")

private def expectCompileToYul (label : String) (spec : CompilationModel) : IO String := do
  match compileToYul spec with
  | .ok yul => pure yul
  | .error err => throw (IO.userError s!"✗ {label} compile failed:\n{err}")

private def selectorSmokeSpec : CompilationModel := {
  name := "SelectorSmoke"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.setStorage "value" (Expr.param "next"),
        Stmt.stop
      ]
    },
    { name := "load"
      params := []
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.storage "value")]
    }
  ]
}

private def envRuntimeSmokeSpec : CompilationModel := {
  name := "EnvRuntimeSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "selfValueTimestampNumberAndChainId"
      params := []
      returnType := none
      returns := [ParamType.address, ParamType.uint256, ParamType.uint256, ParamType.uint256, ParamType.uint256, ParamType.uint256]
      body := [
        Stmt.returnValues [Expr.contractAddress, Expr.msgValue, Expr.blockTimestamp, Expr.blockNumber, Expr.chainid, Expr.blobbasefee]
      ]
    }
  ]
}

private def reservedParamSpec : CompilationModel := {
  name := "ReservedParam"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "__has_selector", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.setStorage "value" (Expr.param "__has_selector"),
        Stmt.stop
      ]
    }
  ]
}

private def reservedFieldSpec : CompilationModel := {
  name := "ReservedField"
  fields := [{ name := "__compat_value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.setStorage "__compat_value" (Expr.param "next"),
        Stmt.stop
      ]
    }
  ]
}

private def reservedLocalBinderSpec : CompilationModel := {
  name := "ReservedLocalBinder"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.letVar "__has_selector" (Expr.param "next"),
        Stmt.setStorage "value" (Expr.localVar "__has_selector"),
        Stmt.stop
      ]
    }
  ]
}

private def reservedAssignTargetSpec : CompilationModel := {
  name := "ReservedAssignTarget"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.assignVar "__compat_value" (Expr.param "next"),
        Stmt.stop
      ]
    }
  ]
}

private def reservedConstructorParamSpec : CompilationModel := {
  name := "ReservedConstructorParam"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := some {
    params := [{ name := "__init", ty := ParamType.uint256 }]
    body := [
      Stmt.setStorage "value" (Expr.constructorArg 0),
      Stmt.stop
    ]
  }
  functions := [
    { name := "load"
      params := []
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.storage "value")]
    }
  ]
}

private def reservedForEachBinderSpec : CompilationModel := {
  name := "ReservedForEachBinder"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := []
      returnType := none
      body := [
        Stmt.forEach "__loop_idx" (Expr.literal 1) [
          Stmt.setStorage "value" (Expr.literal 1)
        ],
        Stmt.stop
      ]
    }
  ]
}

private def assigningForEachBinderSpec : CompilationModel := {
  name := "AssigningForEachBinder"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := []
      returnType := none
      body := [
        Stmt.forEach "i" (Expr.literal 1) [
          Stmt.assignVar "i" (Expr.literal 7)
        ],
        Stmt.stop
      ]
    }
  ]
}

private def shadowingForEachBinderSpec : CompilationModel := {
  name := "ShadowingForEachBinder"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := []
      returnType := none
      body := [
        Stmt.letVar "i" (Expr.literal 10),
        Stmt.forEach "i" (Expr.literal 1) [
          Stmt.setStorage "value" (Expr.localVar "i")
        ],
        Stmt.stop
      ]
    }
  ]
}

private def paramShadowingForEachBinderSpec : CompilationModel := {
  name := "ParamShadowingForEachBinder"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "i", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.forEach "i" (Expr.literal 1) [
          Stmt.setStorage "value" (Expr.localVar "i")
        ],
        Stmt.stop
      ]
    }
  ]
}

private def internalAssignForEachBinderSpec : CompilationModel := {
  name := "InternalAssignForEachBinder"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "helper"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.param "next")]
      isInternal := true
    },
    { name := "store"
      params := []
      returnType := none
      body := [
        Stmt.forEach "i" (Expr.literal 1) [
          Stmt.internalCallAssign ["i"] "helper" [Expr.literal 7]
        ],
        Stmt.stop
      ]
    }
  ]
}

private def externalBindForEachBinderSpec : CompilationModel := {
  name := "ExternalBindForEachBinder"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.forEach "i" (Expr.literal 1) [
          Stmt.externalCallBind ["i"] "echo" [Expr.param "next"]
        ],
        Stmt.stop
      ]
    }
  ]
  externals := [
    { name := "echo"
      params := [ParamType.uint256]
      returnType := some ParamType.uint256
      returns := [ParamType.uint256]
      axiomNames := ["echo_matches_identity"]
    }
  ]
}

private def cachedForEachCountSpec : CompilationModel := {
  name := "CachedForEachCount"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "count", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.forEach "i" (Expr.param "count") [
          Stmt.setStorage "value" (Expr.localVar "i")
        ],
        Stmt.stop
      ]
    }
  ]
}

private def reservedInternalAssignBinderSpec : CompilationModel := {
  name := "ReservedInternalAssignBinder"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "helper"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.param "next")]
      isInternal := true
    },
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.internalCallAssign ["__ret"] "helper" [Expr.param "next"],
        Stmt.setStorage "value" (Expr.localVar "__ret"),
        Stmt.stop
      ]
    }
  ]
}

private def reservedExternalBindSpec : CompilationModel := {
  name := "ReservedExternalBind"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.externalCallBind ["__external_ret"] "echo" [Expr.param "next"],
        Stmt.setStorage "value" (Expr.localVar "__external_ret"),
        Stmt.stop
      ]
    }
  ]
  externals := [
    { name := "echo"
      params := [ParamType.uint256]
      returnType := some ParamType.uint256
      returns := [ParamType.uint256]
      axiomNames := ["echo_matches_identity"]
    }
  ]
}

private def effectOnlyExternalBindSpec : CompilationModel := {
  name := "EffectOnlyExternalBind"
  fields := []
  «constructor» := none
  functions := [
    { name := "poke"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.externalCallBind [] "notify" [Expr.param "next"],
        Stmt.stop
      ]
    }
  ]
  externals := [
    { name := "notify"
      params := [ParamType.uint256]
      returnType := none
      returns := []
      axiomNames := ["notify_effect_only"]
    }
  ]
}

private def effectOnlyExternalBindMismatchSpec : CompilationModel := {
  name := "EffectOnlyExternalBindMismatch"
  fields := []
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.externalCallBind [] "echo" [Expr.param "next"],
        Stmt.stop
      ]
    }
  ]
  externals := [
    { name := "echo"
      params := [ParamType.uint256]
      returnType := some ParamType.uint256
      returns := [ParamType.uint256]
      axiomNames := ["echo_matches_identity"]
    }
  ]
}

private def rawLogTraceSmokeSpec : CompilationModel := {
  name := "RawLogTraceSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "emitDynamicLog"
      params := [
        { name := "topic0", ty := ParamType.uint256 },
        { name := "topic1", ty := ParamType.uint256 },
        { name := "dataOffset", ty := ParamType.uint256 },
        { name := "dataSize", ty := ParamType.uint256 }
      ]
      returnType := none
      body := MacroEventTraceSmoke.MacroEventTrace.emitDynamicLog_modelBody
    }
  ]
}

private def reservedEcmResultVarSpec : CompilationModel := {
  name := "ReservedEcmResultVar"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := []
      returnType := none
      body := [
        Stmt.ecm
          { name := "reservedResult"
            numArgs := 0
            resultVars := ["__ecm_result"]
            writesState := false
            readsState := false
            compile := fun _ _ => pure []
          }
          [],
        Stmt.setStorage "value" (Expr.localVar "__ecm_result"),
        Stmt.stop
      ]
    }
  ]
}

private def stringAbiSpec : CompilationModel := {
  name := "StringABI"
  fields := []
  «constructor» := none
  functions := [
    { name := "echo"
      params := [{ name := "message", ty := ParamType.string }]
      returnType := none
      returns := [ParamType.string]
      body := [Stmt.returnBytes "message"]
    }
    , { name := "echoAfterUint"
        params := [{ name := "tag", ty := ParamType.uint256 }, { name := "message", ty := ParamType.string }]
        returnType := none
        returns := [ParamType.string]
        body := [Stmt.returnBytes "message"]
      }
    , { name := "echoBeforeUint"
        params := [{ name := "message", ty := ParamType.string }, { name := "tag", ty := ParamType.uint256 }]
        returnType := none
        returns := [ParamType.string]
        body := [Stmt.returnBytes "message"]
      }
    , { name := "echoSecondString"
        params := [{ name := "prefix", ty := ParamType.string }, { name := "message", ty := ParamType.string }]
        returnType := none
        returns := [ParamType.string]
        body := [Stmt.returnBytes "message"]
      }
  ]
  events := [
    { name := "MessageLogged"
      params := [{ name := "message", ty := ParamType.string, kind := EventParamKind.unindexed }]
    }
    , { name := "TaggedMessageLogged"
        params := [
          { name := "tag", ty := ParamType.uint256, kind := EventParamKind.indexed }
        , { name := "message", ty := ParamType.string, kind := EventParamKind.unindexed }
        ]
      }
    , { name := "IndexedMessageLogged"
        params := [{ name := "message", ty := ParamType.string, kind := EventParamKind.indexed }]
      }
    , { name := "SecondMessageLogged"
        params := [
          { name := "prefix", ty := ParamType.string, kind := EventParamKind.unindexed }
        , { name := "message", ty := ParamType.string, kind := EventParamKind.unindexed }
        ]
      }
  ]
  «errors» := [
    { name := "BadMessage"
      params := [ParamType.string]
    }
    , { name := "TaggedMessage"
        params := [ParamType.uint256, ParamType.string]
      }
    , { name := "SecondMessage"
        params := [ParamType.string, ParamType.string]
      }
  ]
}

private def stringReturnMismatchSpec : CompilationModel := {
  name := "StringReturnMismatch"
  fields := []
  «constructor» := none
  functions := [
    { name := "echo"
      params := [{ name := "message", ty := ParamType.bytes }]
      returnType := none
      returns := [ParamType.string]
      body := [Stmt.returnBytes "message"]
    }
  ]
}

private def stringEventMismatchSpec : CompilationModel := {
  name := "StringEventMismatch"
  fields := []
  «constructor» := none
  functions := [
    { name := "log"
      params := [{ name := "message", ty := ParamType.bytes }]
      returnType := none
      body := [Stmt.emit "MessageLogged" [Expr.param "message"], Stmt.stop]
    }
  ]
  events := [
    { name := "MessageLogged"
      params := [{ name := "message", ty := ParamType.string, kind := EventParamKind.unindexed }]
    }
  ]
}

private def addressArrayReturnSpec : CompilationModel := {
  name := "AddressArrayReturn"
  fields := []
  «constructor» := none
  functions := [
    { name := "echo"
      params := [{ name := "recipients", ty := ParamType.array ParamType.address }]
      returnType := none
      returns := [ParamType.array ParamType.address]
      body := [Stmt.returnArray "recipients"]
    }
  ]
}

private def bytesArrayReturnSpec : CompilationModel := {
  name := "BytesArrayReturn"
  fields := []
  «constructor» := none
  functions := [
    { name := "echo"
      params := [{ name := "calls", ty := ParamType.array ParamType.bytes }]
      returnType := none
      returns := [ParamType.array ParamType.bytes]
      body := [Stmt.returnArray "calls"]
    }
  ]
}

private def bytesArrayElementSpec : CompilationModel := {
  name := "BytesArrayElement"
  fields := []
  «constructor» := none
  functions := [
    { name := "headWord"
      params := [{ name := "calls", ty := ParamType.array ParamType.bytes }]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.arrayElement "calls" (Expr.literal 0))]
    }
  ]
}

private def storageArrayUint256SmokeSpec : CompilationModel := {
  name := "StorageArrayUint256Smoke"
  fields := [{ name := "queue", ty := FieldType.dynamicArray .uint256, «slot» := some 7 }]
  «constructor» := none
  functions := [
    { name := "size"
      params := []
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.storageArrayLength "queue")]
    },
    { name := "head"
      params := []
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.storageArrayElement "queue" (Expr.literal 0))]
    },
    { name := "enqueue"
      params := [{ name := "value", ty := ParamType.uint256 }]
      returnType := none
      body := [Stmt.storageArrayPush "queue" (Expr.param "value"), Stmt.stop]
    },
    { name := "setHead"
      params := [{ name := "value", ty := ParamType.uint256 }]
      returnType := none
      body := [Stmt.setStorageArrayElement "queue" (Expr.literal 0) (Expr.param "value"), Stmt.stop]
    },
    { name := "dequeue"
      params := []
      returnType := none
      body := [Stmt.storageArrayPop "queue", Stmt.stop]
    }
  ]
}

private def storageArrayBoolRejectSpec : CompilationModel := {
  name := "StorageArrayBoolReject"
  fields := [{ name := "flags", ty := FieldType.dynamicArray .bool, «slot» := some 9 }]
  «constructor» := none
  functions := [
    { name := "pushFlag"
      params := [{ name := "flag", ty := ParamType.bool }]
      returnType := none
      body := [Stmt.storageArrayPush "flags" (Expr.param "flag"), Stmt.stop]
    }
  ]
}

private def ecrecoverSmokeSpec : CompilationModel := {
  name := "EcrecoverSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "recover"
      params := [
        { name := "hash", ty := ParamType.bytes32 }
        , { name := "v", ty := ParamType.uint256 }
        , { name := "r", ty := ParamType.bytes32 }
        , { name := "s", ty := ParamType.bytes32 }
      ]
      returnType := none
      returns := [ParamType.address]
      body := [
        Compiler.Modules.Precompiles.ecrecover
          "signer"
          (Expr.param "hash")
          (Expr.param "v")
          (Expr.param "r")
          (Expr.param "s"),
        Stmt.returnValues [Expr.localVar "signer"]
      ]
    }
  ]
}

private def oracleReadSmokeSpec : CompilationModel := {
  name := "OracleReadSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "peek"
      params := [
        { name := "oracle", ty := ParamType.address }
        , { name := "asset", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.Oracle.oracleReadUint256
          "answer"
          (Expr.param "oracle")
          0xfeaf968c
          [Expr.param "asset"],
        Stmt.returnValues [Expr.localVar "answer"]
      ]
    }
  ]
}

private def erc20BalanceOfSmokeSpec : CompilationModel := {
  name := "ERC20BalanceOfSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "balance"
      params := [
        { name := "token", ty := ParamType.address }
        , { name := "owner", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC20.balanceOf
          "balance"
          (Expr.param "token")
          (Expr.param "owner"),
        Stmt.returnValues [Expr.localVar "balance"]
      ]
    }
  ]
}

private def erc20AllowanceSmokeSpec : CompilationModel := {
  name := "ERC20AllowanceSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "allowance"
      params := [
        { name := "token", ty := ParamType.address }
        , { name := "owner", ty := ParamType.address }
        , { name := "spender", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC20.allowance
          "remaining"
          (Expr.param "token")
          (Expr.param "owner")
          (Expr.param "spender"),
        Stmt.returnValues [Expr.localVar "remaining"]
      ]
    }
  ]
}

private def erc20TotalSupplySmokeSpec : CompilationModel := {
  name := "ERC20TotalSupplySmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "totalSupply"
      params := [{ name := "token", ty := ParamType.address }]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC20.totalSupply
          "supply"
          (Expr.param "token"),
        Stmt.returnValues [Expr.localVar "supply"]
      ]
    }
  ]
}

private def erc4626PreviewDepositSmokeSpec : CompilationModel := {
  name := "ERC4626PreviewDepositSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "preview"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "assets", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.previewDeposit
          "shares"
          (Expr.param "vault")
          (Expr.param "assets"),
        Stmt.returnValues [Expr.localVar "shares"]
      ]
    }
  ]
}

private def erc4626PreviewMintSmokeSpec : CompilationModel := {
  name := "ERC4626PreviewMintSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "preview"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "shares", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.previewMint
          "assets"
          (Expr.param "vault")
          (Expr.param "shares"),
        Stmt.returnValues [Expr.localVar "assets"]
      ]
    }
  ]
}

private def erc4626PreviewWithdrawSmokeSpec : CompilationModel := {
  name := "ERC4626PreviewWithdrawSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "preview"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "assets", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.previewWithdraw
          "shares"
          (Expr.param "vault")
          (Expr.param "assets"),
        Stmt.returnValues [Expr.localVar "shares"]
      ]
    }
  ]
}

private def erc4626PreviewRedeemSmokeSpec : CompilationModel := {
  name := "ERC4626PreviewRedeemSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "preview"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "shares", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.previewRedeem
          "assets"
          (Expr.param "vault")
          (Expr.param "shares"),
        Stmt.returnValues [Expr.localVar "assets"]
      ]
    }
  ]
}

private def erc4626ConvertToAssetsSmokeSpec : CompilationModel := {
  name := "ERC4626ConvertToAssetsSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "convert"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "shares", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.convertToAssets
          "assets"
          (Expr.param "vault")
          (Expr.param "shares"),
        Stmt.returnValues [Expr.localVar "assets"]
      ]
    }
  ]
}

private def erc4626ConvertToSharesSmokeSpec : CompilationModel := {
  name := "ERC4626ConvertToSharesSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "convert"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "assets", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.convertToShares
          "shares"
          (Expr.param "vault")
          (Expr.param "assets"),
        Stmt.returnValues [Expr.localVar "shares"]
      ]
    }
  ]
}

private def erc4626TotalAssetsSmokeSpec : CompilationModel := {
  name := "ERC4626TotalAssetsSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "totalAssets"
      params := [{ name := "vault", ty := ParamType.address }]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.totalAssets
          "assets"
          (Expr.param "vault"),
        Stmt.returnValues [Expr.localVar "assets"]
      ]
    }
  ]
}

private def erc4626AssetSmokeSpec : CompilationModel := {
  name := "ERC4626AssetSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "asset"
      params := [{ name := "vault", ty := ParamType.address }]
      returnType := none
      returns := [ParamType.address]
      body := [
        Compiler.Modules.ERC4626.asset
          "assetAddr"
          (Expr.param "vault"),
        Stmt.returnValues [Expr.localVar "assetAddr"]
      ]
    }
  ]
}

private def erc4626MaxDepositSmokeSpec : CompilationModel := {
  name := "ERC4626MaxDepositSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "maxDeposit"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "receiver", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.maxDeposit
          "assets"
          (Expr.param "vault")
          (Expr.param "receiver"),
        Stmt.returnValues [Expr.localVar "assets"]
      ]
    }
  ]
}

private def erc4626MaxMintSmokeSpec : CompilationModel := {
  name := "ERC4626MaxMintSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "maxMint"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "receiver", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.maxMint
          "shares"
          (Expr.param "vault")
          (Expr.param "receiver"),
        Stmt.returnValues [Expr.localVar "shares"]
      ]
    }
  ]
}

private def erc4626MaxWithdrawSmokeSpec : CompilationModel := {
  name := "ERC4626MaxWithdrawSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "maxWithdraw"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "owner", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.maxWithdraw
          "assets"
          (Expr.param "vault")
          (Expr.param "owner"),
        Stmt.returnValues [Expr.localVar "assets"]
      ]
    }
  ]
}

private def erc4626MaxRedeemSmokeSpec : CompilationModel := {
  name := "ERC4626MaxRedeemSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "maxRedeem"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "owner", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.maxRedeem
          "shares"
          (Expr.param "vault")
          (Expr.param "owner"),
        Stmt.returnValues [Expr.localVar "shares"]
      ]
    }
  ]
}

private def erc4626DepositSmokeSpec : CompilationModel := {
  name := "ERC4626DepositSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "deposit"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "assets", ty := ParamType.uint256 }
        , { name := "receiver", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.deposit
          "shares"
          (Expr.param "vault")
          (Expr.param "assets")
          (Expr.param "receiver"),
        Stmt.returnValues [Expr.localVar "shares"]
      ]
    }
  ]
}

set_option maxRecDepth 4096 in
#eval! do
  let compiled :=
    match Compiler.CompilationModel.compile selectorSmokeSpec (selectorsFor selectorSmokeSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "local CompilationModel smoke spec compiles with deterministic selectors" compiled

  -- Regression: selector mismatch must fail closed.
  let mismatchRejected :=
    match Compiler.CompilationModel.compile selectorSmokeSpec [] with
    | .ok _ => false
    | .error msg => contains msg "Selector count mismatch"
  expectTrue "selector mismatch is rejected with deterministic diagnostic" mismatchRejected
  expectCompileErrorContains
    "reserved compiler prefix is rejected in function parameters"
    reservedParamSpec
    "function parameter '__has_selector' uses reserved compiler prefix '__'"
  let reservedFieldRejected :=
    match validateCompileInputs reservedFieldSpec (selectorsFor reservedFieldSpec) with
    | .ok _ => false
    | .error msg => contains msg "field '__compat_value' uses reserved compiler prefix '__'"
  expectTrue "reserved compiler prefix is rejected in fields" reservedFieldRejected
  expectCompileErrorContains
    "reserved compiler prefix is rejected in local binders"
    reservedLocalBinderSpec
    "local binder '__has_selector' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in assignment targets"
    reservedAssignTargetSpec
    "assignment target '__compat_value' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in constructor parameters"
    reservedConstructorParamSpec
    "constructor parameter '__init' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in forEach binders"
    reservedForEachBinderSpec
    "local binder '__loop_idx' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "forEach binders cannot be reassigned from the loop body"
    assigningForEachBinderSpec
    "assigns to forEach binder 'i' inside the loop body"
  expectCompileErrorContains
    "forEach binders cannot shadow an existing local"
    shadowingForEachBinderSpec
    "redeclares local variable 'i' in the same scope"
  expectCompileErrorContains
    "forEach binders cannot shadow a parameter"
    paramShadowingForEachBinderSpec
    "forEach binder 'i' shadows a parameter"
  expectCompileErrorContains
    "forEach binders cannot be rebound by internal helper results"
    internalAssignForEachBinderSpec
    "redeclares local variable 'i' in the same scope"
  expectCompileErrorContains
    "forEach binders cannot be rebound by external call results"
    externalBindForEachBinderSpec
    "redeclares local variable 'i' in the same scope"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in internal call assignment binders"
    reservedInternalAssignBinderSpec
    "local binder '__ret' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in external call binders"
    reservedExternalBindSpec
    "local binder '__external_ret' uses reserved compiler prefix '__'"
  let effectOnlyExternalBindYul ← expectCompileToYul
    "effect-only external call bind compiles"
    effectOnlyExternalBindSpec
  expectTrue "effect-only external call bind lowers to a bare Yul call"
    (contains effectOnlyExternalBindYul "notify(next)" &&
      !(contains effectOnlyExternalBindYul "let  := notify(next)"))
  let cachedForEachCountYul ← expectCompileToYul
    "forEach count is cached before lowering to Yul"
    cachedForEachCountSpec
  expectTrue "forEach lowering caches the trip count once"
    (contains cachedForEachCountYul "let __for_each_count := count" &&
      contains cachedForEachCountYul "lt(i, __for_each_count)")
  expectCompileErrorContains
    "effect-only external call bind still rejects non-void externals"
    effectOnlyExternalBindMismatchSpec
    "binds 0 values from external function 'echo', but it returns 1."
  expectCompileErrorContains
    "reserved compiler prefix is rejected in ECM result binders"
    reservedEcmResultVarSpec
    "local binder '__ecm_result' uses reserved compiler prefix '__'"
  expectTrue
    "macro payable constructor preserves constructor isPayable flag"
    MacroPayableConstructorSmoke.specMarksConstructorPayable
  let payableCtorAbi := Compiler.ABI.emitContractABIJson MacroPayableConstructorSmoke.MacroPayableConstructor.spec
  expectTrue "macro payable constructor ABI reports payable state mutability"
    (contains payableCtorAbi "\"type\": \"constructor\"" &&
      contains payableCtorAbi "\"stateMutability\": \"payable\"")
  let payableCtorContract ← expectCompile
    "macro payable constructor compiles"
    MacroPayableConstructorSmoke.MacroPayableConstructor.spec
  expectTrue "macro payable constructor reaches IR with constructorPayable enabled"
    payableCtorContract.constructorPayable
  let nonPayableCtorYul ← expectCompileToYul
    "macro non-payable constructor compiles to Yul"
    MacroPayableConstructorSmoke.MacroNonPayableConstructor.spec
  let payableCtorYul ← expectCompileToYul
    "macro payable constructor compiles to Yul"
    MacroPayableConstructorSmoke.MacroPayableConstructor.spec
  expectTrue "macro payable constructor removes one deploy-time callvalue guard from rendered Yul"
    (countOccurrences nonPayableCtorYul "callvalue()" ==
      countOccurrences payableCtorYul "callvalue()" + 1)
  expectTrue
    "macro initializer prepends a single-run storage guard in the model"
    MacroInitializerSmoke.initializeModelPrependsSingleRunGuard
  expectTrue
    "macro reinitializer prepends the target-version storage guard in the model"
    MacroInitializerSmoke.initializeV2ModelPrependsVersionGuard
  expectTrue
    "macro initializer executable path seeds storage on the first call"
    MacroInitializerSmoke.initializeExecutableRunsOnce
  expectTrue
    "macro initializer executable path rejects a second call"
    MacroInitializerSmoke.initializeExecutableSecondCallReverts
  expectTrue
    "macro initializer rollback keeps the version slot unchanged when the user body reverts"
    MacroInitializerSmoke.initializeExecutableBodyRevertRollsBackVersionSlot
  expectTrue
    "macro reinitializer executable path advances the tracked version"
    MacroInitializerSmoke.reinitializerExecutableAdvancesVersion
  expectTrue
    "macro immutable spec includes internal hidden fields"
    MacroImmutableSmoke.specIncludesInternalImmutableFields
  expectTrue
    "macro immutable constructor seeds internal slots before user code"
    MacroImmutableSmoke.constructorSeedsInternalImmutableSlots
  expectTrue
    "macro immutable executable path loads runtime slot values"
    MacroImmutableSmoke.runtimeFunctionsLoadImmutableValuesFromState
  expectTrue
    "macro immutable function parameters still shadow immutable names"
    MacroImmutableSmoke.functionParamsStillShadowImmutableNames
  expectTrue
    "macro immutables synthesize a constructor when needed"
    MacroImmutableSmoke.implicitConstructorCreatedForImmutableInitializers
  expectTrue
    "macro synthesized immutable constructor reads runtime storage on the executable path"
    MacroImmutableSmoke.implicitImmutableExecutableReadsRuntimeSlot
  expectTrue
    "macro typed immutables lower to word-backed hidden slots in the spec"
    MacroImmutableSmoke.typedImmutableSpecUsesWordBackedHiddenSlots
  expectTrue
    "macro typed immutables seed word-backed hidden slots in the constructor"
    MacroImmutableSmoke.typedImmutableConstructorSeedsWordSlots
  expectTrue
    "macro typed immutables convert executable runtime reads back to source types"
    MacroImmutableSmoke.typedImmutableExecutableReadsConvertedValues
  expectTrue "macro emit lowers to Stmt.emit"
    MacroEventTraceSmoke.emitNamedModelUsesStmtEmit
  expectTrue "macro rawLog lowers to Stmt.rawLog with dynamic topic expressions"
    MacroEventTraceSmoke.emitDynamicLogModelUsesStmtRawLog
  expectTrue "macro emit executable path appends the named event trace"
    MacroEventTraceSmoke.emitNamedExecutableAppendsNamedEvent
  expectTrue "macro rawLog executable path appends the low-level event trace"
    MacroEventTraceSmoke.emitDynamicLogExecutableAppendsLowLevelTrace
  expectTrue "executable rawLog rejects more than four topics like the compiler path"
    MacroEventTraceSmoke.rawLogExecutableRejectsTooManyTopics
  let rawLogTraceYul ← expectCompileToYul
    "rawLog trace smoke spec"
    rawLogTraceSmokeSpec
  expectTrue "rawLog with dynamic topic expressions lowers to log2 in rendered Yul"
    (contains rawLogTraceYul "log2(")
  let envRuntimeYul ← expectCompileToYul "env runtime smoke compiles" envRuntimeSmokeSpec
  expectTrue "env runtime smoke lowers block.number" (contains envRuntimeYul "number()")
  let stringCompiled :=
    match Compiler.CompilationModel.compile stringAbiSpec (selectorsFor stringAbiSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "string params/returns compile via dynamic bytes path" stringCompiled
  let stringAbi := Compiler.ABI.emitContractABIJson stringAbiSpec
  expectTrue "string ABI uses Solidity string type"
    (contains stringAbi "\"type\": \"string\"")
  expectTrue "string ABI includes mixed static/dynamic and multi-dynamic functions"
    ((contains stringAbi "\"name\": \"echoAfterUint\"") &&
      (contains stringAbi "\"name\": \"echoBeforeUint\"") &&
      (contains stringAbi "\"name\": \"echoSecondString\""))
  expectTrue "string ABI includes mixed and multi-dynamic custom errors"
    ((contains stringAbi "\"name\": \"TaggedMessage\"") &&
      (contains stringAbi "\"inputs\": [{\"name\": \"\", \"type\": \"uint256\"}, {\"name\": \"\", \"type\": \"string\"}]") &&
      (contains stringAbi "\"name\": \"SecondMessage\"") &&
      (contains stringAbi "\"inputs\": [{\"name\": \"\", \"type\": \"string\"}, {\"name\": \"\", \"type\": \"string\"}]"))
  expectTrue "string ABI includes indexed and multi-head string events"
    ((contains stringAbi "\"name\": \"TaggedMessageLogged\"") &&
      (contains stringAbi "\"inputs\": [{\"name\": \"tag\", \"type\": \"uint256\", \"indexed\": true}, {\"name\": \"message\", \"type\": \"string\", \"indexed\": false}]") &&
      (contains stringAbi "\"name\": \"IndexedMessageLogged\"") &&
      (contains stringAbi "\"inputs\": [{\"name\": \"message\", \"type\": \"string\", \"indexed\": true}]") &&
      (contains stringAbi "\"name\": \"SecondMessageLogged\"") &&
      (contains stringAbi "\"inputs\": [{\"name\": \"prefix\", \"type\": \"string\", \"indexed\": false}, {\"name\": \"message\", \"type\": \"string\", \"indexed\": false}]"))
  expectCompileErrorContains
    "returnBytes rejects bytes params for string returns"
    stringReturnMismatchSpec
    "uses Stmt.returnBytes to return parameter 'message' of type"
  expectCompileErrorContains
    "string events reject bytes parameters"
    stringEventMismatchSpec
    "event 'MessageLogged' param 'message' expects"
  let stringArrayEventsCompile :=
    match Compiler.CompilationModel.compile Contracts.StringArrayEventSmoke.spec
        (selectorsFor Contracts.StringArrayEventSmoke.spec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "string[] event emission compiles for indexed and unindexed params" stringArrayEventsCompile
  let stringArrayErrorsCompile :=
    match Compiler.CompilationModel.compile Contracts.StringArrayErrorSmoke.spec
        (selectorsFor Contracts.StringArrayErrorSmoke.spec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "string[] custom errors compile for direct param refs and multi-dynamic heads"
    stringArrayErrorsCompile
  let stringArrayErrorAbi := Compiler.ABI.emitContractABIJson Contracts.StringArrayErrorSmoke.spec
  expectTrue "string[] custom error ABI uses Solidity string[] type"
    ((contains stringArrayErrorAbi "\"name\": \"BadMessages\"") &&
      (contains stringArrayErrorAbi "\"inputs\": [{\"name\": \"\", \"type\": \"string[]\"}]") &&
      (contains stringArrayErrorAbi "\"name\": \"TaggedMessages\"") &&
      (contains stringArrayErrorAbi "\"inputs\": [{\"name\": \"\", \"type\": \"uint256\"}, {\"name\": \"\", \"type\": \"string[]\"}]") &&
      (contains stringArrayErrorAbi "\"name\": \"SecondMessages\"") &&
      (contains stringArrayErrorAbi "\"inputs\": [{\"name\": \"\", \"type\": \"string[]\"}, {\"name\": \"\", \"type\": \"string[]\"}]"))
  let addressArrayReturnCompiled :=
    match Compiler.CompilationModel.compile addressArrayReturnSpec (selectorsFor addressArrayReturnSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "address[] params can round-trip through returnArray" addressArrayReturnCompiled
  expectCompileErrorContains
    "returnArray rejects bytes[] params until dynamic-element lowering lands"
    bytesArrayReturnSpec
    "only arrays with single-word static elements are currently supported"
  expectCompileErrorContains
    "arrayElement rejects bytes[] params until dynamic-element indexing lands"
    bytesArrayElementSpec
    "Expr.arrayElement 'calls' requires an array with single-word static elements"
  let storageArrayUint256Yul ←
    expectCompileToYul "storage uint256[] smoke spec" storageArrayUint256SmokeSpec
  expectTrue "storage uint256[] length lowers to sload(slot)"
    (contains storageArrayUint256Yul "sload(7)")
  expectTrue "storage uint256[] indexed reads use the checked storage-array helper"
    ((contains storageArrayUint256Yul checkedStorageArrayElementHelperName) &&
      (contains storageArrayUint256Yul "function __verity_storage_array_element_checked(slot, index)"))
  expectTrue "storage uint256[] push computes the Solidity base slot and bumps length"
    ((contains storageArrayUint256Yul "mstore(0, 7)") &&
      (contains storageArrayUint256Yul "keccak256(0, 32)") &&
      (contains storageArrayUint256Yul "sstore(7, add(__array_len, 1))"))
  expectTrue "storage uint256[] indexed writes guard bounds"
    (contains storageArrayUint256Yul "lt(__array_index, __array_len)")
  expectTrue "storage uint256[] pop clears the removed tail word"
    (contains storageArrayUint256Yul "sstore(add(__array_base, __array_new_len), 0)")
  expectTrue "storageArrayPush is tracked as reading state"
    (Compiler.CompilationModel.stmtReadsStateOrEnv
      (Stmt.storageArrayPush "queue" (Expr.literal 1)))
  expectTrue "setStorageArrayElement is tracked as reading state"
    (Compiler.CompilationModel.stmtReadsStateOrEnv
      (Stmt.setStorageArrayElement "queue" (Expr.literal 0) (Expr.literal 1)))
  expectCompileErrorContains
    "storage bool[] rejects packed element layouts until slot packing lands"
    storageArrayBoolRejectSpec
    "only one-storage-word elements (uint256, address, bytes32)"
  let envYul ← expectCompileToYul "env runtime smoke spec" envRuntimeSmokeSpec
  expectTrue "address(this) lowers to the Yul address builtin"
    (contains envYul "address()")
  expectTrue "msg.value lowers to the Yul callvalue builtin"
    (contains envYul "callvalue()")
  expectTrue "block.timestamp lowers to the Yul timestamp builtin"
    (contains envYul "timestamp()")
  expectTrue "chainid lowers to the Yul chainid builtin"
    (contains envYul "chainid()")
  expectTrue "blobbasefee lowers to the Yul blobbasefee builtin"
    (contains envYul "blobbasefee()")
  let ecrecoverYul ←
    expectCompileToYul "ecrecover smoke spec" ecrecoverSmokeSpec
  expectTrue "ecrecover ECM lowers to precompile staticcall"
    (contains ecrecoverYul "staticcall(gas(), 1, 0, 128, 0, 32)")
  expectTrue "ecrecover ECM reverts when the precompile call fails"
    (contains ecrecoverYul "if iszero(__ecr_success) {")
  expectTrue "ecrecover ECM zeroes scratch memory on empty returndata"
    (contains ecrecoverYul "if iszero(returndatasize()) {")
  expectTrue "ecrecover ECM masks recovered address to 160 bits"
    (contains ecrecoverYul "let signer := and(mload(0), 0xffffffffffffffffffffffffffffffffffffffff)")
  let oracleReadYul ←
    expectCompileToYul "oracle read smoke spec" oracleReadSmokeSpec
  expectTrue "oracle read ECM lowers to staticcall"
    (contains oracleReadYul "staticcall(gas(), oracle, 0, 36, 0, 32)")
  expectTrue "oracle read ECM forwards revert returndata"
    (contains oracleReadYul "returndatacopy(0, 0, __oracle_rds)")
  expectTrue "oracle read ECM rejects non-32-byte returndata"
    (contains oracleReadYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "oracle read ECM ABI-encodes the selector"
    (contains oracleReadYul "mstore(0, shl(224, 0xfeaf968c))")
  let erc20BalanceOfYul ←
    expectCompileToYul "erc20 balanceOf smoke spec" erc20BalanceOfSmokeSpec
  expectTrue "erc20 balanceOf ECM lowers to staticcall"
    (contains erc20BalanceOfYul "staticcall(gas(), token, 0, 36, 0, 32)")
  expectTrue "erc20 balanceOf ECM forwards revert returndata"
    (contains erc20BalanceOfYul "returndatacopy(0, 0, __balanceOf_rds)")
  expectTrue "erc20 balanceOf ECM rejects non-32-byte returndata"
    (contains erc20BalanceOfYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc20 balanceOf ECM ABI-encodes the selector"
    (contains erc20BalanceOfYul "mstore(0, shl(224, 0x70a08231))")
  let erc20AllowanceYul ←
    expectCompileToYul "erc20 allowance smoke spec" erc20AllowanceSmokeSpec
  expectTrue "erc20 allowance ECM lowers to staticcall"
    (contains erc20AllowanceYul "staticcall(gas(), token, 0, 68, 0, 32)")
  expectTrue "erc20 allowance ECM forwards revert returndata"
    (contains erc20AllowanceYul "returndatacopy(0, 0, __allowance_rds)")
  expectTrue "erc20 allowance ECM rejects non-32-byte returndata"
    (contains erc20AllowanceYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc20 allowance ECM ABI-encodes the selector"
    (contains erc20AllowanceYul "mstore(0, shl(224, 0xdd62ed3e))")
  let erc20TotalSupplyYul ←
    expectCompileToYul "erc20 totalSupply smoke spec" erc20TotalSupplySmokeSpec
  expectTrue "erc20 totalSupply ECM lowers to staticcall"
    (contains erc20TotalSupplyYul "staticcall(gas(), token, 0, 4, 0, 32)")
  expectTrue "erc20 totalSupply ECM forwards revert returndata"
    (contains erc20TotalSupplyYul "returndatacopy(0, 0, __totalSupply_rds)")
  expectTrue "erc20 totalSupply ECM rejects non-32-byte returndata"
    (contains erc20TotalSupplyYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc20 totalSupply ECM ABI-encodes the selector"
    (contains erc20TotalSupplyYul "mstore(0, shl(224, 0x18160ddd))")
  let erc4626PreviewDepositYul ←
    expectCompileToYul "erc4626 previewDeposit smoke spec" erc4626PreviewDepositSmokeSpec
  expectTrue "erc4626 previewDeposit ECM lowers to staticcall"
    (contains erc4626PreviewDepositYul "staticcall(gas(), vault, 0, 36, 0, 32)")
  expectTrue "erc4626 previewDeposit ECM forwards revert returndata"
    (contains erc4626PreviewDepositYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 previewDeposit ECM rejects non-32-byte returndata"
    (contains erc4626PreviewDepositYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 previewDeposit ECM ABI-encodes the selector"
    (contains erc4626PreviewDepositYul "mstore(0, shl(224, 0xef8b30f7))")
  let erc4626PreviewMintYul ←
    expectCompileToYul "erc4626 previewMint smoke spec" erc4626PreviewMintSmokeSpec
  expectTrue "erc4626 previewMint ECM lowers to staticcall"
    (contains erc4626PreviewMintYul "staticcall(gas(), vault, 0, 36, 0, 32)")
  expectTrue "erc4626 previewMint ECM forwards revert returndata"
    (contains erc4626PreviewMintYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 previewMint ECM rejects non-32-byte returndata"
    (contains erc4626PreviewMintYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 previewMint ECM ABI-encodes the selector"
    (contains erc4626PreviewMintYul "mstore(0, shl(224, 0xb3d7f6b9))")
  let erc4626PreviewWithdrawYul ←
    expectCompileToYul "erc4626 previewWithdraw smoke spec" erc4626PreviewWithdrawSmokeSpec
  expectTrue "erc4626 previewWithdraw ECM lowers to staticcall"
    (contains erc4626PreviewWithdrawYul "staticcall(gas(), vault, 0, 36, 0, 32)")
  expectTrue "erc4626 previewWithdraw ECM forwards revert returndata"
    (contains erc4626PreviewWithdrawYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 previewWithdraw ECM rejects non-32-byte returndata"
    (contains erc4626PreviewWithdrawYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 previewWithdraw ECM ABI-encodes the selector"
    (contains erc4626PreviewWithdrawYul "mstore(0, shl(224, 0x0a28a477))")
  let erc4626PreviewRedeemYul ←
    expectCompileToYul "erc4626 previewRedeem smoke spec" erc4626PreviewRedeemSmokeSpec
  expectTrue "erc4626 previewRedeem ECM lowers to staticcall"
    (contains erc4626PreviewRedeemYul "staticcall(gas(), vault, 0, 36, 0, 32)")
  expectTrue "erc4626 previewRedeem ECM forwards revert returndata"
    (contains erc4626PreviewRedeemYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 previewRedeem ECM rejects non-32-byte returndata"
    (contains erc4626PreviewRedeemYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 previewRedeem ECM ABI-encodes the selector"
    (contains erc4626PreviewRedeemYul "mstore(0, shl(224, 0x4cdad506))")
  let erc4626ConvertToAssetsYul ←
    expectCompileToYul "erc4626 convertToAssets smoke spec" erc4626ConvertToAssetsSmokeSpec
  expectTrue "erc4626 convertToAssets ECM lowers to staticcall"
    (contains erc4626ConvertToAssetsYul "staticcall(gas(), vault, 0, 36, 0, 32)")
  expectTrue "erc4626 convertToAssets ECM forwards revert returndata"
    (contains erc4626ConvertToAssetsYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 convertToAssets ECM rejects non-32-byte returndata"
    (contains erc4626ConvertToAssetsYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 convertToAssets ECM ABI-encodes the selector"
    (contains erc4626ConvertToAssetsYul "mstore(0, shl(224, 0x07a2d13a))")
  let erc4626ConvertToSharesYul ←
    expectCompileToYul "erc4626 convertToShares smoke spec" erc4626ConvertToSharesSmokeSpec
  expectTrue "erc4626 convertToShares ECM lowers to staticcall"
    (contains erc4626ConvertToSharesYul "staticcall(gas(), vault, 0, 36, 0, 32)")
  expectTrue "erc4626 convertToShares ECM forwards revert returndata"
    (contains erc4626ConvertToSharesYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 convertToShares ECM rejects non-32-byte returndata"
    (contains erc4626ConvertToSharesYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 convertToShares ECM ABI-encodes the selector"
    (contains erc4626ConvertToSharesYul "mstore(0, shl(224, 0xc6e6f592))")
  let erc4626TotalAssetsYul ←
    expectCompileToYul "erc4626 totalAssets smoke spec" erc4626TotalAssetsSmokeSpec
  expectTrue "erc4626 totalAssets ECM lowers to staticcall"
    (contains erc4626TotalAssetsYul "staticcall(gas(), vault, 0, 4, 0, 32)")
  expectTrue "erc4626 totalAssets ECM forwards revert returndata"
    (contains erc4626TotalAssetsYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 totalAssets ECM rejects non-32-byte returndata"
    (contains erc4626TotalAssetsYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 totalAssets ECM ABI-encodes the selector"
    (contains erc4626TotalAssetsYul "mstore(0, shl(224, 0x01e1d114))")
  let erc4626AssetYul ←
    expectCompileToYul "erc4626 asset smoke spec" erc4626AssetSmokeSpec
  expectTrue "erc4626 asset ECM lowers to staticcall"
    (contains erc4626AssetYul "staticcall(gas(), vault, 0, 4, 0, 32)")
  expectTrue "erc4626 asset ECM forwards revert returndata"
    (contains erc4626AssetYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 asset ECM rejects non-32-byte returndata"
    (contains erc4626AssetYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 asset ECM ABI-encodes the selector"
    (contains erc4626AssetYul "mstore(0, shl(224, 0x38d52e0f))")
  expectTrue "erc4626 asset ECM masks the returned address"
    (contains erc4626AssetYul "let assetAddr := and(mload(0), 0xffffffffffffffffffffffffffffffffffffffff)")
  let erc4626MaxDepositYul ←
    expectCompileToYul "erc4626 maxDeposit smoke spec" erc4626MaxDepositSmokeSpec
  expectTrue "erc4626 maxDeposit ECM lowers to staticcall"
    (contains erc4626MaxDepositYul "staticcall(gas(), vault, 0, 36, 0, 32)")
  expectTrue "erc4626 maxDeposit ECM forwards revert returndata"
    (contains erc4626MaxDepositYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 maxDeposit ECM rejects non-32-byte returndata"
    (contains erc4626MaxDepositYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 maxDeposit ECM ABI-encodes the selector"
    (contains erc4626MaxDepositYul "mstore(0, shl(224, 0x402d267d))")
  let erc4626MaxMintYul ←
    expectCompileToYul "erc4626 maxMint smoke spec" erc4626MaxMintSmokeSpec
  expectTrue "erc4626 maxMint ECM lowers to staticcall"
    (contains erc4626MaxMintYul "staticcall(gas(), vault, 0, 36, 0, 32)")
  expectTrue "erc4626 maxMint ECM forwards revert returndata"
    (contains erc4626MaxMintYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 maxMint ECM rejects non-32-byte returndata"
    (contains erc4626MaxMintYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 maxMint ECM ABI-encodes the selector"
    (contains erc4626MaxMintYul "mstore(0, shl(224, 0xc63d75b6))")
  let erc4626MaxWithdrawYul ←
    expectCompileToYul "erc4626 maxWithdraw smoke spec" erc4626MaxWithdrawSmokeSpec
  expectTrue "erc4626 maxWithdraw ECM lowers to staticcall"
    (contains erc4626MaxWithdrawYul "staticcall(gas(), vault, 0, 36, 0, 32)")
  expectTrue "erc4626 maxWithdraw ECM forwards revert returndata"
    (contains erc4626MaxWithdrawYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 maxWithdraw ECM rejects non-32-byte returndata"
    (contains erc4626MaxWithdrawYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 maxWithdraw ECM ABI-encodes the selector"
    (contains erc4626MaxWithdrawYul "mstore(0, shl(224, 0xce96cb77))")
  let erc4626MaxRedeemYul ←
    expectCompileToYul "erc4626 maxRedeem smoke spec" erc4626MaxRedeemSmokeSpec
  expectTrue "erc4626 maxRedeem ECM lowers to staticcall"
    (contains erc4626MaxRedeemYul "staticcall(gas(), vault, 0, 36, 0, 32)")
  expectTrue "erc4626 maxRedeem ECM forwards revert returndata"
    (contains erc4626MaxRedeemYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 maxRedeem ECM rejects non-32-byte returndata"
    (contains erc4626MaxRedeemYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 maxRedeem ECM ABI-encodes the selector"
    (contains erc4626MaxRedeemYul "mstore(0, shl(224, 0xd905777e))")
  let erc4626DepositYul ←
    expectCompileToYul "erc4626 deposit smoke spec" erc4626DepositSmokeSpec
  expectTrue "erc4626 deposit ECM lowers to call"
    (contains erc4626DepositYul "call(gas(), vault, 0, 0, 68, 0, 32)")
  expectTrue "erc4626 deposit ECM forwards revert returndata"
    (contains erc4626DepositYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 deposit ECM rejects non-32-byte returndata"
    (contains erc4626DepositYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 deposit ECM ABI-encodes the selector"
    (contains erc4626DepositYul "mstore(0, shl(224, 0x6e553f65))")
  let macroEcrecoverYul ←
    expectCompileToYul "macro ecrecover smoke spec" MacroEcrecoverSmoke.MacroEcrecover.spec
  expectTrue "macro ecrecover bind elaborates to the same ECM lowering"
    (contains macroEcrecoverYul "staticcall(gas(), 1, 0, 128, 0, 32)")
  let macroTrustReport := emitTrustReportJson [MacroEcrecoverSmoke.MacroEcrecover.spec]
  expectTrue "macro ecrecover trust report surfaces the precompile assumption"
    (contains macroTrustReport "\"module\":\"ecrecover\"" &&
      contains macroTrustReport "\"assumption\":\"evm_ecrecover_precompile\"")
  let macroKeccakYul ←
    expectCompileToYul "macro keccak smoke spec" MacroKeccakSmoke.MacroKeccak.spec
  expectTrue "macro keccak primitive lowers to the Yul keccak256 builtin"
    (contains macroKeccakYul "keccak256(offset, size)")
  let macroKeccakTrustReport := emitTrustReportJson [MacroKeccakSmoke.MacroKeccak.spec]
  expectTrue "macro keccak trust report surfaces the named primitive assumption"
    (contains macroKeccakTrustReport "\"primitive\":\"keccak256\"" &&
      contains macroKeccakTrustReport "\"assumption\":\"keccak256_memory_slice_matches_evm\"")
  let macroTransientYul ←
    expectCompileToYul "macro transient storage smoke spec" MacroTransientStorageSmoke.MacroTransientStorage.spec
  expectTrue "macro transient storage lowers to the Yul transient builtins"
    (contains macroTransientYul "tstore(" &&
      contains macroTransientYul "tload(")
  expectTrue "macro transient storage executable path uses the transient state map"
    MacroTransientStorageSmoke.warmExecutableWritesTransientStorage
  expectTrue "macro transient storage round-trips across executable calls"
    MacroTransientStorageSmoke.transientStoragePersistsAcrossExecutableCalls
  let macroTransientTrustReport := emitTrustReportJson [MacroTransientStorageSmoke.MacroTransientStorage.spec]
  expectTrue "macro transient storage trust report surfaces low-level mechanics"
    (contains macroTransientTrustReport "\"modeledLowLevelMechanics\"" &&
      contains macroTransientTrustReport "\"tstore\"" &&
      contains macroTransientTrustReport "\"tload\"")
  let macroBlobbasefeeYul ←
    expectCompileToYul "macro blobbasefee smoke spec" MacroBlobbasefeeSmoke.MacroBlobbasefee.spec
  expectTrue "macro blobbasefee lowers to the Yul blobbasefee builtin"
    (contains macroBlobbasefeeYul "blobbasefee()")
  expectTrue "macro blobbasefee executable path uses the runtime stub"
    MacroBlobbasefeeSmoke.executableUsesRuntimeStub
  let macroBlobbasefeeTrustReport := emitTrustReportJson [MacroBlobbasefeeSmoke.MacroBlobbasefee.spec]
  expectTrue "macro blobbasefee trust report surfaces the post-core builtin"
    (contains macroBlobbasefeeTrustReport "\"modeledLowLevelMechanics\"" &&
      contains macroBlobbasefeeTrustReport "\"blobbasefee\"")
  let macroExternalYul ←
    expectCompileToYul "macro external smoke spec" MacroExternalSmoke.MacroExternal.spec
  expectTrue "macro externalCall lowers to the linked external symbol"
    (contains macroExternalYul "let echoed := echo(next)")
  let macroExternalTrustReport := emitTrustReportJson [MacroExternalSmoke.MacroExternal.spec]
  expectTrue "macro externals surface in the trust report"
    (contains macroExternalTrustReport "\"linkedExternals\"" &&
      contains macroExternalTrustReport "\"echo\"")
  expectTrue "macro constant expressions inline into model bodies"
    MacroConstantSmoke.feeOnModelInlinesContractConstants
  expectTrue "macro address constants inline through the executable and model paths"
    (MacroConstantSmoke.treasuryAddrModelInlinesAddressConstant &&
      MacroConstantSmoke.treasuryExecutableUsesGeneratedConstantDef)
  expectTrue "macro nested constants inline transitively"
    MacroConstantSmoke.treasuryAsWordModelInlinesNestedConstants
  expectTrue "macro locals and params shadow contract constants"
    MacroConstantSmoke.shadowedConstantModelPrefersLocalAndParamBindings

end Compiler.CompilationModelFeatureTest
