import Compiler.CompilationModel
import Compiler.ABI
import Compiler.Codegen
import Compiler.Modules.ERC4626
import Compiler.Modules.ERC20
import Compiler.Modules.Oracle
import Compiler.Modules.Precompiles
import Compiler.Yul.PrettyPrint
import Contracts.Common

namespace Compiler.CompilationModelFeatureTest

open Compiler
open Compiler.CompilationModel

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

namespace MacroTupleDestructuringSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroTupleDestructuring where
  storage
    firstSlot : Uint256 := slot 0
    secondSlot : Uint256 := slot 1

  function storePair (pair : Tuple [Uint256, Uint256]) : Unit := do
    let (first, second) := pair
    setStorage firstSlot first
    setStorage secondSlot second

  function storeLiteralPair (seed : Uint256) : Unit := do
    let (first, second) := (seed, add seed 1)
    setStorage firstSlot first
    setStorage secondSlot second

  function echoPair (pair : Tuple [Uint256, Uint256]) : Tuple [Uint256, Uint256] := do
    let (first, second) := pair
    return (first, second)

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

def echoPairExecutableKeepsTupleShape : Bool :=
  match MacroTupleDestructuring.echoPair (11, 17) Verity.defaultState with
  | .success (first, second) state =>
      first == 11 && second == 17 && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : echoPairExecutableKeepsTupleShape = true := by native_decide

end MacroTupleDestructuringSmoke

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
      returns := [ParamType.address, ParamType.uint256, ParamType.uint256, ParamType.uint256, ParamType.uint256]
      body := [
        Stmt.returnValues [Expr.contractAddress, Expr.msgValue, Expr.blockTimestamp, Expr.blockNumber, Expr.chainid]
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
  ]
  events := [
    { name := "MessageLogged"
      params := [{ name := "message", ty := ParamType.string, kind := EventParamKind.unindexed }]
    }
  ]
  errors := [
    { name := "BadMessage"
      params := [ParamType.string]
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

private def stringArrayEventSpec : CompilationModel := {
  name := "StringArrayEvents"
  fields := []
  «constructor» := none
  functions := [
    { name := "log"
      params := [{ name := "messages", ty := ParamType.array ParamType.string }]
      returnType := none
      body := [
        Stmt.emit "MessageBatch" [Expr.param "messages", Expr.param "messages"],
        Stmt.stop
      ]
    }
  ]
  events := [
    { name := "MessageBatch"
      params := [
        { name := "body", ty := ParamType.array ParamType.string, kind := EventParamKind.unindexed },
        { name := "topicBody", ty := ParamType.array ParamType.string, kind := EventParamKind.indexed }
      ]
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
  expectCompileErrorContains
    "reserved compiler prefix is rejected in local binders"
    reservedLocalBinderSpec
    "local binder '__has_selector' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in constructor parameters"
    reservedConstructorParamSpec
    "constructor parameter '__init' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in forEach binders"
    reservedForEachBinderSpec
    "local binder '__loop_idx' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in internal call assignment binders"
    reservedInternalAssignBinderSpec
    "local binder '__ret' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in external call binders"
    reservedExternalBindSpec
    "local binder '__external_ret' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in ECM result binders"
    reservedEcmResultVarSpec
    "local binder '__ecm_result' uses reserved compiler prefix '__'"
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
  expectCompileErrorContains
    "returnBytes rejects bytes params for string returns"
    stringReturnMismatchSpec
    "uses Stmt.returnBytes to return parameter 'message' of type"
  expectCompileErrorContains
    "string events reject bytes parameters"
    stringEventMismatchSpec
    "event 'MessageLogged' param 'message' expects"
  let stringArrayEventsCompile :=
    match Compiler.CompilationModel.compile stringArrayEventSpec (selectorsFor stringArrayEventSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "string[] event emission compiles for indexed and unindexed params" stringArrayEventsCompile
  let envYul ← expectCompileToYul "env runtime smoke spec" envRuntimeSmokeSpec
  expectTrue "address(this) lowers to the Yul address builtin"
    (contains envYul "address()")
  expectTrue "msg.value lowers to the Yul callvalue builtin"
    (contains envYul "callvalue()")
  expectTrue "block.timestamp lowers to the Yul timestamp builtin"
    (contains envYul "timestamp()")
  expectTrue "chainid lowers to the Yul chainid builtin"
    (contains envYul "chainid()")
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

end Compiler.CompilationModelFeatureTest
