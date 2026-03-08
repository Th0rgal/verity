import Compiler.CompilationModel
import Compiler.ABI
import Compiler.Codegen
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
  let macroEcrecoverYul ←
    expectCompileToYul "macro ecrecover smoke spec" MacroEcrecoverSmoke.MacroEcrecover.spec
  expectTrue "macro ecrecover bind elaborates to the same ECM lowering"
    (contains macroEcrecoverYul "staticcall(gas(), 1, 0, 128, 0, 32)")
  let macroTrustReport := emitTrustReportJson [MacroEcrecoverSmoke.MacroEcrecover.spec]
  expectTrue "macro ecrecover trust report surfaces the precompile assumption"
    (contains macroTrustReport "\"module\":\"ecrecover\"" &&
      contains macroTrustReport "\"assumption\":\"evm_ecrecover_precompile\"")

end Compiler.CompilationModelFeatureTest
