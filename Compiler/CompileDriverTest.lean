import Contracts
import Compiler.CompileDriver
import Compiler.CompilationModel
import Compiler.CompilationModel.TrustSurface
import Compiler.ECM
import Compiler.ModuleInput
import Compiler.Modules.ERC4626
import Compiler.Modules.ERC20
import Compiler.Modules.Oracle
import Compiler.Modules.Precompiles
import Compiler.TestModules

namespace Compiler.CompileDriverTest

open Compiler
open Compiler.CompilationModel

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

private def expectFailureContains (label : String) (action : IO Unit) (needle : String) : IO Unit := do
  try
    action
    throw (IO.userError s!"✗ {label}: expected failure, command succeeded")
  catch e =>
    let msg := e.toString
    if !contains msg needle then
      throw (IO.userError s!"✗ {label}: expected '{needle}', got:\n{msg}")
    IO.println s!"✓ {label}"

private def fileExists (path : String) : IO Bool := do
  try
    let _ ← IO.FS.readFile path
    pure true
  catch _ =>
    pure false

private def expectFileEquals (label : String) (lhs rhs : String) : IO Unit := do
  let lhsText ← IO.FS.readFile lhs
  let rhsText ← IO.FS.readFile rhs
  if lhsText != rhsText then
    throw (IO.userError s!"✗ {label}: files differ\nlhs: {lhs}\nrhs: {rhs}")
  IO.println s!"✓ {label}"

private def expectFileContains (label path : String) (needles : List String) : IO Unit := do
  let text ← IO.FS.readFile path
  for needle in needles do
    if !contains text needle then
      throw (IO.userError s!"✗ {label}: missing '{needle}' in:\n{text}")
  IO.println s!"✓ {label}"

private def abiSmokeSpec : CompilationModel := {
  name := "AbiSmoke"
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
    }
  ]
}

private def stringAbiSmokeSpec : CompilationModel := {
  name := "StringAbiSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "echoString"
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

private def linkedLibrarySpec : CompilationModel := {
  name := "LinkedLibrarySmoke"
  fields := [{ name := "lastHash", ty := FieldType.uint256 }]
  «constructor» := none
  externals := [
    { name := "PoseidonT3_hash"
      params := [ParamType.uint256, ParamType.uint256]
      returnType := some ParamType.uint256
      axiomNames := ["poseidon_t3_deterministic"] }
  ]
  functions := [
    { name := "storeHash"
      params := [
        { name := "a", ty := ParamType.uint256 }
      , { name := "b", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        Stmt.letVar "h" (Expr.externalCall "PoseidonT3_hash" [Expr.param "a", Expr.param "b"]),
        Stmt.setStorage "lastHash" (Expr.localVar "h"),
        Stmt.stop
      ]
    }
  ]
}

private def trustSurfaceSpec : CompilationModel := {
  name := "TrustSurfaceSmoke"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  externals := [
    { name := "PoseidonT3_hash"
      params := [ParamType.uint256, ParamType.uint256]
      returnType := some ParamType.uint256
      axiomNames := ["poseidon_t3_deterministic"] }
  ]
  functions := [
    { name := "exercise"
      params := [{ name := "target", ty := ParamType.address }]
      returnType := none
      body := [
        Stmt.letVar "ok"
          (Expr.staticcall
            (Expr.literal 5000)
            (Expr.param "target")
            (Expr.literal 0)
            (Expr.literal 0)
            (Expr.literal 0)
            (Expr.literal 32)),
        Stmt.letVar "rd" Expr.returndataSize,
        Stmt.returndataCopy (Expr.literal 0) (Expr.literal 0) (Expr.localVar "rd"),
        Stmt.letVar "digest" (Expr.keccak256 (Expr.literal 0) (Expr.literal 64)),
        Stmt.letVar "hash" (Expr.externalCall "PoseidonT3_hash" [Expr.literal 1, Expr.literal 2]),
        Stmt.ecm
          { name := "testCall"
            numArgs := 1
            resultVars := []
            writesState := false
            readsState := true
            axioms := ["test_call_interface"]
            compile := fun _ _ => pure [] }
          [Expr.localVar "hash"],
        Stmt.setStorage "value" (Expr.add (Expr.localVar "ok") (Expr.localVar "digest")),
        Stmt.stop
      ]
    }
  ]
}

private def uncheckedTrustSurfaceSpec : CompilationModel := {
  name := "UncheckedTrustSurface"
  fields := []
  «constructor» := none
  externals := [
    { name := "DebugOracle_peek"
      params := []
      returnType := some ParamType.uint256
      proofStatus := .unchecked
      axiomNames := [] }
  ]
  functions := [
    { name := "exercise"
      params := []
      returnType := none
      body := [
        Stmt.letVar "peek" (Expr.externalCall "DebugOracle_peek" []),
        Stmt.ecm
          { name := "debugHook"
            numArgs := 1
            resultVars := []
            writesState := false
            readsState := true
            proofStatus := .unchecked
            axioms := []
            compile := fun _ _ => pure [] }
          [Expr.localVar "peek"],
        Stmt.stop
      ]
    }
  ]
}

private def constructorOnlyEcmTrustSurfaceSpec : CompilationModel := {
  name := "ConstructorOnlyEcmTrustSurface"
  fields := []
  «constructor» := some {
    params := []
    body := [
      Stmt.ecm
        { name := "ctorHook"
          numArgs := 0
          resultVars := []
          writesState := false
          readsState := true
          proofStatus := .unchecked
          axioms := ["ctor_hook_interface"]
          compile := fun _ _ => pure [] }
        [],
      Stmt.stop
    ]
  }
  functions := [
    { name := "ping"
      params := []
      returnType := none
      body := [Stmt.stop]
    }
  ]
}

private def ecrecoverTrustSurfaceSpec : CompilationModel := {
  name := "EcrecoverTrustSurface"
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

private def oracleTrustSurfaceSpec : CompilationModel := {
  name := "OracleTrustSurface"
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

private def erc20BalanceOfTrustSurfaceSpec : CompilationModel := {
  name := "ERC20BalanceOfTrustSurface"
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

private def erc20AllowanceTrustSurfaceSpec : CompilationModel := {
  name := "ERC20AllowanceTrustSurface"
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

private def erc4626TrustSurfaceSpec : CompilationModel := {
  name := "ERC4626TrustSurface"
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

private def erc4626PreviewRedeemTrustSurfaceSpec : CompilationModel := {
  name := "ERC4626PreviewRedeemTrustSurface"
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

private def expectModuleArtifacts
    (labelPrefix : String)
    (modules : List String)
    (outDir abiDir : String) : IO Unit := do
  for moduleName in modules do
    let contractName := contractNameOfModule moduleName
    let yulPath := s!"{outDir}/{contractName}.yul"
    let abiPath := s!"{abiDir}/{contractName}.abi.json"
    let yulExists ← fileExists yulPath
    let abiExists ← fileExists abiPath
    if !yulExists || !abiExists then
      throw (IO.userError s!"✗ {labelPrefix}: missing artifacts for {contractName}")
  IO.println s!"✓ {labelPrefix}"

private def expectOnlySelectedArtifacts
    (label : String)
    (selectedModules : List String)
    (allModules : List String)
    (outDir abiDir : String) : IO Unit := do
  for moduleName in allModules do
    let contractName := contractNameOfModule moduleName
    let shouldExist := selectedModules.contains moduleName
    let yulExists ← fileExists s!"{outDir}/{contractName}.yul"
    let abiExists ← fileExists s!"{abiDir}/{contractName}.abi.json"
    if yulExists != shouldExist then
      throw (IO.userError
        s!"✗ {label}: unexpected Yul artifact presence for {contractName} (expected={shouldExist}, found={yulExists})")
    if abiExists != shouldExist then
      throw (IO.userError
        s!"✗ {label}: unexpected ABI artifact presence for {contractName} (expected={shouldExist}, found={abiExists})")
  IO.println s!"✓ {label}"

unsafe def runTests : IO Unit := do
  let nonce ← IO.rand 0 1000000000
  let outDir := s!"/tmp/verity-compile-driver-test-{nonce}-out"
  let abiDir := s!"/tmp/verity-compile-driver-test-{nonce}-abi"
  let manifestOutDir := s!"/tmp/verity-compile-driver-test-{nonce}-manifest-out"
  let manifestAbiDir := s!"/tmp/verity-compile-driver-test-{nonce}-manifest-abi"
  let selectedOutDir := s!"/tmp/verity-compile-driver-test-{nonce}-selected-out"
  let selectedAbiDir := s!"/tmp/verity-compile-driver-test-{nonce}-selected-abi"
  let reversedOutDir := s!"/tmp/verity-compile-driver-test-{nonce}-reversed-out"
  let reversedAbiDir := s!"/tmp/verity-compile-driver-test-{nonce}-reversed-abi"
  let stringOutDir := s!"/tmp/verity-compile-driver-test-{nonce}-string-out"
  let stringAbiDir := s!"/tmp/verity-compile-driver-test-{nonce}-string-abi"
  let trustReportDir := s!"/tmp/verity-compile-driver-test-{nonce}-reports/trust"
  let trustReportPath := s!"{trustReportDir}/trust-report.json"
  let patchReportDir := s!"/tmp/verity-compile-driver-test-{nonce}-reports/patch"
  let patchReportPath := s!"{patchReportDir}/patch-report.tsv"
  let missingLib := "/tmp/definitely-missing-library.yul"
  let earlySuccessfulAbi := s!"{abiDir}/AbiSmoke.abi.json"

  IO.FS.createDirAll outDir
  IO.FS.createDirAll abiDir
  IO.FS.createDirAll manifestOutDir
  IO.FS.createDirAll manifestAbiDir
  IO.FS.createDirAll selectedOutDir
  IO.FS.createDirAll selectedAbiDir
  IO.FS.createDirAll reversedOutDir
  IO.FS.createDirAll reversedAbiDir
  IO.FS.createDirAll stringOutDir
  IO.FS.createDirAll stringAbiDir

  try IO.FS.removeFile earlySuccessfulAbi catch _ => pure ()

  expectFailureContains
    "compileSpecsWithOptions reports missing linked library"
    (compileSpecsWithOptions [abiSmokeSpec, linkedLibrarySpec] outDir false [missingLib] {} none none (some abiDir))
    missingLib

  let hasEarlySuccessfulAbi ← fileExists earlySuccessfulAbi
  if !hasEarlySuccessfulAbi then
    throw (IO.userError s!"✗ expected ABI artifact for early successful contract, missing: {earlySuccessfulAbi}")
  IO.println "✓ ABI artifacts still emitted for contracts compiled before failure"

  compileSpecsWithOptions [stringAbiSmokeSpec] stringOutDir false [] {} none none (some stringAbiDir)
  expectFileContains
    "compileSpecsWithOptions emits string ABI artifacts"
    s!"{stringAbiDir}/StringAbiSmoke.abi.json"
    [ "\"name\": \"echoString\""
    , "\"inputs\": [{\"name\": \"message\", \"type\": \"string\"}]"
    , "\"outputs\": [{\"name\": \"\", \"type\": \"string\"}]"
    , "\"name\": \"MessageLogged\""
    , "\"name\": \"BadMessage\""
    ]

  compileModulesWithOptions outDir canonicalModules false [] {} none none (some abiDir)
  expectModuleArtifacts "explicit module list emits Yul/ABI for all requested contracts" canonicalModules outDir abiDir

  let manifestModules ←
    match ← Compiler.ModuleInput.resolveRawModules (some "packages/verity-examples/contracts.manifest") [] with
    | .ok modules => pure modules
    | .error err => throw (IO.userError err)
  compileModulesWithOptions manifestOutDir manifestModules false [] {} none none (some manifestAbiDir)
  expectModuleArtifacts "manifest module list emits Yul/ABI for all requested contracts" manifestModules manifestOutDir manifestAbiDir

  for moduleName in canonicalModules do
    let contractName := contractNameOfModule moduleName
    expectFileEquals
      s!"manifest parity Yul: {contractName}"
      s!"{outDir}/{contractName}.yul"
      s!"{manifestOutDir}/{contractName}.yul"
    expectFileEquals
      s!"manifest parity ABI: {contractName}"
      s!"{abiDir}/{contractName}.abi.json"
      s!"{manifestAbiDir}/{contractName}.abi.json"

  let selectedModules := ["Contracts.SimpleStorage.SimpleStorage", "Contracts.Counter.Counter"]
  compileModulesWithOptions selectedOutDir selectedModules false [] {} none none (some selectedAbiDir)
  expectOnlySelectedArtifacts
    "selected module compilation emits only requested artifacts"
    selectedModules
    canonicalModules
    selectedOutDir
    selectedAbiDir

  compileModulesWithOptions reversedOutDir selectedModules.reverse false [] {} none none (some reversedAbiDir)
  expectOnlySelectedArtifacts
    "selected module compilation is order-invariant for artifact set"
    selectedModules
    canonicalModules
    reversedOutDir
    reversedAbiDir

  for moduleName in selectedModules do
    let contractName := contractNameOfModule moduleName
    expectFileEquals
      s!"selected module order-invariant Yul: {contractName}"
      s!"{selectedOutDir}/{contractName}.yul"
      s!"{reversedOutDir}/{contractName}.yul"
    expectFileEquals
      s!"selected module order-invariant ABI: {contractName}"
      s!"{selectedAbiDir}/{contractName}.abi.json"
      s!"{reversedAbiDir}/{contractName}.abi.json"

  expectFailureContains
    "duplicate selected modules fail closed"
    (compileModulesWithOptions outDir ["Contracts.Counter.Counter", "Contracts.Counter.Counter"] false [] {} none none (some abiDir))
    "Duplicate module input: Contracts.Counter.Counter"

  let trustReport := emitTrustReportJson [trustSurfaceSpec]
  if !contains trustReport "\"contract\":\"TrustSurfaceSmoke\"" then
    throw (IO.userError "✗ trust report emits contract name")
  if !contains trustReport "\"modeledLowLevelMechanics\":[\"staticcall\",\"returndataSize\",\"returndataCopy\"]" then
    throw (IO.userError "✗ trust report emits low-level mechanics")
  if !contains trustReport "\"axiomatizedPrimitives\":[\"keccak256\"]" then
    throw (IO.userError "✗ trust report emits axiomatized primitives")
  if !contains trustReport "\"axiomatizedPrimitives\":[{\"primitive\":\"keccak256\",\"status\":\"assumed\",\"assumption\":\"keccak256_memory_slice_matches_evm\"}]" then
    throw (IO.userError "✗ trust report emits structured primitive assumptions")
  if !contains trustReport "\"proofStatus\":{\"proved\":{\"axiomatizedPrimitives\":[],\"linkedExternals\":[],\"ecmModules\":[]}" then
    throw (IO.userError "✗ trust report emits proved proof-status bucket")
  if !contains trustReport "\"assumed\":{\"axiomatizedPrimitives\":[\"keccak256\"],\"linkedExternals\":[\"PoseidonT3_hash\"],\"ecmModules\":[\"testCall\"]}" then
    throw (IO.userError "✗ trust report emits assumed proof-status bucket")
  if !contains trustReport "\"unchecked\":{\"axiomatizedPrimitives\":[],\"linkedExternals\":[],\"ecmModules\":[]}" then
    throw (IO.userError "✗ trust report emits unchecked proof-status bucket")
  if !contains trustReport "\"name\":\"PoseidonT3_hash\"" then
    throw (IO.userError "✗ trust report emits linked external name")
  if !contains trustReport "\"status\":\"assumed\"" then
    throw (IO.userError "✗ trust report emits linked external status")
  if !contains trustReport "\"axioms\":[\"poseidon_t3_deterministic\"]" then
    throw (IO.userError "✗ trust report emits linked external axioms")
  if !contains trustReport "\"module\":\"testCall\"" || !contains trustReport "\"assumption\":\"test_call_interface\"" then
    throw (IO.userError "✗ trust report emits ECM axioms")
  if !contains trustReport "\"ecmModules\":[{\"module\":\"testCall\",\"status\":\"assumed\",\"axioms\":[\"test_call_interface\"]}]" then
    throw (IO.userError "✗ trust report emits ECM module status")
  IO.println "✓ trust report emits low-level mechanics, proof-status buckets, structured primitive assumptions, and external assumptions"

  let uncheckedTrustReport := emitTrustReportJson [uncheckedTrustSurfaceSpec]
  if !contains uncheckedTrustReport "\"hasUncheckedDependencies\":true" then
    throw (IO.userError "✗ trust report flags unchecked dependencies")
  if !contains uncheckedTrustReport "\"unchecked\":{\"axiomatizedPrimitives\":[],\"linkedExternals\":[\"DebugOracle_peek\"],\"ecmModules\":[\"debugHook\"]}" then
    throw (IO.userError "✗ trust report emits unchecked proof-status bucket")
  if !contains uncheckedTrustReport "\"status\":\"unchecked\"" then
    throw (IO.userError "✗ trust report emits unchecked dependency status")
  IO.println "✓ trust report flags unchecked linked externals and ECM modules"

  let constructorOnlyEcmTrustReport := emitTrustReportJson [constructorOnlyEcmTrustSurfaceSpec]
  if !contains constructorOnlyEcmTrustReport "\"unchecked\":{\"axiomatizedPrimitives\":[],\"linkedExternals\":[],\"ecmModules\":[\"ctorHook\"]}" then
    throw (IO.userError "✗ trust report includes constructor-only ECM modules in proof-status buckets")
  if !contains constructorOnlyEcmTrustReport "\"ecmModules\":[{\"module\":\"ctorHook\",\"status\":\"unchecked\",\"axioms\":[\"ctor_hook_interface\"]}]" then
    throw (IO.userError "✗ trust report includes constructor-only ECM modules in external assumptions")
  IO.println "✓ trust report includes constructor-only ECM modules"

  let ecrecoverTrustReport := emitTrustReportJson [ecrecoverTrustSurfaceSpec]
  if !contains ecrecoverTrustReport "\"contract\":\"EcrecoverTrustSurface\"" then
    throw (IO.userError "✗ ecrecover trust report emits contract name")
  if !contains ecrecoverTrustReport "\"module\":\"ecrecover\"" ||
      !contains ecrecoverTrustReport "\"assumption\":\"evm_ecrecover_precompile\"" then
    throw (IO.userError "✗ ecrecover trust report emits precompile assumption")
  IO.println "✓ ecrecover trust report emits precompile assumption"

  let oracleTrustReport := emitTrustReportJson [oracleTrustSurfaceSpec]
  if !contains oracleTrustReport "\"contract\":\"OracleTrustSurface\"" then
    throw (IO.userError "✗ oracle trust report emits contract name")
  if !contains oracleTrustReport "\"module\":\"oracleReadUint256\"" ||
      !contains oracleTrustReport "\"assumption\":\"oracle_read_uint256_interface\"" then
    throw (IO.userError "✗ oracle trust report emits oracle module assumption")
  if !contains oracleTrustReport "\"assumed\":{\"axiomatizedPrimitives\":[],\"linkedExternals\":[],\"ecmModules\":[\"oracleReadUint256\"]}" then
    throw (IO.userError "✗ oracle trust report emits assumed ECM proof-status bucket")
  IO.println "✓ oracle trust report emits standard oracle module assumption"

  let erc20BalanceOfTrustReport := emitTrustReportJson [erc20BalanceOfTrustSurfaceSpec]
  if !contains erc20BalanceOfTrustReport "\"contract\":\"ERC20BalanceOfTrustSurface\"" then
    throw (IO.userError "✗ erc20 balanceOf trust report emits contract name")
  if !contains erc20BalanceOfTrustReport "\"module\":\"balanceOf\"" ||
      !contains erc20BalanceOfTrustReport "\"assumption\":\"erc20_balanceOf_interface\"" then
    throw (IO.userError "✗ erc20 balanceOf trust report emits module assumption")
  if !contains erc20BalanceOfTrustReport "\"assumed\":{\"axiomatizedPrimitives\":[],\"linkedExternals\":[],\"ecmModules\":[\"balanceOf\"]}" then
    throw (IO.userError "✗ erc20 balanceOf trust report emits assumed ECM proof-status bucket")
  IO.println "✓ erc20 balanceOf trust report emits standard token read module assumption"

  let erc20AllowanceTrustReport := emitTrustReportJson [erc20AllowanceTrustSurfaceSpec]
  if !contains erc20AllowanceTrustReport "\"contract\":\"ERC20AllowanceTrustSurface\"" then
    throw (IO.userError "✗ erc20 allowance trust report emits contract name")
  if !contains erc20AllowanceTrustReport "\"module\":\"allowance\"" ||
      !contains erc20AllowanceTrustReport "\"assumption\":\"erc20_allowance_interface\"" then
    throw (IO.userError "✗ erc20 allowance trust report emits module assumption")
  if !contains erc20AllowanceTrustReport "\"assumed\":{\"axiomatizedPrimitives\":[],\"linkedExternals\":[],\"ecmModules\":[\"allowance\"]}" then
    throw (IO.userError "✗ erc20 allowance trust report emits assumed ECM proof-status bucket")
  IO.println "✓ erc20 allowance trust report emits standard token read module assumption"

  let erc4626TrustReport := emitTrustReportJson [erc4626TrustSurfaceSpec]
  if !contains erc4626TrustReport "\"contract\":\"ERC4626TrustSurface\"" then
    throw (IO.userError "✗ erc4626 trust report emits contract name")
  if !contains erc4626TrustReport "\"module\":\"previewDeposit\"" ||
      !contains erc4626TrustReport "\"assumption\":\"erc4626_previewDeposit_interface\"" then
    throw (IO.userError "✗ erc4626 trust report emits previewDeposit module assumption")
  if !contains erc4626TrustReport "\"assumed\":{\"axiomatizedPrimitives\":[],\"linkedExternals\":[],\"ecmModules\":[\"previewDeposit\"]}" then
    throw (IO.userError "✗ erc4626 trust report emits assumed ECM proof-status bucket")
  IO.println "✓ erc4626 trust report emits standard vault module assumption"

  let erc4626PreviewRedeemTrustReport := emitTrustReportJson [erc4626PreviewRedeemTrustSurfaceSpec]
  if !contains erc4626PreviewRedeemTrustReport "\"contract\":\"ERC4626PreviewRedeemTrustSurface\"" then
    throw (IO.userError "✗ erc4626 previewRedeem trust report emits contract name")
  if !contains erc4626PreviewRedeemTrustReport "\"module\":\"previewRedeem\"" ||
      !contains erc4626PreviewRedeemTrustReport "\"assumption\":\"erc4626_previewRedeem_interface\"" then
    throw (IO.userError "✗ erc4626 previewRedeem trust report emits module assumption")
  if !contains erc4626PreviewRedeemTrustReport "\"assumed\":{\"axiomatizedPrimitives\":[],\"linkedExternals\":[],\"ecmModules\":[\"previewRedeem\"]}" then
    throw (IO.userError "✗ erc4626 previewRedeem trust report emits assumed ECM proof-status bucket")
  IO.println "✓ erc4626 previewRedeem trust report emits standard vault module assumption"

  compileSpecsWithOptions [abiSmokeSpec] outDir false [] {} none (some trustReportPath) none
  let writtenTrustReport ← fileExists trustReportPath
  if !writtenTrustReport then
    throw (IO.userError "✗ compileSpecsWithOptions writes trust report file")
  IO.println "✓ compileSpecsWithOptions writes trust report file"

  compileSpecsWithOptions [abiSmokeSpec] outDir false [] { patchConfig := { enabled := true } } (some patchReportPath) none none
  let writtenPatchReport ← fileExists patchReportPath
  if !writtenPatchReport then
    throw (IO.userError "✗ compileSpecsWithOptions writes patch report file")
  IO.println "✓ compileSpecsWithOptions writes patch report file"

#eval! runTests

end Compiler.CompileDriverTest
