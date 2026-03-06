import Compiler.CompileDriver
import Compiler.CompilationModel
import Compiler.ModuleInput

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

private def canonicalModules : List String :=
  [ "Contracts.MacroContracts.SimpleStorage"
  , "Contracts.MacroContracts.Counter"
  , "Contracts.MacroContracts.Owned"
  , "Contracts.MacroContracts.Ledger"
  , "Contracts.MacroContracts.OwnedCounter"
  , "Contracts.MacroContracts.SimpleToken"
  , "Contracts.MacroContracts.SafeCounter"
  , "Contracts.MacroContracts.ERC20"
  , "Contracts.MacroContracts.ERC721"
  ]

private def contractNameOfModule (moduleName : String) : String :=
  match moduleName.splitOn "." |>.reverse with
  | name :: _ => name
  | [] => moduleName

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
  let missingLib := "/tmp/definitely-missing-library.yul"
  let failingAbi := s!"{abiDir}/AbiSmoke.abi.json"

  IO.FS.createDirAll outDir
  IO.FS.createDirAll abiDir
  IO.FS.createDirAll manifestOutDir
  IO.FS.createDirAll manifestAbiDir
  IO.FS.createDirAll selectedOutDir
  IO.FS.createDirAll selectedAbiDir
  IO.FS.createDirAll reversedOutDir
  IO.FS.createDirAll reversedAbiDir

  try IO.FS.removeFile failingAbi catch _ => pure ()

  expectFailureContains
    "compileSpecsWithOptions reports missing linked library"
    (compileSpecsWithOptions [abiSmokeSpec, linkedLibrarySpec] outDir false [missingLib] {} none (some abiDir))
    missingLib

  let hasFailingAbi ← fileExists failingAbi
  if !hasFailingAbi then
    throw (IO.userError s!"✗ expected ABI artifact for early successful contract, missing: {failingAbi}")
  IO.println "✓ ABI artifacts still emitted for contracts compiled before failure"

  compileModulesWithOptions outDir canonicalModules false [] {} none (some abiDir)
  expectModuleArtifacts "explicit module list emits Yul/ABI for all requested contracts" canonicalModules outDir abiDir

  let manifestModules ←
    match ← Compiler.ModuleInput.resolveRawModules (some "packages/verity-examples/contracts.manifest") [] with
    | .ok modules => pure modules
    | .error err => throw (IO.userError err)
  compileModulesWithOptions manifestOutDir manifestModules false [] {} none (some manifestAbiDir)
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

  let selectedModules := ["Contracts.MacroContracts.SimpleStorage", "Contracts.MacroContracts.Counter"]
  compileModulesWithOptions selectedOutDir selectedModules false [] {} none (some selectedAbiDir)
  expectOnlySelectedArtifacts
    "selected module compilation emits only requested artifacts"
    selectedModules
    canonicalModules
    selectedOutDir
    selectedAbiDir

  compileModulesWithOptions reversedOutDir selectedModules.reverse false [] {} none (some reversedAbiDir)
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
    (compileModulesWithOptions outDir ["Contracts.MacroContracts.Counter", "Contracts.MacroContracts.Counter"] false [] {} none (some abiDir))
    "Duplicate --module value: Contracts.MacroContracts.Counter"

#eval! runTests

end Compiler.CompileDriverTest
