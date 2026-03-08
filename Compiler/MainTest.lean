import Contracts
import Contracts.RawLogTrustSurface
import Compiler.Main
import Compiler.Linker
import Compiler.TestModules

namespace Compiler.MainTest

private def contains (haystack needle : String) : Bool :=
  if needle.isEmpty then true else (haystack.splitOn needle).length > 1

private unsafe def expectErrorContains (label : String) (args : List String) (needle : String) : IO Unit := do
  try
    main args
    throw (IO.userError s!"✗ {label}: expected failure, command succeeded")
  catch e =>
    let msg := e.toString
    if !contains msg needle then
      throw (IO.userError s!"✗ {label}: expected '{needle}', got:\n{msg}")
    IO.println s!"✓ {label}"

private def expectTrue (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"✗ {label}")
  IO.println s!"✓ {label}"

private def fileExists (path : String) : IO Bool := do
  try
    let _ ← IO.FS.readFile path
    pure true
  catch _ =>
    pure false

private def moduleArgs (modules : List String) : List String :=
  modules.foldr (fun moduleName acc => "--module" :: moduleName :: acc) []

private def contractArtifactPath (outDir : String) (moduleName : String) : String :=
  s!"{outDir}/{contractNameOfModule moduleName}.yul"

unsafe def runTests : IO Unit := do
  expectErrorContains "missing --link value" ["--link"] "Missing value for --link"
  expectErrorContains "missing --output value" ["--output"] "Missing value for --output"
  expectErrorContains "missing -o value" ["-o"] "Missing value for --output"
  expectErrorContains "missing --abi-output value" ["--abi-output"] "Missing value for --abi-output"
  expectErrorContains "removed --input flag is rejected" ["--input", "edsl"] "Unknown argument: --input"
  expectErrorContains "missing --manifest value" ["--manifest"] "Missing value for --manifest"
  expectErrorContains "missing --module value" ["--module"] "Missing value for --module"
  expectErrorContains
    "duplicate --module value"
    (["--module", "Contracts.Counter.Counter", "--module", "Contracts.Counter.Counter"] ++ ["--output", "/tmp/verity-main-test-dup"])
    "Duplicate module input: Contracts.Counter.Counter"
  expectErrorContains
    "empty compiler input is rejected"
    ["--output", "/tmp/verity-main-test-empty"]
    "No compiler input provided. Use --manifest and/or --module."
  expectErrorContains
    "invalid module name is rejected"
    ["--module", "Contracts..Counter", "--output", "/tmp/verity-main-test-invalid"]
    "Invalid module name: Contracts..Counter"
  expectErrorContains
    "missing manifest file is rejected"
    ["--manifest", "/tmp/definitely-missing-verty-manifest", "--output", "/tmp/verity-main-test-missing-manifest"]
    "Failed to read manifest"

  let nonce ← IO.monoMsNow
  let allOutDir := s!"/tmp/verity-main-test-{nonce}-all-out"
  IO.FS.createDirAll allOutDir
  main (moduleArgs canonicalModules ++ ["--output", allOutDir])
  let allArtifactsPresent ←
    canonicalModules.allM (fun moduleName => fileExists (contractArtifactPath allOutDir moduleName))
  expectTrue "module input mode compiles every requested artifact" allArtifactsPresent

  let singleOutDir := s!"/tmp/verity-main-test-{nonce}-single-out"
  IO.FS.createDirAll singleOutDir
  main (["--module", "Contracts.Counter.Counter", "--output", singleOutDir])
  let selectedCounterArtifact ← fileExists s!"{singleOutDir}/Counter.yul"
  expectTrue "module input mode compiles explicitly selected contract" selectedCounterArtifact
  let strictOutDir := s!"/tmp/verity-main-test-{nonce}-strict-out"
  IO.FS.createDirAll strictOutDir
  main (["--module", "Contracts.Counter.Counter", "--deny-unchecked-dependencies", "--output", strictOutDir])
  let strictCounterArtifact ← fileExists s!"{strictOutDir}/Counter.yul"
  expectTrue "strict unchecked-dependency gate accepts proved local modules" strictCounterArtifact
  let proofStrictOutDir := s!"/tmp/verity-main-test-{nonce}-proof-strict-out"
  IO.FS.createDirAll proofStrictOutDir
  main (["--module", "Contracts.Counter.Counter", "--deny-assumed-dependencies", "--output", proofStrictOutDir])
  let proofStrictCounterArtifact ← fileExists s!"{proofStrictOutDir}/Counter.yul"
  expectTrue "strict assumed-dependency gate accepts proved local modules" proofStrictCounterArtifact
  let primitiveStrictOutDir := s!"/tmp/verity-main-test-{nonce}-primitive-strict-out"
  IO.FS.createDirAll primitiveStrictOutDir
  main (["--module", "Contracts.SimpleStorage.SimpleStorage", "--deny-axiomatized-primitives", "--output", primitiveStrictOutDir])
  let primitiveStrictArtifact ← fileExists s!"{primitiveStrictOutDir}/SimpleStorage.yul"
  expectTrue "strict axiomatized-primitive gate accepts contracts without axiomatized primitives" primitiveStrictArtifact
  expectErrorContains
    "strict axiomatized-primitive gate rejects axiomatized primitives"
    ["--module", "Contracts.Counter.Counter", "--deny-axiomatized-primitives", "--output", s!"/tmp/verity-main-test-{nonce}-primitive-fail-out"]
    "Counter [function:previewEnvOps]: keccak256"
  let memoryStrictOutDir := s!"/tmp/verity-main-test-{nonce}-memory-strict-out"
  IO.FS.createDirAll memoryStrictOutDir
  main (["--module", "Contracts.SimpleStorage.SimpleStorage", "--deny-linear-memory-mechanics", "--output", memoryStrictOutDir])
  let memoryStrictArtifact ← fileExists s!"{memoryStrictOutDir}/SimpleStorage.yul"
  expectTrue "strict linear-memory gate accepts contracts without partially modeled memory mechanics" memoryStrictArtifact
  expectErrorContains
    "strict linear-memory gate rejects partially modeled memory mechanics"
    ["--module", "Contracts.Counter.Counter", "--deny-linear-memory-mechanics", "--output", s!"/tmp/verity-main-test-{nonce}-memory-fail-out"]
    "Counter [function:previewEnvOps]: mload"
  let eventStrictOutDir := s!"/tmp/verity-main-test-{nonce}-event-strict-out"
  IO.FS.createDirAll eventStrictOutDir
  main (["--module", "Contracts.SimpleStorage.SimpleStorage", "--deny-event-emission", "--output", eventStrictOutDir])
  let eventStrictArtifact ← fileExists s!"{eventStrictOutDir}/SimpleStorage.yul"
  expectTrue "strict event-emission gate accepts contracts without raw event emission" eventStrictArtifact
  expectErrorContains
    "strict event-emission gate rejects raw event emission"
    ["--module", "Contracts.RawLogTrustSurface", "--deny-event-emission", "--output", s!"/tmp/verity-main-test-{nonce}-event-fail-out"]
    "RawLogTrustSurface [function:emitTrace]: rawLog"
  let lowLevelStrictOutDir := s!"/tmp/verity-main-test-{nonce}-low-level-strict-out"
  IO.FS.createDirAll lowLevelStrictOutDir
  main (["--module", "Contracts.SimpleStorage.SimpleStorage", "--deny-low-level-mechanics", "--output", lowLevelStrictOutDir])
  let lowLevelStrictArtifact ← fileExists s!"{lowLevelStrictOutDir}/SimpleStorage.yul"
  expectTrue "strict low-level gate accepts contracts without low-level mechanics" lowLevelStrictArtifact
  expectErrorContains
    "strict low-level gate rejects low-level mechanics"
    ["--module", "Contracts.Counter.Counter", "--deny-low-level-mechanics", "--output", s!"/tmp/verity-main-test-{nonce}-low-level-fail-out"]
    "Counter [function:previewLowLevel]: call, staticcall, delegatecall, revertReturndata, returndataCopy, returndataSize"
  let runtimeStrictOutDir := s!"/tmp/verity-main-test-{nonce}-runtime-strict-out"
  IO.FS.createDirAll runtimeStrictOutDir
  main (["--module", "Contracts.SimpleStorage.SimpleStorage", "--deny-runtime-introspection", "--output", runtimeStrictOutDir])
  let runtimeStrictArtifact ← fileExists s!"{runtimeStrictOutDir}/SimpleStorage.yul"
  expectTrue "strict runtime-introspection gate accepts contracts without partially modeled runtime introspection" runtimeStrictArtifact
  expectErrorContains
    "strict runtime-introspection gate rejects partially modeled runtime introspection"
    ["--module", "Contracts.Counter.Counter", "--deny-runtime-introspection", "--output", s!"/tmp/verity-main-test-{nonce}-runtime-fail-out"]
    "Counter [function:previewEnvOps]: blockNumber, contractAddress, chainid"
  let proxyStrictOutDir := s!"/tmp/verity-main-test-{nonce}-proxy-strict-out"
  IO.FS.createDirAll proxyStrictOutDir
  main (["--module", "Contracts.SimpleStorage.SimpleStorage", "--deny-proxy-upgradeability", "--output", proxyStrictOutDir])
  let proxyStrictArtifact ← fileExists s!"{proxyStrictOutDir}/SimpleStorage.yul"
  expectTrue "strict proxy-upgradeability gate accepts contracts without delegatecall" proxyStrictArtifact
  expectErrorContains
    "strict proxy-upgradeability gate rejects delegatecall mechanics"
    ["--module", "Contracts.Counter.Counter", "--deny-proxy-upgradeability", "--output", s!"/tmp/verity-main-test-{nonce}-proxy-fail-out"]
    "Counter [function:previewLowLevel]: delegatecall"
  let nonSelectedArtifactFlags ←
    (canonicalModules.filter (· != "Contracts.Counter.Counter")).mapM
      (fun moduleName => fileExists (contractArtifactPath singleOutDir moduleName))
  let nonSelectedArtifactsAbsent := nonSelectedArtifactFlags.all (fun isPresent => !isPresent)
  expectTrue "selected module mode does not emit non-selected artifacts" nonSelectedArtifactsAbsent

  let manifestOutDir := s!"/tmp/verity-main-test-{nonce}-manifest-out"
  IO.FS.createDirAll manifestOutDir
  main ["--manifest", "packages/verity-examples/contracts.manifest", "--output", manifestOutDir]
  let manifestArtifactsPresent ←
    canonicalModules.allM (fun moduleName => fileExists (contractArtifactPath manifestOutDir moduleName))
  expectTrue "manifest input mode compiles every requested artifact" manifestArtifactsPresent

  expectErrorContains "missing --patch-report value" ["--patch-report"] "Missing value for --patch-report"
  expectErrorContains "missing --patch-max-iterations value" ["--patch-max-iterations"] "Missing value for --patch-max-iterations"
  expectErrorContains "missing --backend-profile value" ["--backend-profile"] "Missing value for --backend-profile"
  expectErrorContains "invalid --backend-profile value" ["--backend-profile", "invalid-profile"] "Invalid value for --backend-profile: invalid-profile"
  expectErrorContains "missing --parity-pack value" ["--parity-pack"] "Missing value for --parity-pack"
  expectErrorContains "invalid --parity-pack value" ["--parity-pack", "invalid-pack"] "Invalid value for --parity-pack: invalid-pack"
  expectErrorContains "reject duplicate --parity-pack" ["--parity-pack", "solc-0.8.33-o200-viair-false-evm-shanghai", "--parity-pack", "solc-0.8.28-o999999-viair-true-evm-paris"] "Cannot specify --parity-pack more than once"
  expectErrorContains "reject backend-profile + parity-pack conflict (profile first)" ["--backend-profile", "semantic", "--parity-pack", "solc-0.8.33-o200-viair-false-evm-shanghai"] "Cannot combine --parity-pack with --backend-profile"
  expectErrorContains "reject backend-profile + parity-pack conflict (pack first)" ["--parity-pack", "solc-0.8.33-o200-viair-false-evm-shanghai", "--backend-profile", "semantic"] "Cannot combine --backend-profile with --parity-pack"
  expectErrorContains "missing --mapping-slot-scratch-base value" ["--mapping-slot-scratch-base"] "Missing value for --mapping-slot-scratch-base"
  expectErrorContains "invalid --mapping-slot-scratch-base value" ["--mapping-slot-scratch-base", "not-a-number"] "Invalid value for --mapping-slot-scratch-base: not-a-number"
  expectErrorContains "removed --ast flag is rejected" ["--ast"] "Unknown argument: --ast"
  expectErrorContains "unknown argument still reported" ["--definitely-unknown-flag"] "Unknown argument: --definitely-unknown-flag"
  expectTrue "shipped parity packs have proof composition metadata"
    Compiler.allParityPacksProofCompositionValid
  let invalidPack : Compiler.ParityPack :=
    { id := "invalid-proof-pack"
      compat := {
        solcVersion := "0.8.28"
        solcCommit := "7893614a"
        optimizerRuns := 200
        viaIR := false
        evmVersion := "shanghai"
        metadataMode := "default"
      }
      backendProfile := .solidityParity
      forcePatches := true
      defaultPatchMaxIterations := 2
      rewriteBundleId := Compiler.Yul.solcCompatRewriteBundleId
      compositionProofRef := .anonymous
      requiredProofRefs := [] }
  expectTrue "parity pack proof composition rejects empty metadata" (!invalidPack.proofCompositionValid)
  let missingBundlePack := { invalidPack with
    compositionProofRef := Compiler.Yul.proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_patch_pack_obligations"
    requiredProofRefs := Compiler.Yul.foundationProofAllowlist
    rewriteBundleId := "missing-rewrite-bundle" }
  expectTrue "parity pack proof composition rejects unknown rewrite bundle IDs"
    (!missingBundlePack.proofCompositionValid)

  let libWithCommentAndStringBraces :=
    "{\n" ++
    "function PoseidonT3_hash(a, b) -> result {\n" ++
    "  // } stray brace in comment\n" ++
    "  result := add(a, b)\n" ++
    "}\n\n" ++
    "function PoseidonT4_hash(a, b, c) -> result {\n" ++
    "  let marker := \"} in string\"\n" ++
    "  result := add(add(a, b), c)\n" ++
    "}\n" ++
    "}\n"

  let parsed := Compiler.Linker.parseLibrary libWithCommentAndStringBraces
  expectTrue "linker parses two functions when braces appear in comments/strings" (parsed.length == 2)
  expectTrue "linker keeps first function boundary intact" ((parsed.getD 0 {name := "", arity := 0, body := []}).name == "PoseidonT3_hash")
  expectTrue "linker keeps second function boundary intact" ((parsed.getD 1 {name := "", arity := 0, body := []}).name == "PoseidonT4_hash")
  let firstBody := String.intercalate "\n" ((parsed.getD 0 {name := "", arity := 0, body := []}).body)
  expectTrue "first function body does not swallow next function" (!contains firstBody "function PoseidonT4_hash")

set_option maxRecDepth 100000 in
#eval! runTests

end Compiler.MainTest
