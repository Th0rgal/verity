import Compiler.Main
import Compiler.Linker
import Compiler.TestModules

namespace Compiler.MainTest

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

#eval! runTests

end Compiler.MainTest
