import Compiler.Main
import Compiler.Linker
import Compiler.Lowering.FromEDSL

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

private def expectErrorContains (label : String) (args : List String) (needle : String) : IO Unit := do
  try
    main args
    throw (IO.userError s!"✗ {label}: expected failure, command succeeded")
  catch e =>
    let msg := e.toString
    if !contains msg needle then
      throw (IO.userError s!"✗ {label}: expected '{needle}', got:\n{msg}")
    IO.println s!"✓ {label}"

private def expectErrorSatisfies
    (label : String)
    (args : List String)
    (predicate : String → Bool)
    (expectation : String) : IO Unit := do
  try
    main args
    throw (IO.userError s!"✗ {label}: expected failure, command succeeded")
  catch e =>
    let msg := e.toString
    if !predicate msg then
      throw (IO.userError s!"✗ {label}: expected {expectation}, got:\n{msg}")
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

private def contractArtifactPath (outDir : String) (contract : Compiler.Lowering.EDSLContract) : String :=
  s!"{outDir}/{contract.name}.yul"

#eval! do
  expectErrorContains "missing --link value" ["--link"] "Missing value for --link"
  expectErrorContains "missing --output value" ["--output"] "Missing value for --output"
  expectErrorContains "missing -o value" ["-o"] "Missing value for --output"
  expectErrorContains "missing --abi-output value" ["--abi-output"] "Missing value for --abi-output"
  expectErrorContains "removed --input flag is rejected" ["--input", "edsl"] "Unknown argument: --input"
  expectErrorContains "missing --edsl-contract value" ["--edsl-contract"] "Missing value for --edsl-contract"
  expectErrorContains
    "unknown --edsl-contract value"
    ["--edsl-contract", "does-not-exist"]
    "Unsupported --edsl-contract: does-not-exist"
  expectErrorSatisfies
    "unknown --edsl-contract lists supported ids deterministically"
    ["--edsl-contract", "does-not-exist"]
    (fun msg =>
      contains msg
        s!"(supported: {String.intercalate ", " Compiler.Lowering.edslContractIds})")
    "full ordered supported --edsl-contract list in diagnostic"
  expectErrorContains
    "duplicate --edsl-contract value"
    ["--edsl-contract", "counter", "--edsl-contract", "counter"]
    "Duplicate --edsl-contract value: counter"
  let nonce ← IO.monoMsNow
  let edslOutDir := s!"/tmp/verity-main-test-{nonce}-edsl-out"
  IO.FS.createDirAll edslOutDir
  main ["--output", edslOutDir]
  let allArtifactsPresent ←
    Compiler.Lowering.edslContracts.allM (fun contract => fileExists (contractArtifactPath edslOutDir contract))
  expectTrue "edsl input mode compiles every generalized EDSL artifact" allArtifactsPresent
  let singleContractOutDir := s!"/tmp/verity-main-test-{nonce}-edsl-single-contract-out"
  IO.FS.createDirAll singleContractOutDir
  main ["--edsl-contract", "counter", "--output", singleContractOutDir]
  let selectedCounterArtifact ← fileExists s!"{singleContractOutDir}/Counter.yul"
  expectTrue "edsl input mode compiles explicitly selected contract" selectedCounterArtifact
  let nonSelectedContracts :=
    Compiler.Lowering.edslContracts.filter
      (fun contract => Compiler.Lowering.edslContractId contract != "counter")
  let nonSelectedArtifactFlags ←
    nonSelectedContracts.mapM (fun contract => fileExists (contractArtifactPath singleContractOutDir contract))
  let nonSelectedArtifactsAbsent := nonSelectedArtifactFlags.all (fun isPresent => !isPresent)
  expectTrue "edsl selected-contract mode does not emit non-selected artifacts" nonSelectedArtifactsAbsent
  expectErrorContains
    "edsl input mode rejects linked-library path"
    ["--link", "examples/external-libs/PoseidonT3.yul", "--output", edslOutDir]
    "Linked external Yul libraries are not yet supported through the EDSL-only CLI path"
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
      compositionProofRef := ""
      requiredProofRefs := [] }
  expectTrue "parity pack proof composition rejects empty metadata" (!invalidPack.proofCompositionValid)
  let missingBundlePack := { invalidPack with
    compositionProofRef := "Compiler.Proofs.YulGeneration.PatchRulesProofs.foundation_patch_pack_obligations"
    requiredProofRefs := Compiler.Yul.foundationProofAllowlist
    rewriteBundleId := "missing-rewrite-bundle" }
  expectTrue "parity pack proof composition rejects unknown rewrite bundle IDs"
    (!missingBundlePack.proofCompositionValid)
  let selectedCounterContract :=
    Compiler.Lowering.edslContracts.find?
      (fun contract => Compiler.Lowering.edslContractId contract == "counter")
  expectTrue "selected EDSL contract lowers successfully through boundary"
    (match selectedCounterContract with
    | some contract =>
        match Compiler.Lowering.lowerModelPath contract with
        | .ok lowered => lowered.name == contract.name
        | .error _ => false
    | none => false)
  let edslIds := Compiler.Lowering.edslContractIds
  expectTrue "edsl-contract ids are unique"
    (edslIds.eraseDups.length == edslIds.length)
  let parserRoundtripUnique :=
    Compiler.Lowering.edslContracts.all (fun requested =>
      match Compiler.Lowering.parseEDSLContract? (Compiler.Lowering.edslContractId requested) with
      | some parsed => parsed.name == requested.name
      | none => false)
  expectTrue "edsl-contract parser roundtrip is unique" parserRoundtripUnique
  expectTrue "parsed --edsl-contract lowers through generalized helper"
    (match Compiler.Lowering.lowerRequestedEDSLContracts ["counter"] with
    | .ok [lowered] => lowered.name == "Counter"
    | .ok _ => false
    | .error _ => false)
  expectTrue "selected/default EDSL helper lowers full canonical set by default"
    (match Compiler.Lowering.lowerRequestedEDSLContracts [] with
    | .ok lowered =>
        lowered.length == Compiler.Lowering.edslContracts.length &&
        (Compiler.Lowering.edslContracts.zip lowered).all
          (fun (contract, loweredContract) => loweredContract.name == contract.name)
    | .error _ => false)
  expectTrue "selected/default EDSL helper fails closed on duplicate IDs"
    (match Compiler.Lowering.lowerRequestedEDSLContracts ["counter", "counter"] with
    | .ok _ => false
    | .error msg => contains msg "Duplicate --edsl-contract value: counter")
  expectTrue "unsupported --edsl-contract helper keeps deterministic diagnostic"
    (match Compiler.Lowering.lowerRequestedEDSLContracts ["does-not-exist"] with
    | .ok _ => false
    | .error msg => contains msg "Unsupported --edsl-contract: does-not-exist")

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

end Compiler.MainTest
