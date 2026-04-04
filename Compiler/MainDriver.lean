import Compiler.CompileDriverBase
import Compiler.ModuleInput

/-!
## Baseline CLI Argument Parsing

Supports:
- `--link <path>` : Link external Yul library (can be specified multiple times)
- `--output <dir>` or `-o <dir>` : Output directory (default: "artifacts/yul")
- `--verbose` or `-v` : Verbose output
- `--help` or `-h` : Show help message
-/

private structure CLIArgs where
  outDir : String := "artifacts/yul"
  abiOutDir : Option String := none
  manifestPath : Option String := none
  modules : List String := []
  libs : List String := []
  verbose : Bool := false
  backendProfile : Compiler.Base.BackendProfile := .semantic
  mappingSlotScratchBase : Nat := 0
  denyUncheckedDependencies : Bool := false
  denyAssumedDependencies : Bool := false
  denyAxiomatizedPrimitives : Bool := false
  denyLocalObligations : Bool := false
  denyLinearMemoryMechanics : Bool := false
  denyEventEmission : Bool := false
  denyLowLevelMechanics : Bool := false
  denyRuntimeIntrospection : Bool := false
  denyProxyUpgradeability : Bool := false
  denyLayoutIncompatibility : Bool := false
  trustReportPath : Option String := none
  assumptionReportPath : Option String := none
  layoutReportPath : Option String := none
  layoutCompatibilityReportPath : Option String := none

private def parseBackendProfile (raw : String) : Option Compiler.Base.BackendProfile :=
  match raw with
  | "semantic" => some .semantic
  | "solidity-parity-ordering" => some .solidityParityOrdering
  | _ => none

private def backendProfileString (profile : Compiler.Base.BackendProfile) : String :=
  match profile with
  | .semantic => "semantic"
  | .solidityParityOrdering => "solidity-parity-ordering"
  | .solidityParity => "solidity-parity"

private def patchedCompilerHint : String :=
  "Patch-enabled compilation moved to `verity-compiler-patched`."

private def parseArgs (args : List String) : IO CLIArgs := do
  let rec go (remaining : List String) (cfg : CLIArgs) : IO CLIArgs :=
    match remaining with
    | [] => pure { cfg with libs := cfg.libs.reverse, modules := cfg.modules.reverse }
    | "--help" :: _ | "-h" :: _ => do
        IO.println "Verity Compiler"
        IO.println ""
        IO.println "Usage: verity-compiler [options]"
        IO.println ""
        IO.println "Options:"
        IO.println "  --link <path>      Link external Yul library (can be used multiple times)"
        IO.println "  --output <dir>     Output directory (default: artifacts/yul)"
        IO.println "  -o <dir>           Short form of --output"
        IO.println "  --abi-output <dir> Output ABI JSON artifacts (one <Contract>.abi.json per spec)"
        IO.println "  --manifest <path>  Manifest file with one Lean module per line"
        IO.println "  --module <name>    Import a Lean module and compile its canonical `<Module>.spec`"
        IO.println "  --backend-profile <semantic|solidity-parity-ordering>"
        IO.println "  --trust-report <path>       Write JSON trust-surface report"
        IO.println "  --assumption-report <path>  Write JSON assumption inventory report"
        IO.println "  --layout-report <path>      Write JSON storage-layout report"
        IO.println "  --layout-compat-report <path>  Compare baseline/candidate layouts and write JSON compatibility report"
        IO.println "  --deny-unchecked-dependencies  Fail if any contract depends on `unchecked` foreign surfaces"
        IO.println "  --deny-assumed-dependencies    Fail if any contract depends on `assumed` or `unchecked` foreign surfaces"
        IO.println "  --deny-axiomatized-primitives  Fail if any contract uses axiomatized primitives"
        IO.println "  --deny-local-obligations      Fail if any contract keeps undischarged local unsafe/refinement obligations"
        IO.println "  --deny-linear-memory-mechanics  Fail if any contract uses partially modeled linear-memory mechanics"
        IO.println "  --deny-event-emission         Fail if any contract uses raw `rawLog` event emission"
        IO.println "  --deny-low-level-mechanics    Fail if any contract uses first-class low-level call / returndata mechanics"
        IO.println "  --deny-runtime-introspection   Fail if any contract uses partially modeled runtime-introspection primitives"
        IO.println "  --deny-proxy-upgradeability   Fail if any contract uses `delegatecall`-style proxy / upgradeability mechanics"
        IO.println "  --deny-layout-incompatibility Fail if the candidate layout moves or mutates baseline storage fields"
        IO.println "  --mapping-slot-scratch-base <n>  Scratch memory base for mappingSlot helper (default: 0)"
        IO.println "  --verbose          Enable verbose output"
        IO.println "  -v                 Short form of --verbose"
        IO.println "  --help             Show this help message"
        IO.println "  -h                 Short form of --help"
        IO.println ""
        IO.println patchedCompilerHint
        IO.println "Example:"
        IO.println "  verity-compiler --manifest packages/verity-examples/contracts.manifest -o artifacts/yul"
        IO.println "  verity-compiler --module Contracts.Counter.Counter -o artifacts/yul"
        throw (IO.userError "help")
    | "--link" :: path :: rest =>
        go rest { cfg with libs := path :: cfg.libs }
    | ["--link"] =>
        throw (IO.userError "Missing value for --link")
    | "--output" :: dir :: rest | "-o" :: dir :: rest =>
        go rest { cfg with outDir := dir }
    | ["--output"] | ["-o"] =>
        throw (IO.userError "Missing value for --output")
    | "--abi-output" :: dir :: rest =>
        go rest { cfg with abiOutDir := some dir }
    | ["--abi-output"] =>
        throw (IO.userError "Missing value for --abi-output")
    | "--manifest" :: path :: rest =>
        if cfg.manifestPath.isSome then
          throw (IO.userError "Cannot specify --manifest more than once")
        else
          go rest { cfg with manifestPath := some path }
    | ["--manifest"] =>
        throw (IO.userError "Missing value for --manifest")
    | "--module" :: raw :: rest =>
        go rest { cfg with modules := raw :: cfg.modules }
    | ["--module"] =>
        throw (IO.userError "Missing value for --module")
    | "--backend-profile" :: raw :: rest =>
        match raw with
        | "solidity-parity" =>
            throw (IO.userError
              s!"Backend profile `solidity-parity` requires `verity-compiler-patched`. {patchedCompilerHint}")
        | _ =>
            match parseBackendProfile raw with
            | some profile => go rest { cfg with backendProfile := profile }
            | none =>
                throw (IO.userError
                  s!"Invalid value for --backend-profile: {raw} (expected semantic or solidity-parity-ordering)")
    | ["--backend-profile"] =>
        throw (IO.userError "Missing value for --backend-profile")
    | "--enable-patches" :: _ =>
        throw (IO.userError s!"`--enable-patches` requires `verity-compiler-patched`. {patchedCompilerHint}")
    | "--patch-max-iterations" :: _ =>
        throw (IO.userError s!"`--patch-max-iterations` requires `verity-compiler-patched`. {patchedCompilerHint}")
    | "--patch-report" :: _ =>
        throw (IO.userError s!"`--patch-report` requires `verity-compiler-patched`. {patchedCompilerHint}")
    | "--parity-pack" :: _ =>
        throw (IO.userError s!"`--parity-pack` requires `verity-compiler-patched`. {patchedCompilerHint}")
    | "--trust-report" :: path :: rest =>
        go rest { cfg with trustReportPath := some path }
    | ["--trust-report"] =>
        throw (IO.userError "Missing value for --trust-report")
    | "--assumption-report" :: path :: rest =>
        go rest { cfg with assumptionReportPath := some path }
    | ["--assumption-report"] =>
        throw (IO.userError "Missing value for --assumption-report")
    | "--layout-report" :: path :: rest =>
        go rest { cfg with layoutReportPath := some path }
    | ["--layout-report"] =>
        throw (IO.userError "Missing value for --layout-report")
    | "--layout-compat-report" :: path :: rest =>
        go rest { cfg with layoutCompatibilityReportPath := some path }
    | ["--layout-compat-report"] =>
        throw (IO.userError "Missing value for --layout-compat-report")
    | "--deny-unchecked-dependencies" :: rest =>
        go rest { cfg with denyUncheckedDependencies := true }
    | "--deny-assumed-dependencies" :: rest =>
        go rest { cfg with denyAssumedDependencies := true }
    | "--deny-axiomatized-primitives" :: rest =>
        go rest { cfg with denyAxiomatizedPrimitives := true }
    | "--deny-local-obligations" :: rest =>
        go rest { cfg with denyLocalObligations := true }
    | "--deny-linear-memory-mechanics" :: rest =>
        go rest { cfg with denyLinearMemoryMechanics := true }
    | "--deny-event-emission" :: rest =>
        go rest { cfg with denyEventEmission := true }
    | "--deny-low-level-mechanics" :: rest =>
        go rest { cfg with denyLowLevelMechanics := true }
    | "--deny-runtime-introspection" :: rest =>
        go rest { cfg with denyRuntimeIntrospection := true }
    | "--deny-proxy-upgradeability" :: rest =>
        go rest { cfg with denyProxyUpgradeability := true }
    | "--deny-layout-incompatibility" :: rest =>
        go rest { cfg with denyLayoutIncompatibility := true }
    | "--mapping-slot-scratch-base" :: raw :: rest =>
        match raw.toNat? with
        | some n => go rest { cfg with mappingSlotScratchBase := n }
        | none => throw (IO.userError s!"Invalid value for --mapping-slot-scratch-base: {raw}")
    | ["--mapping-slot-scratch-base"] =>
        throw (IO.userError "Missing value for --mapping-slot-scratch-base")
    | "--verbose" :: rest | "-v" :: rest =>
        go rest { cfg with verbose := true }
    | unknown :: _ =>
        throw (IO.userError s!"Unknown argument: {unknown}\nUse --help for usage information")
  go args {}

namespace Compiler.Main

unsafe def run (args : List String) : IO Unit := do
  try
    let cfg ← parseArgs args
    let rawModules ←
      match ← Compiler.ModuleInput.resolveRawModules cfg.manifestPath cfg.modules with
      | .ok modules => pure modules
      | .error err => throw (IO.userError err)
    if rawModules.isEmpty then
      throw (IO.userError "No compiler input provided. Use --manifest and/or --module.")
    if cfg.verbose then
      IO.println s!"Output directory: {cfg.outDir}"
      IO.println "Input mode: manifest/modules"
      match cfg.manifestPath with
      | some path => IO.println s!"Manifest: {path}"
      | none => pure ()
      if !rawModules.isEmpty then
        IO.println s!"Modules: {String.intercalate ", " rawModules}"
      IO.println s!"Backend profile: {backendProfileString cfg.backendProfile}"
      match cfg.abiOutDir with
      | some dir => IO.println s!"ABI output directory: {dir}"
      | none => pure ()
      match cfg.trustReportPath with
      | some path => IO.println s!"Trust report: {path}"
      | none => pure ()
      match cfg.assumptionReportPath with
      | some path => IO.println s!"Assumption report: {path}"
      | none => pure ()
      match cfg.layoutReportPath with
      | some path => IO.println s!"Layout report: {path}"
      | none => pure ()
      match cfg.layoutCompatibilityReportPath with
      | some path => IO.println s!"Layout compatibility report: {path}"
      | none => pure ()
      IO.println s!"Mapping slot scratch base: {cfg.mappingSlotScratchBase}"
      IO.println ""
    let options : Compiler.Base.YulEmitOptions := {
      backendProfile := cfg.backendProfile
      mappingSlotScratchBase := cfg.mappingSlotScratchBase
    }
    Compiler.Base.compileModulesWithOptions
      cfg.outDir rawModules cfg.verbose cfg.libs options none cfg.trustReportPath
      cfg.assumptionReportPath cfg.abiOutDir cfg.denyUncheckedDependencies cfg.denyAssumedDependencies
      cfg.denyAxiomatizedPrimitives cfg.denyLocalObligations cfg.denyLinearMemoryMechanics cfg.denyEventEmission
      cfg.denyLowLevelMechanics cfg.denyRuntimeIntrospection cfg.denyProxyUpgradeability cfg.layoutReportPath
      cfg.layoutCompatibilityReportPath cfg.denyLayoutIncompatibility
  catch e =>
    if e.toString == "help" then
      return ()
    else
      throw e

end Compiler.Main
