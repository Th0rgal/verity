import Compiler.CompileDriver
import Compiler.ASTDriver

/-!
## CLI Argument Parsing

Supports:
- `--link <path>` : Link external Yul library (can be specified multiple times)
- `--output <dir>` or `-o <dir>` : Output directory (default: "compiler/yul")
- `--ast` : Use unified AST compilation path (issue #364)
- `--verbose` or `-v` : Verbose output
- `--help` or `-h` : Show help message
-/

private structure CLIArgs where
  outDir : String := "compiler/yul"
  libs : List String := []
  verbose : Bool := false
  useAST : Bool := false
  patchEnabled : Bool := false
  patchMaxIterations : Nat := 2
  patchReportPath : Option String := none

private def parseArgs (args : List String) : IO CLIArgs := do
  let rec go (remaining : List String) (cfg : CLIArgs) : IO CLIArgs :=
    match remaining with
    | [] => pure { cfg with libs := cfg.libs.reverse }
    | "--help" :: _ | "-h" :: _ => do
        IO.println "Verity Compiler"
        IO.println ""
        IO.println "Usage: verity-compiler [options]"
        IO.println ""
        IO.println "Options:"
        IO.println "  --link <path>      Link external Yul library (can be used multiple times)"
        IO.println "  --output <dir>     Output directory (default: compiler/yul)"
        IO.println "  -o <dir>           Short form of --output"
        IO.println "  --ast              Use unified AST compilation path (#364)"
        IO.println "  --enable-patches   Enable deterministic Yul patch pass"
        IO.println "  --patch-max-iterations <n>  Max patch-pass fixpoint iterations (default: 2)"
        IO.println "  --patch-report <path>       Write TSV patch coverage report"
        IO.println "  --verbose          Enable verbose output"
        IO.println "  -v                 Short form of --verbose"
        IO.println "  --help             Show this help message"
        IO.println "  -h                 Short form of --help"
        IO.println ""
        IO.println "Example:"
        IO.println "  verity-compiler --link examples/external-libs/PoseidonT3.yul -o compiler/yul"
        IO.println "  verity-compiler --ast -v  # compile using unified AST path"
        IO.println "  verity-compiler --enable-patches --patch-report compiler/patch-report.tsv"
        throw (IO.userError "help")
    | "--link" :: path :: rest =>
        go rest { cfg with libs := path :: cfg.libs }
    | "--output" :: dir :: rest | "-o" :: dir :: rest =>
        go rest { cfg with outDir := dir }
    | "--ast" :: rest =>
        go rest { cfg with useAST := true }
    | "--enable-patches" :: rest =>
        go rest { cfg with patchEnabled := true }
    | "--patch-max-iterations" :: raw :: rest =>
        match raw.toNat? with
        | some n => go rest { cfg with patchEnabled := true, patchMaxIterations := n }
        | none => throw (IO.userError s!"Invalid value for --patch-max-iterations: {raw}")
    | "--patch-report" :: path :: rest =>
        go rest { cfg with patchEnabled := true, patchReportPath := some path }
    | "--verbose" :: rest | "-v" :: rest =>
        go rest { cfg with verbose := true }
    | unknown :: _ =>
        throw (IO.userError s!"Unknown argument: {unknown}\nUse --help for usage information")
  go args {}

def main (args : List String) : IO Unit := do
  try
    let cfg ← parseArgs args
    if cfg.verbose then
      IO.println s!"Output directory: {cfg.outDir}"
      if cfg.useAST then
        IO.println "Mode: unified AST compilation"
      if cfg.patchEnabled then
        IO.println s!"Patch pass: enabled (max iterations = {cfg.patchMaxIterations})"
      if !cfg.libs.isEmpty then
        IO.println s!"External libraries: {cfg.libs.length}"
        for lib in cfg.libs do
          IO.println s!"  - {lib}"
      match cfg.patchReportPath with
      | some path => IO.println s!"Patch report: {path}"
      | none => pure ()
      IO.println ""
    let options : Compiler.YulEmitOptions := {
      patchConfig := {
        enabled := cfg.patchEnabled
        maxIterations := cfg.patchMaxIterations
      }
    }
    if cfg.useAST then
      Compiler.ASTDriver.compileAllASTWithOptions cfg.outDir cfg.verbose cfg.libs options cfg.patchReportPath
    else
      compileAllWithOptions cfg.outDir cfg.verbose cfg.libs options cfg.patchReportPath
  catch e =>
    if e.toString == "help" then
      -- Help was shown, exit cleanly
      return ()
    else
      throw e
