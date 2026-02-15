import Compiler.CompileDriver

/-!
## CLI Argument Parsing

Supports:
- `--link <path>` : Link external Yul library (can be specified multiple times)
- `--output <dir>` or `-o <dir>` : Output directory (default: "compiler/yul")
- `--verbose` or `-v` : Verbose output
- `--help` or `-h` : Show help message
-/

private def parseArgs (args : List String) : IO (String × List String × Bool) := do
  let rec go (remaining : List String) (outDir : String) (libs : List String) (verbose : Bool) : IO (String × List String × Bool) :=
    match remaining with
    | [] => pure (outDir, libs.reverse, verbose)
    | "--help" :: _ | "-h" :: _ => do
        IO.println "Verity Compiler"
        IO.println ""
        IO.println "Usage: verity-compiler [options]"
        IO.println ""
        IO.println "Options:"
        IO.println "  --link <path>      Link external Yul library (can be used multiple times)"
        IO.println "  --output <dir>     Output directory (default: compiler/yul)"
        IO.println "  -o <dir>           Short form of --output"
        IO.println "  --verbose          Enable verbose output"
        IO.println "  -v                 Short form of --verbose"
        IO.println "  --help             Show this help message"
        IO.println "  -h                 Short form of --help"
        IO.println ""
        IO.println "Example:"
        IO.println "  verity-compiler --link libs/Poseidon.yul --link libs/Groth16.yul -o out/"
        throw (IO.userError "help")
    | "--link" :: path :: rest =>
        go rest outDir (path :: libs) verbose
    | "--output" :: dir :: rest | "-o" :: dir :: rest =>
        go rest dir libs verbose
    | "--verbose" :: rest | "-v" :: rest =>
        go rest outDir libs true
    | unknown :: _ =>
        throw (IO.userError s!"Unknown argument: {unknown}\nUse --help for usage information")
  go args "compiler/yul" [] false

def main (args : List String) : IO Unit := do
  try
    let (outDir, libs, verbose) ← parseArgs args
    if verbose then
      IO.println s!"Output directory: {outDir}"
      if !libs.isEmpty then
        IO.println s!"External libraries: {libs.length}"
        for lib in libs do
          IO.println s!"  - {lib}"
      IO.println ""
    compileAll outDir verbose libs
  catch e =>
    if e.toString == "help" then
      -- Help was shown, exit cleanly
      return ()
    else
      throw e
