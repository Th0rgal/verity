import Lake
open Lake DSL

package «verity-compiler» where
  version := v!"0.1.0"

require «verity-edsl» from "../verity-edsl"

lean_lib «Compiler» where
  srcDir := "../.."
  globs := #[]

lean_exe «verity-compiler» where
  srcDir := "../.."
  root := `Compiler.Main
