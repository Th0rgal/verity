import Lake
open Lake DSL

package «verity» where
  version := v!"0.1.0"

require evmyul from git
  "https://github.com/NethermindEth/EVMYulLean.git"@"047f63070309f436b66c61e276ab3b6d1169265a"

@[default_target]
lean_lib «Verity» where
  globs := #[.andSubmodules `Verity]

lean_lib «Compiler» where
  globs := #[.andSubmodules `Compiler]

lean_exe «verity-compiler» where
  root := `Compiler.Main

lean_exe «difftest-interpreter» where
  root := `Compiler.Interpreter

lean_exe «random-gen» where
  root := `Compiler.RandomGen

lean_exe «gas-report» where
  root := `Compiler.Gas.Report
