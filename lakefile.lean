import Lake
open Lake DSL

package «verity» where
  version := v!"0.1.0"

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
