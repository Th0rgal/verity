import Lake
open Lake DSL

package «dumb-contracts» where
  version := v!"0.1.0"

@[default_target]
lean_lib «DumbContracts» where
  globs := #[.andSubmodules `DumbContracts]

lean_lib «Compiler» where
  globs := #[.andSubmodules `Compiler]

lean_exe «dumbcontracts-compiler» where
  root := `Compiler.Main
