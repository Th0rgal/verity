import Lake
open Lake DSL

package «dumb-contracts» where
  version := v!"0.1.0"

lean_lib «DumbContracts» where
  srcDir := "edsl"
  globs := #[.andSubmodules `DumbContracts]

lean_lib «Compiler» where
  srcDir := "edsl"
  globs := #[.andSubmodules `Compiler]

lean_exe «dumbcontracts-compiler» where
  root := `Compiler.Main
  srcDir := "edsl"

@[default_target]
lean_lib «DumbContractsExamples» where
  srcDir := "examples/lean"
  globs := #[
    .submodules `DumbContracts.Examples,
    .submodules `DumbContracts.Proofs,
    .submodules `DumbContracts.Specs
  ]
