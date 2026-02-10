import Lake
open Lake DSL

package «dumb-contracts» where
  version := v!"0.1.0"

lean_lib «DumbContracts» where
  srcDir := "edsl"
  globs := #[.andSubmodules `DumbContracts]

@[default_target]
lean_lib «DumbContractsExamples» where
  srcDir := "examples/lean"
  globs := #[.andSubmodules `DumbContracts]
