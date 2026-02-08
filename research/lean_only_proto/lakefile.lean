import Lake
open Lake DSL

package dumbcontracts where
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]

lean_lib DumbContracts

lean_exe dumbcontracts where
  root := `Main
