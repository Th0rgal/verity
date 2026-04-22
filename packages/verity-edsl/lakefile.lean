import Lake
open Lake DSL

package «verity-edsl» where
  version := v!"1.0.0"

require evmyul from git
  "https://github.com/lfglabs-dev/EVMYulLean.git"@"7b54b8f38bb68ee930d00d39c1b11dd60fb123c8"

lean_lib «Verity» where
  srcDir := "../.."
  globs := #[
    .one `Verity,
    .one `Verity.Macro.Syntax,
    .one `Verity.Core,
    .one `Verity.Core.Address,
    .one `Verity.Core.FiniteSet,
    .one `Verity.Core.Int256,
    .one `Verity.Core.Semantics,
    .one `Verity.Core.Uint256,
    .one `Verity.Core.Free.IRStepAttr,
    .one `Verity.Core.Free.ContractStep,
    .one `Verity.Core.Free.TypedIR,
    .one `Verity.EVM.Int256,
    .one `Verity.EVM.Uint256,
    .one `Verity.Stdlib.Math,
    .one `Verity.Specs.Common,
    .one `Verity.Specs.Common.Sum,
    .one `Verity.Proofs.Stdlib.Math,
    .one `Verity.Proofs.Stdlib.ListSum
  ]
