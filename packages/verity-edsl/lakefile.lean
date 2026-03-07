import Lake
open Lake DSL

package «verity-edsl» where
  version := v!"0.1.0"

require evmyul from git
  "https://github.com/NethermindEth/EVMYulLean.git"@"047f63070309f436b66c61e276ab3b6d1169265a"

lean_lib «Verity» where
  srcDir := "../.."
  globs := #[
    .one `Verity,
    .one `Verity.Macro.Syntax,
    .one `Verity.Core,
    .one `Verity.Core.Address,
    .one `Verity.Core.FiniteSet,
    .one `Verity.Core.Semantics,
    .one `Verity.Core.Uint256,
    .one `Verity.Core.Free.IRStepAttr,
    .one `Verity.Core.Free.ContractStep,
    .one `Verity.Core.Free.TypedIR,
    .one `Verity.EVM.Uint256,
    .one `Verity.Stdlib.Math,
    .one `Verity.Specs.Common,
    .one `Verity.Specs.Common.Sum,
    .one `Verity.Proofs.Stdlib.Math,
    .one `Verity.Proofs.Stdlib.ListSum
  ]
