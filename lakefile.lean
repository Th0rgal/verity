import Lake
open Lake DSL

package «verity» where
  version := v!"0.1.0"

require evmyul from git
  "https://github.com/NethermindEth/EVMYulLean.git"@"047f63070309f436b66c61e276ab3b6d1169265a"

@[default_target]
lean_lib «Verity» where
  globs := #[
    .one `Verity,
    .andSubmodules `Verity.Core,
    .andSubmodules `Verity.EVM,
    .andSubmodules `Verity.Macro,
    .andSubmodules `Verity.Stdlib,
    .andSubmodules `Verity.Specs.Common,
    .andSubmodules `Verity.Proofs.Stdlib
  ]

lean_lib «Examples» where
  globs := #[
    .one `Verity.All,
    .andSubmodules `Verity.Examples,
    .andSubmodules `Verity.Specs.Counter,
    .andSubmodules `Verity.Specs.ERC20,
    .andSubmodules `Verity.Specs.ERC721,
    .andSubmodules `Verity.Specs.Ledger,
    .andSubmodules `Verity.Specs.Owned,
    .andSubmodules `Verity.Specs.OwnedCounter,
    .andSubmodules `Verity.Specs.SafeCounter,
    .andSubmodules `Verity.Specs.SimpleStorage,
    .andSubmodules `Verity.Specs.SimpleToken,
    .andSubmodules `Verity.Proofs.Counter,
    .andSubmodules `Verity.Proofs.ERC20,
    .andSubmodules `Verity.Proofs.ERC721,
    .andSubmodules `Verity.Proofs.Ledger,
    .andSubmodules `Verity.Proofs.Owned,
    .andSubmodules `Verity.Proofs.OwnedCounter,
    .andSubmodules `Verity.Proofs.SafeCounter,
    .andSubmodules `Verity.Proofs.SimpleStorage,
    .andSubmodules `Verity.Proofs.SimpleToken
  ]

lean_lib «Compiler» where
  globs := #[.andSubmodules `Compiler]

-- Axiom dependency audit: imports all proof modules so `lake build PrintAxioms`
-- compiles them, then `lake env lean PrintAxioms.lean` can run #print axioms.
lean_lib «PrintAxioms» where
  globs := #[.one `PrintAxioms]

lean_exe «verity-compiler» where
  root := `Compiler.Main

lean_exe «difftest-interpreter» where
  root := `Compiler.Interpreter

lean_exe «random-gen» where
  root := `Compiler.RandomGen

lean_exe «gas-report» where
  root := `Compiler.Gas.Report
