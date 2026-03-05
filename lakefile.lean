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
    .submodules `Verity.EVM,
    .andSubmodules `Verity.Macro,
    .submodules `Verity.Stdlib,
    .andSubmodules `Verity.Specs.Common,
    .submodules `Verity.Proofs.Stdlib
  ]

lean_lib «Examples» where
  globs := #[
    .one `Contracts,
    .andSubmodules `Contracts.MacroContracts,
    .andSubmodules `Contracts.Counter,
    .andSubmodules `Contracts.SimpleStorage,
    .one `Verity.All,
    .submodules `Verity.Examples,
    .submodules `Verity.Specs.Counter,
    .submodules `Verity.Specs.ERC20,
    .submodules `Verity.Specs.ERC721,
    .submodules `Verity.Specs.Ledger,
    .submodules `Verity.Specs.Owned,
    .submodules `Verity.Specs.OwnedCounter,
    .submodules `Verity.Specs.SafeCounter,
    .submodules `Verity.Specs.SimpleStorage,
    .submodules `Verity.Specs.SimpleToken,
    .submodules `Verity.Proofs.Counter,
    .submodules `Verity.Proofs.ERC20,
    .submodules `Verity.Proofs.ERC721,
    .submodules `Verity.Proofs.Ledger,
    .submodules `Verity.Proofs.Owned,
    .submodules `Verity.Proofs.OwnedCounter,
    .submodules `Verity.Proofs.SafeCounter,
    .submodules `Verity.Proofs.SimpleStorage,
    .submodules `Verity.Proofs.SimpleToken
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
