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

lean_lib «Contracts» where
  globs := #[
    .one `Contracts,
    .one `Contracts.Common,
    .one `Contracts.Specs,
    .one `Contracts.Interpreter,
    .one `Contracts.MacroTranslateInvariantTest,
    .one `Contracts.MacroTranslateRoundTripFuzz,
    .one `Contracts.Smoke,
    .andSubmodules `Contracts.Counter,
    .andSubmodules `Contracts.SimpleStorage,
    .andSubmodules `Contracts.Owned,
    .andSubmodules `Contracts.OwnedCounter,
    .andSubmodules `Contracts.SafeCounter,
    .andSubmodules `Contracts.Ledger,
    .andSubmodules `Contracts.Vault,
    .andSubmodules `Contracts.ERC20,
    .andSubmodules `Contracts.ERC721,
    .andSubmodules `Contracts.SimpleToken,
    .andSubmodules `Contracts.CryptoHash,
    .andSubmodules `Contracts.ReentrancyExample
  ]

lean_lib «Compiler» where
  globs := #[.andSubmodules `Compiler]

-- Axiom dependency audit: imports all proof modules so `lake build PrintAxioms`
-- compiles them, then `lake env lean PrintAxioms.lean` can run #print axioms.
lean_lib «PrintAxioms» where
  globs := #[.one `PrintAxioms]

lean_exe «verity-compiler» where
  root := `Compiler.Main

lean_exe «verity-compiler-patched» where
  root := `Compiler.MainPatched

lean_exe «difftest-interpreter» where
  root := `Contracts.Interpreter

lean_exe «random-gen» where
  root := `Compiler.RandomGen

lean_exe «gas-report» where
  root := `Compiler.Gas.Report

lean_exe «macro-roundtrip-fuzz» where
  root := `Contracts.MacroTranslateRoundTripFuzz

lean_exe «compiler-main-test» where
  root := `Compiler.MainTestRunner
