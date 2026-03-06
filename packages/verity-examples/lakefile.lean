import Lake
open Lake DSL

package «verity-examples» where
  version := v!"0.1.0"

require «verity-edsl» from "../verity-edsl"
require «verity-compiler» from "../verity-compiler"

lean_lib «Contracts» where
  srcDir := "../.."
  globs := #[
    .one `Contracts,
    .andSubmodules `Contracts.MacroContracts,
    .andSubmodules `Contracts.Counter,
    .andSubmodules `Contracts.SimpleStorage,
    .andSubmodules `Contracts.Owned,
    .andSubmodules `Contracts.OwnedCounter,
    .andSubmodules `Contracts.SafeCounter,
    .andSubmodules `Contracts.Ledger,
    .andSubmodules `Contracts.ERC20,
    .andSubmodules `Contracts.ERC721,
    .andSubmodules `Contracts.SimpleToken,
    .andSubmodules `Contracts.CryptoHash,
    .andSubmodules `Contracts.ReentrancyExample
  ]
