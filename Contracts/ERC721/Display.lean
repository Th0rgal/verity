/-
  Contracts.ERC721.Display: Intent specification for the ERC-721 contract.

  Defines `Contracts.ERC721.intentSpec` — the provable intent DSL mapping
  for the ERC-721 contract's user-facing state-changing functions:
    - approve(approved, tokenId)
    - setApprovalForAll(operator, approved)
    - transferFrom(fromAddr, to, tokenId)

  This constant is auto-discovered by the compiler when `--circom-output`
  or `--erc7730-output` is passed, enabling circuit and clear-signing
  JSON generation for each binding.

  See `Contracts/ERC20/Display.lean` for the ERC-20 version.
-/
import Verity.Intent.Types

namespace Contracts.ERC721

open Verity.Intent
open Compiler.CompilationModel (ParamType)

/-- Intent specification for the ERC-721 contract.

    Covers three functions:
    - `approve`: unconditional — approve an address for a specific token
    - `setApprovalForAll`: conditional on approved (bool) — approve or revoke operator
    - `transferFrom`: unconditional — transfer a token between addresses

    Read-only functions (`balanceOf`, `ownerOf`, `getApproved`, `isApprovedForAll`)
    and owner-only functions (`mint`) are not covered. -/
def intentSpec : IntentSpec := {
  contractName := "ERC721"

  fns := [
    -- Intent: approve(approved: address, tokenId: uint256)
    -- Unconditional — always shows the approved address and token ID
    { name := "approveIntent"
      params := [("approved", .address), ("tokenId", .uint256)]
      returnKind := .void
      body := [
        .emit { text := "Approve {approved} to transfer token #{tokenId}",
                holes := [{ param := "approved", format := .address },
                          { param := "tokenId", format := .raw }] }
      ]
    },

    -- Intent: setApprovalForAll(operator: address, approved: bool)
    -- Conditional on the bool parameter
    { name := "setApprovalForAllIntent"
      params := [("operator", .address), ("approved", .bool)]
      returnKind := .void
      body := [
        .ite (.param "approved")
          [.emit { text := "Approve {operator} to manage all your NFTs",
                   holes := [{ param := "operator", format := .address }] }]
          [.emit { text := "Revoke {operator} from managing your NFTs",
                   holes := [{ param := "operator", format := .address }] }]
      ]
    },

    -- Intent: transferFrom(fromAddr: address, to: address, tokenId: uint256)
    -- Unconditional — always shows from, to, and token ID
    { name := "transferFromIntent"
      params := [("fromAddr", .address), ("to", .address), ("tokenId", .uint256)]
      returnKind := .void
      body := [
        .emit { text := "Transfer token #{tokenId} from {fromAddr} to {to}",
                holes := [{ param := "tokenId", format := .raw },
                          { param := "fromAddr", format := .address },
                          { param := "to", format := .address }] }
      ]
    }
  ]

  bindings := [
    { functionName := "approve",           intentFn := "approveIntent" },
    { functionName := "setApprovalForAll", intentFn := "setApprovalForAllIntent" },
    { functionName := "transferFrom",      intentFn := "transferFromIntent" }
  ]
}

end Contracts.ERC721
