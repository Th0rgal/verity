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
import Verity.Intent.DSL

namespace Contracts.ERC721

open Verity.Intent
open Verity.Intent.DSL
open Compiler.CompilationModel (ParamType)

/-- Intent specification for the ERC-721 contract.

    Covers three functions:
    - `approve`: unconditional — approve an address for a specific token
    - `setApprovalForAll`: conditional on approved (bool) — approve or revoke operator
    - `transferFrom`: unconditional — transfer a token between addresses

    Read-only functions (`balanceOf`, `ownerOf`, `getApproved`, `isApprovedForAll`)
    and owner-only functions (`mint`) are not covered. -/
intent_spec "ERC721" where
  intent approveIntent(approved : address, tokenId : uint256) where
    emit "Approve {approved} to transfer token #{tokenId}" [approved : address, tokenId : raw]

  intent setApprovalForAllIntent(operator : address, approved : bool) where
    if approved
    then { emit "Approve {operator} to manage all your NFTs" [operator : address] }
    else { emit "Revoke {operator} from managing your NFTs" [operator : address] }

  intent transferFromIntent(fromAddr : address, to : address, tokenId : uint256) where
    emit "Transfer token #{tokenId} from {fromAddr} to {to}" [tokenId : raw, fromAddr : address, to : address]

  bind "approve" => approveIntent
  bind "setApprovalForAll" => setApprovalForAllIntent
  bind "transferFrom" => transferFromIntent

end Contracts.ERC721
