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
  intent approve(approved : address, tokenId : uint256) where
    emit "Approve {approved:address} to transfer token #{tokenId:raw}"

  intent setApprovalForAll(operator : address, approved : bool) where
    when approved =>
      emit "Approve {operator:address} to manage all your NFTs"
    otherwise =>
      emit "Revoke {operator:address} from managing your NFTs"

  intent transferFrom(fromAddr : address, to : address, tokenId : uint256) where
    emit "Transfer token #{tokenId:raw} from {fromAddr:address} to {to:address}"

end Contracts.ERC721
