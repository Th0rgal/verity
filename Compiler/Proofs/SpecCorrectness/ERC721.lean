/-
  Compiler.Proofs.SpecCorrectness.ERC721

  Initial bridge theorem surface for ERC721 scaffolding.
-/

import Verity.Specs.ERC721.Spec
import Verity.Examples.ERC721
import Verity.Proofs.ERC721.Basic

namespace Compiler.Proofs.SpecCorrectness

open Verity
open Verity.Specs.ERC721

/-- Spec/EDSL agreement for read-only `balanceOf`. -/
theorem erc721_balanceOf_spec_correct (s : ContractState) (addr : Address) :
    balanceOf_spec addr ((Verity.Examples.ERC721.balanceOf addr).runValue s) s := by
  simpa using Verity.Proofs.ERC721.balanceOf_meets_spec s addr

/-- Spec/EDSL agreement for read-only `ownerOf`. -/
theorem erc721_ownerOf_spec_correct (s : ContractState) (tokenId : Uint256) :
    ownerOf_spec tokenId ((Verity.Examples.ERC721.ownerOf tokenId).runValue s) s := by
  simpa using Verity.Proofs.ERC721.ownerOf_meets_spec s tokenId

/-- Spec/EDSL agreement for read-only `getApproved`. -/
theorem erc721_getApproved_spec_correct (s : ContractState) (tokenId : Uint256) :
    getApproved_spec tokenId ((Verity.Examples.ERC721.getApproved tokenId).runValue s) s := by
  simpa using Verity.Proofs.ERC721.getApproved_meets_spec s tokenId

/-- Spec/EDSL agreement for read-only `isApprovedForAll`. -/
theorem erc721_isApprovedForAll_spec_correct (s : ContractState) (ownerAddr operator : Address) :
    isApprovedForAll_spec ownerAddr operator
      ((Verity.Examples.ERC721.isApprovedForAll ownerAddr operator).runValue s) s := by
  simpa using Verity.Proofs.ERC721.isApprovedForAll_meets_spec s ownerAddr operator

/-- Spec/EDSL agreement for `setApprovalForAll` with sender-bound owner. -/
theorem erc721_setApprovalForAll_spec_correct (s : ContractState) (operator : Address) (approved : Bool) :
    setApprovalForAll_spec s.sender operator approved s
      ((Verity.Examples.ERC721.setApprovalForAll operator approved).runState s) := by
  simpa using Verity.Proofs.ERC721.setApprovalForAll_meets_spec s operator approved

end Compiler.Proofs.SpecCorrectness
