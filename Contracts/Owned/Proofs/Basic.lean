import Verity.Proofs.Owned.Basic

namespace Contracts.Owned.Proofs.Basic

abbrev setStorageAddr_updates_owner := Verity.Proofs.Owned.setStorageAddr_updates_owner
abbrev getStorageAddr_reads_owner := Verity.Proofs.Owned.getStorageAddr_reads_owner
abbrev setStorageAddr_preserves_other_slots := Verity.Proofs.Owned.setStorageAddr_preserves_other_slots
abbrev setStorageAddr_preserves_uint_storage := Verity.Proofs.Owned.setStorageAddr_preserves_uint_storage
abbrev setStorageAddr_preserves_map_storage := Verity.Proofs.Owned.setStorageAddr_preserves_map_storage
abbrev setStorageAddr_preserves_context := Verity.Proofs.Owned.setStorageAddr_preserves_context
abbrev constructor_meets_spec := Verity.Proofs.Owned.constructor_meets_spec
abbrev constructor_sets_owner := Verity.Proofs.Owned.constructor_sets_owner
abbrev getOwner_meets_spec := Verity.Proofs.Owned.getOwner_meets_spec
abbrev getOwner_returns_owner := Verity.Proofs.Owned.getOwner_returns_owner
abbrev getOwner_preserves_state := Verity.Proofs.Owned.getOwner_preserves_state
abbrev isOwner_meets_spec := Verity.Proofs.Owned.isOwner_meets_spec
abbrev isOwner_returns_correct_value := Verity.Proofs.Owned.isOwner_returns_correct_value
abbrev transferOwnership_unfold := Verity.Proofs.Owned.transferOwnership_unfold
abbrev transferOwnership_meets_spec_when_owner := Verity.Proofs.Owned.transferOwnership_meets_spec_when_owner
abbrev transferOwnership_changes_owner_when_allowed := Verity.Proofs.Owned.transferOwnership_changes_owner_when_allowed
abbrev constructor_getOwner_correct := Verity.Proofs.Owned.constructor_getOwner_correct
abbrev constructor_preserves_wellformedness := Verity.Proofs.Owned.constructor_preserves_wellformedness
abbrev getOwner_preserves_wellformedness := Verity.Proofs.Owned.getOwner_preserves_wellformedness

end Contracts.Owned.Proofs.Basic
