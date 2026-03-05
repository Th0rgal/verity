import Verity.Proofs.SimpleStorage.Basic

namespace Contracts.SimpleStorage.Proofs.Basic

abbrev setStorage_updates_slot := Verity.Proofs.SimpleStorage.setStorage_updates_slot
abbrev getStorage_reads_slot := Verity.Proofs.SimpleStorage.getStorage_reads_slot
abbrev setStorage_preserves_other_slots := Verity.Proofs.SimpleStorage.setStorage_preserves_other_slots
abbrev setStorage_preserves_sender := Verity.Proofs.SimpleStorage.setStorage_preserves_sender
abbrev setStorage_preserves_address := Verity.Proofs.SimpleStorage.setStorage_preserves_address
abbrev setStorage_preserves_addr_storage := Verity.Proofs.SimpleStorage.setStorage_preserves_addr_storage
abbrev setStorage_preserves_map_storage := Verity.Proofs.SimpleStorage.setStorage_preserves_map_storage
abbrev store_meets_spec := Verity.Proofs.SimpleStorage.store_meets_spec
abbrev retrieve_meets_spec := Verity.Proofs.SimpleStorage.retrieve_meets_spec
abbrev store_retrieve_correct := Verity.Proofs.SimpleStorage.store_retrieve_correct
abbrev store_preserves_wellformedness := Verity.Proofs.SimpleStorage.store_preserves_wellformedness
abbrev retrieve_preserves_state := Verity.Proofs.SimpleStorage.retrieve_preserves_state
abbrev retrieve_twice_idempotent := Verity.Proofs.SimpleStorage.retrieve_twice_idempotent

end Contracts.SimpleStorage.Proofs.Basic
