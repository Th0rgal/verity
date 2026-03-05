import Verity.Proofs.Counter.Basic

namespace Contracts.Counter.Proofs.Basic

abbrev setStorage_updates_count := Verity.Proofs.Counter.setStorage_updates_count
abbrev getStorage_reads_count := Verity.Proofs.Counter.getStorage_reads_count
abbrev setStorage_preserves_other_slots := Verity.Proofs.Counter.setStorage_preserves_other_slots
abbrev setStorage_preserves_context := Verity.Proofs.Counter.setStorage_preserves_context
abbrev setStorage_preserves_addr_storage := Verity.Proofs.Counter.setStorage_preserves_addr_storage
abbrev setStorage_preserves_map_storage := Verity.Proofs.Counter.setStorage_preserves_map_storage
abbrev increment_meets_spec := Verity.Proofs.Counter.increment_meets_spec
abbrev increment_adds_one := Verity.Proofs.Counter.increment_adds_one
abbrev decrement_meets_spec := Verity.Proofs.Counter.decrement_meets_spec
abbrev decrement_subtracts_one := Verity.Proofs.Counter.decrement_subtracts_one
abbrev getCount_meets_spec := Verity.Proofs.Counter.getCount_meets_spec
abbrev getCount_reads_count_value := Verity.Proofs.Counter.getCount_reads_count_value
abbrev increment_getCount_correct := Verity.Proofs.Counter.increment_getCount_correct
abbrev decrement_getCount_correct := Verity.Proofs.Counter.decrement_getCount_correct
abbrev increment_twice_adds_two := Verity.Proofs.Counter.increment_twice_adds_two
abbrev increment_decrement_cancel := Verity.Proofs.Counter.increment_decrement_cancel
abbrev increment_preserves_wellformedness := Verity.Proofs.Counter.increment_preserves_wellformedness
abbrev decrement_preserves_wellformedness := Verity.Proofs.Counter.decrement_preserves_wellformedness
abbrev getCount_preserves_state := Verity.Proofs.Counter.getCount_preserves_state

end Contracts.Counter.Proofs.Basic
