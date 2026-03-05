import Verity.Specs.Counter.Invariants

namespace Contracts.Counter.Invariants

abbrev WellFormedState := Verity.Specs.Counter.WellFormedState
abbrev storage_isolated := Verity.Specs.Counter.storage_isolated
abbrev addr_storage_unchanged := Verity.Specs.Counter.addr_storage_unchanged
abbrev map_storage_unchanged := Verity.Specs.Counter.map_storage_unchanged
abbrev context_preserved := Verity.Specs.Counter.context_preserved
abbrev state_preserved_except_count := Verity.Specs.Counter.state_preserved_except_count

end Contracts.Counter.Invariants
