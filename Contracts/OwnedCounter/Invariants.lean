import Verity.Specs.OwnedCounter.Invariants

namespace Contracts.OwnedCounter.Invariants

abbrev WellFormedState := Verity.Specs.OwnedCounter.WellFormedState
abbrev count_preserves_owner := Verity.Specs.OwnedCounter.count_preserves_owner
abbrev owner_preserves_count := Verity.Specs.OwnedCounter.owner_preserves_count
abbrev context_preserved := Verity.Specs.OwnedCounter.context_preserved

end Contracts.OwnedCounter.Invariants
