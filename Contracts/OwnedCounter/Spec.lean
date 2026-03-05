import Verity.Specs.OwnedCounter.Spec

namespace Contracts.OwnedCounter.Spec

abbrev constructor_spec := Verity.Specs.OwnedCounter.constructor_spec
abbrev getCount_spec := Verity.Specs.OwnedCounter.getCount_spec
abbrev getOwner_spec := Verity.Specs.OwnedCounter.getOwner_spec
abbrev increment_spec := Verity.Specs.OwnedCounter.increment_spec
abbrev decrement_spec := Verity.Specs.OwnedCounter.decrement_spec
abbrev transferOwnership_spec := Verity.Specs.OwnedCounter.transferOwnership_spec

end Contracts.OwnedCounter.Spec
