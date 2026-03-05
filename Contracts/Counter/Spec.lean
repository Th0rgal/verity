import Verity.Specs.Counter.Spec

namespace Contracts.Counter.Spec

abbrev increment_spec := Verity.Specs.Counter.increment_spec
abbrev decrement_spec := Verity.Specs.Counter.decrement_spec
abbrev getCount_spec := Verity.Specs.Counter.getCount_spec
abbrev increment_getCount_spec := Verity.Specs.Counter.increment_getCount_spec
abbrev decrement_getCount_spec := Verity.Specs.Counter.decrement_getCount_spec
abbrev increment_decrement_cancel := Verity.Specs.Counter.increment_decrement_cancel
abbrev two_increments_spec := Verity.Specs.Counter.two_increments_spec

end Contracts.Counter.Spec
