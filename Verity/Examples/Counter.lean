import Verity.Examples.MacroContracts.Core

namespace Verity.Examples.Counter

def count : StorageSlot Uint256 := ⟨0⟩

abbrev increment := Verity.Examples.MacroContracts.Counter.increment
abbrev decrement := Verity.Examples.MacroContracts.Counter.decrement
abbrev getCount := Verity.Examples.MacroContracts.Counter.getCount
abbrev previewAddTwice := Verity.Examples.MacroContracts.Counter.previewAddTwice
abbrev previewOps := Verity.Examples.MacroContracts.Counter.previewOps
abbrev previewEnvOps := Verity.Examples.MacroContracts.Counter.previewEnvOps
abbrev previewLowLevel := Verity.Examples.MacroContracts.Counter.previewLowLevel

end Verity.Examples.Counter
