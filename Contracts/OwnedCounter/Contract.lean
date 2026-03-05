import Verity.Examples.OwnedCounter

namespace Contracts.OwnedCounter.Contract

abbrev owner := Verity.Examples.OwnedCounter.owner
abbrev count := Verity.Examples.OwnedCounter.count
abbrev increment := Verity.Examples.OwnedCounter.increment
abbrev decrement := Verity.Examples.OwnedCounter.decrement
abbrev getCount := Verity.Examples.OwnedCounter.getCount
abbrev getOwner := Verity.Examples.OwnedCounter.getOwner
abbrev transferOwnership := Verity.Examples.OwnedCounter.transferOwnership
abbrev isOwner := Verity.Examples.OwnedCounter.isOwner
abbrev onlyOwner := Verity.Examples.OwnedCounter.onlyOwner
abbrev «constructor» := Verity.Examples.OwnedCounter.constructor

end Contracts.OwnedCounter.Contract
