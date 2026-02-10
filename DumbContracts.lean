import DumbContracts.Core
import DumbContracts.Stdlib.Math
import DumbContracts.Examples.SimpleStorage
import DumbContracts.Examples.Counter
import DumbContracts.Examples.SafeCounter
import DumbContracts.Examples.Owned
import DumbContracts.Examples.OwnedCounter
import DumbContracts.Examples.Ledger
import DumbContracts.Examples.SimpleToken

-- Formal Verification
import DumbContracts.Specs.SimpleStorage.Spec
import DumbContracts.Specs.SimpleStorage.Invariants
import DumbContracts.Proofs.SimpleStorage.Basic

import DumbContracts.Specs.Counter.Spec
import DumbContracts.Specs.Counter.Invariants
import DumbContracts.Proofs.Counter.Basic

import DumbContracts.Specs.Owned.Spec
import DumbContracts.Specs.Owned.Invariants
import DumbContracts.Proofs.Owned.Basic

import DumbContracts.Specs.SimpleToken.Spec
import DumbContracts.Specs.SimpleToken.Invariants
import DumbContracts.Proofs.SimpleToken.Basic
