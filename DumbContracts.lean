import DumbContracts.Core
import DumbContracts.Stdlib.Math
import DumbContracts.Proofs.Stdlib.Math
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
import DumbContracts.Proofs.SimpleStorage.Correctness

import DumbContracts.Specs.Counter.Spec
import DumbContracts.Specs.Counter.Invariants
import DumbContracts.Proofs.Counter.Basic
import DumbContracts.Proofs.Counter.Correctness

import DumbContracts.Specs.Owned.Spec
import DumbContracts.Specs.Owned.Invariants
import DumbContracts.Proofs.Owned.Basic
import DumbContracts.Proofs.Owned.Correctness

import DumbContracts.Specs.SimpleToken.Spec
import DumbContracts.Specs.SimpleToken.Invariants
import DumbContracts.Proofs.SimpleToken.Basic
import DumbContracts.Proofs.SimpleToken.Correctness
import DumbContracts.Proofs.SimpleToken.Supply

import DumbContracts.Specs.OwnedCounter.Spec
import DumbContracts.Specs.OwnedCounter.Invariants
import DumbContracts.Proofs.OwnedCounter.Basic
import DumbContracts.Proofs.OwnedCounter.Correctness

import DumbContracts.Specs.Ledger.Spec
import DumbContracts.Specs.Ledger.Invariants
import DumbContracts.Proofs.Ledger.Basic
import DumbContracts.Proofs.Ledger.Correctness

import DumbContracts.Specs.SafeCounter.Spec
import DumbContracts.Specs.SafeCounter.Invariants
import DumbContracts.Proofs.SafeCounter.Basic
import DumbContracts.Proofs.SafeCounter.Correctness
