-- Verity — Complete Module Index
--
-- This file imports all public Verity modules so that downstream users
-- can write a single `import Verity` to access everything.
--
-- The modules are organized by layer:
--   1. Core — Contract monad, storage primitives, Uint256
--   2. Stdlib — Safe arithmetic, EVM-compatible ops
--   3. Examples — EDSL contract implementations
--   4. Specs — Formal specifications and state invariants
--   5. Proofs — Correctness proofs (EDSL ↔ Spec ↔ Compiler)

-- Core & Stdlib
import Verity.Core
import Verity.Core.Uint256
import Verity.Core.FiniteSet
import Verity.EVM.Uint256
import Verity.Stdlib.Math

-- Common specifications & invariants
import Verity.Specs.Common
import Verity.Specs.Common.Invariants
import Verity.Specs.Common.Sum

-- Proof automation & stdlib proofs
import Verity.Proofs.Stdlib.Math
import Verity.Proofs.Stdlib.Automation
import Verity.Proofs.Stdlib.MappingAutomation
import Verity.Proofs.Stdlib.SpecInterpreter

-- Example contracts (EDSL implementations)
import Verity.Examples.SimpleStorage
import Verity.Examples.Counter
import Verity.Examples.SafeCounter
import Verity.Examples.Owned
import Verity.Examples.OwnedCounter
import Verity.Examples.Ledger
import Verity.Examples.SimpleToken
import Verity.Examples.ReentrancyExample
import Verity.Examples.CryptoHash

-- SimpleStorage: Spec, Invariants, Proofs
import Verity.Specs.SimpleStorage.Spec
import Verity.Specs.SimpleStorage.Invariants
import Verity.Specs.SimpleStorage.Proofs
import Verity.Proofs.SimpleStorage.Basic
import Verity.Proofs.SimpleStorage.Correctness

-- Counter: Spec, Invariants, Proofs
import Verity.Specs.Counter.Spec
import Verity.Specs.Counter.Invariants
import Verity.Specs.Counter.Proofs
import Verity.Proofs.Counter.Basic
import Verity.Proofs.Counter.Correctness

-- SafeCounter: Spec, Invariants, Proofs
import Verity.Specs.SafeCounter.Spec
import Verity.Specs.SafeCounter.Invariants
import Verity.Specs.SafeCounter.Proofs
import Verity.Proofs.SafeCounter.Basic
import Verity.Proofs.SafeCounter.Correctness

-- Owned: Spec, Invariants, Proofs
import Verity.Specs.Owned.Spec
import Verity.Specs.Owned.Invariants
import Verity.Specs.Owned.Proofs
import Verity.Proofs.Owned.Basic
import Verity.Proofs.Owned.Correctness

-- OwnedCounter: Spec, Invariants, Proofs
import Verity.Specs.OwnedCounter.Spec
import Verity.Specs.OwnedCounter.Invariants
import Verity.Specs.OwnedCounter.Proofs
import Verity.Proofs.OwnedCounter.Basic
import Verity.Proofs.OwnedCounter.Correctness
import Verity.Proofs.OwnedCounter.Isolation

-- Ledger: Spec, Invariants, Proofs
import Verity.Specs.Ledger.Spec
import Verity.Specs.Ledger.Invariants
import Verity.Specs.Ledger.Proofs
import Verity.Proofs.Ledger.Basic
import Verity.Proofs.Ledger.Correctness
import Verity.Proofs.Ledger.Conservation

-- SimpleToken: Spec, Invariants, Proofs
import Verity.Specs.SimpleToken.Spec
import Verity.Specs.SimpleToken.Invariants
import Verity.Specs.SimpleToken.Proofs
import Verity.Proofs.SimpleToken.Basic
import Verity.Proofs.SimpleToken.Correctness
import Verity.Proofs.SimpleToken.Supply
import Verity.Proofs.SimpleToken.Isolation
