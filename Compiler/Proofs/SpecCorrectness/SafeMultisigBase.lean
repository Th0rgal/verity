/-
  Compiler.Proofs.SpecCorrectness.SafeMultisigBase (Scaffold)

  Placeholder file for proofs that the Safe base EDSL matches the
  ContractSpec used by the compiler.
-/

import Compiler.Proofs.SpecInterpreter
import Compiler.Specs.SafeMultisigBase
import DumbContracts.Examples.SafeMultisigBase

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs.SafeMultisigBase
open DumbContracts
open DumbContracts.Examples.SafeMultisigBase

/-- Convert EDSL ContractState to SpecStorage for SafeMultisigBase (placeholder). -/
def safeMultisigBaseEdslToSpecStorage (state : ContractState) : SpecStorage :=
  { slots := [
      (singleton.slot, addressToNat (state.storageAddr singleton.slot)),
      (ownerCount.slot, (state.storage ownerCount.slot).val),
      (threshold.slot, (state.storage threshold.slot).val),
      (nonce.slot, (state.storage nonce.slot).val),
      (deprecatedDomainSeparator.slot, (state.storage deprecatedDomainSeparator.slot).val)
    ]
    mappings := [] }

end Compiler.Proofs.SpecCorrectness
