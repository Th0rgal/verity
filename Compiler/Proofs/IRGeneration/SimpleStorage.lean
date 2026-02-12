/-
  Layer 2: ContractSpec → IR Preservation for SimpleStorage

  Prove that compiling SimpleStorage spec to IR preserves semantics:
    interpretIR (compile simpleStorageSpec) = interpretSpec simpleStorageSpec

  This is the first step in Layer 2 verification, demonstrating the approach
  on the simplest possible contract.
-/

import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.IRGeneration.Expr
import Compiler.Proofs.SpecInterpreter
import Compiler.Specs
import Compiler.ContractSpec

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.Specs
open Compiler.ContractSpec
open DiffTestTypes

/-! ## SimpleStorage IR Compilation -/

/-- Compile SimpleStorage spec to IR
    Note: We need to provide selectors manually for now -/
def simpleStorageIR : Except String IRContract :=
  compile simpleStorageSpec [0x6057361d, 0x2e64cec1]

/-! ## Preservation Theorems -/

/-- The store function preserves semantics: IR execution matches Spec execution

    TODO: This theorem statement needs refinement to properly relate
    IRTransaction/IRResult with SpecInterpreter's Transaction/Result types.

    The key challenge: IRInterpreter uses Nat everywhere (addresses, values)
    while SpecInterpreter uses richer types (Address = String, Uint256).

    We need a translation layer between these representations.
-/
theorem store_preserves_semantics (value : Nat) (initialState : ContractState) :
  let spec := simpleStorageSpec
  let irContract := compile spec [0x6057361d, 0x2e64cec1]
  let sender := "test_sender"
  let tx : Transaction := {
    sender := sender
    functionName := "store"
    args := [value]
  }
  -- Create IR transaction
  let irTx : IRTransaction := {
    sender := addressToNat sender
    functionSelector := 0x6057361d  -- store selector
    args := [value]
  }
  -- Execute both sides
  let specResult := interpretSpec spec (SpecStorage.empty) tx
  match irContract with
  | .ok ir =>
      let irResult := interpretIR ir irTx
      -- Results should match
      resultsMatch ir.usesMapping [] irResult specResult initialState
  | .error _ => False
  :=
  simpleStorage_store_correct value initialState

/-- The retrieve function preserves semantics -/
theorem retrieve_preserves_semantics (initialState : ContractState) :
  let spec := simpleStorageSpec
  let irContract := compile spec [0x6057361d, 0x2e64cec1]
  let sender := "test_sender"
  let tx : Transaction := {
    sender := sender
    functionName := "retrieve"
    args := []
  }
  -- Create IR transaction
  let irTx : IRTransaction := {
    sender := addressToNat sender
    functionSelector := 0x2e64cec1  -- retrieve selector
    args := []
  }
  let specResult := interpretSpec spec (SpecStorage.empty) tx
  match irContract with
  | .ok ir =>
      let irResult := interpretIR ir irTx
      resultsMatch ir.usesMapping [] irResult specResult initialState
  | .error _ => False
  :=
  simpleStorage_retrieve_correct initialState

/-! ## Notes on Proof Strategy

The main challenge for Layer 2 proofs is aligning type representations:

**Spec Side**:
- Uses ContractState with Uint256, Address types
- SpecStorage with slots/mappings
- Transaction with sender : Address

**IR Side**:
- Uses IRState with only Nat
- IRTransaction with sender : Nat, functionSelector : Nat
- No type-level distinction between addresses and values

**Solution Approach**:
1. Define conversion functions: ContractState → IRState, Transaction → IRTransaction
2. Define relation: IRResult ≈ SpecInterpreter.Result (modulo type conversions)
3. Prove compilation preserves this relation

**Why This is Simpler than Layer 1**:
- IR semantics are more operational (variables, assignment, sstore)
- No nested monadic structure to reduce
- Clearer separation between compilation (ContractSpec → IR) and execution (IR → Result)
- The `compile` function is deterministic and structural

**Next Steps**:
1. Add type conversion infrastructure
2. Refine theorem statements with proper types
3. Prove store/retrieve preservation
4. Generalize to other contracts

-/

end Compiler.Proofs.IRGeneration
