/-
  Layer 2: ContractSpec → IR Preservation for SimpleStorage

  Prove that compiling SimpleStorage spec to IR preserves semantics:
    interpretIR (compile simpleStorageSpec) = interpretSpec simpleStorageSpec

  This is the first step in Layer 2 verification, demonstrating the approach
  on the simplest possible contract.
-/

import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.IRGeneration.Conversions
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

/-- The store function preserves semantics: IR execution matches Spec execution.

    This statement now uses the explicit conversion layer:
    - `transactionToIRTransaction` for the call
    - `specStorageToIRState` for initial IR state
    This cleanly relates Spec and IR representations.
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
  -- Create IR transaction via conversion layer
  let irTx : IRTransaction := transactionToIRTransaction tx 0x6057361d
  -- Execute both sides
  let specResult := interpretSpec spec (SpecStorage.empty) tx
  match irContract with
  | .ok ir =>
      let irResult := interpretIR ir irTx (specStorageToIRState SpecStorage.empty sender)
      -- Results should match
      resultsMatch ir.usesMapping [] irResult specResult
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
  -- Create IR transaction via conversion layer
  let irTx : IRTransaction := transactionToIRTransaction tx 0x2e64cec1
  let specResult := interpretSpec spec (SpecStorage.empty) tx
  match irContract with
  | .ok ir =>
      let irResult := interpretIR ir irTx (specStorageToIRState SpecStorage.empty sender)
      resultsMatch ir.usesMapping [] irResult specResult
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
