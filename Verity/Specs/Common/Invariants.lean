import Verity.Core

namespace Verity.Specs

/--
  Multi-Transaction Invariant Framework

  This module provides utilities for proving that state invariants hold
  across arbitrary sequences of transactions, not just single operations.

  ## Problem

  Each theorem in Verity proves a property about a single transaction:
  - `transfer_sum_preserved` proves sum conservation for ONE transfer
  - `mint_reverts_when_not_owner` proves access control for ONE mint

  But real smart contracts are vulnerable to multi-transaction attacks:
  - State accumulated across calls can reach unexpected configurations
  - Reentrancy exploits span multiple transactions
  - Economic attacks combine multiple operations

  ## Solution

  Define an inductive invariant and prove it preserved:
  1. Constructor establishes the invariant (base case)
  2. Each public function preserves the invariant (inductive step)
  3. Compose via induction to get invariant for ANY transaction sequence

  ## Usage

  ```lean
  -- Define your invariant
  class MyContractInvariant (s : ContractState) : Prop where
    wellFormed : WellFormedState s
    totalSupplyBounded : s.storage 0 ≤ MAX_UINT256

  -- Prove constructor establishes invariant
  instance constructorEstablishesInvariant :
    ConstructorEstablishesInvariant MyContractInvariant where
    constructor_invariant := by sorry

  -- Prove each function preserves invariant
  instance transferPreservesInvariant (to : Address) (amount : Uint256) :
    PreservesInvariant MyContractInvariant (transfer to amount) where
    preservation := by sorry

  -- Get theorem for any transaction sequence
  #check invariant_holds_for_all_transactions
  ```
-/

open Verity

/-- Typeclass for inductive invariants.
  
  An inductive invariant I(s) holds if:
  1. Base case: constructor establishes I
  2. Inductive step: ∀s, I(s) → after any public function f, I(s')

  Then by induction, I holds for any sequence of transactions.
-/
class InductiveInvariant (I : ContractState → Prop) : Type where
  /-- The invariant holds after constructor initialization. -/
  constructor_establishes : I defaultState
  /-- Each public function preserves the invariant. -/
  preserves : ∀ {s : ContractState}, I s → ∀ (f : Contract Unit), preservesInvariant I f s

/-- Evidence that a function preserves an invariant. -/
class PreservesInvariant (I : ContractState → Prop) (f : Contract Unit) (s : ContractState) where
  preservation : I s → I (f.run s).snd

/-- Execute a list of transactions and return the final state. -/
def executeAll (txs : List (Contract Unit)) (s₀ : ContractState) : ContractState :=
  match txs with
  | [] => s₀
  | f :: rest => executeAll rest (f.run s₀).snd

/-- Main theorem: invariant holds for any transaction sequence.
  
  If:
  1. I is an inductive invariant (base case + preservation for each function)
  2. Initial state s₀ satisfies I
  
  Then for any transaction list txs, the final state after executing txs satisfies I.
-/
theorem invariant_holds_for_all_transactions 
    (I : ContractState → Prop) 
    [InductiveInvariant I]
    (s₀ : ContractState) 
    (h_init : I s₀)
    (txs : List (Contract Unit)) :
    I (executeAll txs s₀) :=
  by
    induction txs with
    | nil => exact h_init
    | cons f rest ih =>
      have : PreservesInvariant I f s₀ := InductiveInvariant.preserves
      have : I ((f.run s₀).snd) := Preserveservation.preservation h_init
      exact ih this

/-- Shorthand for proving preservation when the function always succeeds.
  
  If a function never reverts and always transforms state in an invariant-preserving
  way, use this for simpler proofs.
-/
class AlwaysSucceedsAndPreserves (I : ContractState → Prop) (f : Contract Unit) (s : ContractState) extends PreservesInvariant I f s where
  /-- The contract executes successfully (no revert). -/
  success : (f.run s).fst.isSuccess = true
  /-- State transformation preserves invariant. -/
  state_preserve : I ((f.run s).snd)

/-- Execute a list of transactions, collecting all results. -/
def executeAllWithResults (txs : List (Contract Unit)) (s₀ : ContractState) : List (ContractState × Bool) :=
  match txs with
  | [] => []
  | f :: rest =>
      let result := f.run s₀
      let success := match result.fst with | .success _ _ => true | .revert _ _ => false
      (result.snd, success) :: executeAllWithResults rest result.snd

/-- Variant: prove invariant holds for all successful transaction sequences.
  
  Useful when some functions can revert - we only care about paths where
  all transactions succeed.
-/
theorem invariant_holds_for_successful_transactions
    (I : ContractState → Prop)
    [InductiveInvariant I]
    (s₀ : ContractState)
    (h_init : I s₀)
    (txs : List (Contract Unit))
    (h_all_success : ∀ s, (executeAllWithResults txs s).all (·.2 = true)) :
    I (executeAll txs s₀) :=
  by
    induction txs generalizing s₀ with
    | nil => exact h_init
    | cons f rest ih =>
      have : PreservesInvariant I f s₀ := InductiveInvariant.preserves
      have h_success : (f.run s₀).fst.isSuccess = true := by
        simp [executeAllWithResults] at h_all_success
        exact h_all_success.symm
      have : I ((f.run s₀).snd) := PreservesInvariant.preservation h_init
      exact ih this

end Verity.Specs
