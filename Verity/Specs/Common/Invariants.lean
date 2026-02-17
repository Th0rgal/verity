import Verity.Core

/-!
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
  structure MyContractInvariant (s : ContractState) : Prop where
    wellFormed : WellFormedState s
    totalSupplyBounded : s.storage 0 ≤ MAX_UINT256

  -- Prove constructor establishes invariant
  theorem constructor_establishes : MyContractInvariant defaultState := ...

  -- Prove each function preserves invariant  
  theorem transfer_preserves {s : ContractState} (h : MyContractInvariant s)
    (to : Address) (amount : Uint256) :
    MyContractInvariant ((transfer to amount).run s).snd := ...

  -- Use the main theorem
  theorem all_transactions_preserve_invariant 
      (s₀ : ContractState) (h₀ : MyContractInvariant s₀)
      (txs : List (Contract Unit)) :
      MyContractInvariant (executeAll txs s₀) := ...
  ```
-/

namespace Verity.Specs

open Verity

/-- Execute a list of transactions and return the final state. -/
def executeAll (txs : List (Contract Unit)) (s₀ : ContractState) : ContractState :=
  match txs with
  | [] => s₀
  | f :: rest => executeAll rest (f.run s₀).snd

/-- Main theorem: invariant holds for any transaction sequence.
  
  If:
  1. The invariant holds for the initial state
  2. Each transaction in the list preserves the invariant
  
  Then the invariant holds after executing all transactions.
-/
theorem invariant_holds_for_all_transactions 
    (I : ContractState → Prop) 
    (s₀ : ContractState) 
    (h_init : I s₀)
    (txs : List (Contract Unit))
    (h_preserves : ∀ (s : ContractState) (f : Contract Unit), I s → I (f.run s).snd) :
    I (executeAll txs s₀) :=
  by
    induction txs generalizing s₀ with
    | nil => exact h_init
    | cons f rest ih =>
      have : I ((f.run s₀).snd) := h_preserves s₀ f h_init
      exact ih ((f.run s₀).snd) this

/-- Execute transactions and collect success/failure results. -/
def executeAllWithResults (txs : List (Contract Unit)) (s₀ : ContractState) : List (ContractState × Bool) :=
  match txs with
  | [] => []
  | f :: rest =>
      let result := f.run s₀
      let success := ContractResult.isSuccess result
      (result.snd, success) :: executeAllWithResults rest result.snd

end Verity.Specs
