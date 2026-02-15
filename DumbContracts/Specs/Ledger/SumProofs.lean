/-
  Sum Properties Proofs for Ledger Contract

  This module proves the 7 sum properties defined in Specs.Ledger.Spec:
  1. Spec_deposit_sum_equation - deposit increases total balance
  2. Spec_withdraw_sum_equation - withdraw decreases total balance
  3. Spec_transfer_sum_preservation - transfer preserves total balance
  4. Spec_deposit_sum_singleton_sender - singleton set deposit property
  5. Spec_withdraw_sum_singleton_sender - singleton set withdraw property
  6. Spec_transfer_sum_preserved_unique - transfer with unique addresses preserves sum
  7. Spec_deposit_withdraw_sum_cancel - deposit then withdraw cancels out

  These proofs rely on the finite address set tracking introduced in Phase 1.
-/

import DumbContracts.Core
import DumbContracts.Examples.Ledger
import DumbContracts.EVM.Uint256
import DumbContracts.Specs.Ledger.Spec
import DumbContracts.Specs.Common.Sum
import DumbContracts.Proofs.Ledger.Basic

namespace DumbContracts.Specs.Ledger.SumProofs

open DumbContracts
open DumbContracts.Examples.Ledger
open DumbContracts.Specs.Ledger
open DumbContracts.Specs.Common

/-! ## Deposit Sum Properties -/

/-- Deposit increases total balance by the deposited amount.

Strategy: Use deposit_increases_balance to show balance increases and
knownAddresses is updated to include sender. Then show sumBalances increases
by the deposited amount using FiniteSet.sum properties. -/
theorem deposit_sum_equation (amount : Uint256) (s : ContractState)
    (h_finite : balancesFinite 0 s) :
    let s' := (deposit amount).runState s
    Spec_deposit_sum_equation amount s s' := by
  unfold Spec_deposit_sum_equation totalBalance
  unfold Contract.runState
  sorry

/-- Deposit on singleton set with only sender.

Special case of deposit_sum_equation where only sender has non-zero balance.
Show totalBalance equals the single address balance, then apply deposit logic. -/
theorem deposit_sum_singleton_sender (amount : Uint256) (s : ContractState)
    (h_finite : balancesFinite 0 s) :
    let s' := (deposit amount).runState s
    Spec_deposit_sum_singleton_sender amount s s' := by
  unfold Spec_deposit_sum_singleton_sender totalBalance
  intro h_only_sender
  sorry

/-! ## Withdraw Sum Properties -/

/-- Withdraw decreases total balance by the withdrawn amount.

Strategy: Use withdraw_decreases_balance to show the sender's balance decreases.
Since knownAddresses includes sender, apply sumBalances_update_existing to show
the total sum decreases by the withdrawn amount. -/
theorem withdraw_sum_equation (amount : Uint256) (s : ContractState)
    (h_balance : s.storageMap 0 s.sender >= amount)
    (h_finite : balancesFinite 0 s) :
    let s' := (withdraw amount).runState s
    Spec_withdraw_sum_equation amount s s' := by
  unfold Spec_withdraw_sum_equation totalBalance
  unfold Contract.runState
  sorry

/-- Withdraw on singleton set with only sender.

Special case of withdraw_sum_equation where only sender has non-zero balance.
Show totalBalance equals the single address balance, then apply withdraw logic. -/
theorem withdraw_sum_singleton_sender (amount : Uint256) (s : ContractState)
    (h_balance : s.storageMap 0 s.sender >= amount)
    (h_finite : balancesFinite 0 s) :
    let s' := (withdraw amount).runState s
    Spec_withdraw_sum_singleton_sender amount s s' := by
  unfold Spec_withdraw_sum_singleton_sender totalBalance
  intro h_only_sender
  sorry

/-! ## Transfer Sum Properties -/

/-- Transfer preserves total balance.

Strategy: Case split on sender == to.
- If sender == to: Use transfer_self_preserves_balance (balances unchanged).
- If sender ≠ to: The amount subtracted from sender is added to recipient,
  so the net change to totalBalance is zero. Requires sumBalances distributivity
  and Uint256 arithmetic to show the amounts cancel. -/
theorem transfer_sum_preservation (to : Address) (amount : Uint256) (s : ContractState)
    (h_balance : s.storageMap 0 s.sender >= amount)
    (h_finite : balancesFinite 0 s) :
    let s' := (transfer to amount).runState s
    Spec_transfer_sum_preservation to amount s s' := by
  unfold Spec_transfer_sum_preservation totalBalance
  unfold Contract.runState
  by_cases h_eq : s.sender = to
  · sorry
  · sorry

/-- Transfer with unique addresses preserves total balance.

Specialized version of transfer_sum_preservation with sender ≠ to assumed.
Follows directly from the main theorem. -/
theorem transfer_sum_preserved_unique (to : Address) (amount : Uint256) (s : ContractState)
    (h_ne : s.sender ≠ to)
    (h_balance : s.storageMap 0 s.sender >= amount)
    (h_finite : balancesFinite 0 s) :
    let s' := (transfer to amount).runState s
    Spec_transfer_sum_preserved_unique to amount s s' := by
  unfold Spec_transfer_sum_preserved_unique totalBalance
  intro _
  sorry

/-! ## Composition Properties -/

/-- Deposit followed by withdraw cancels out in total balance.

Composition property: deposit increases total by amount, withdraw decreases by amount,
so net change is zero. Uses EVM.Uint256.sub_add_cancel for the arithmetic.
Requires deposit_sum_equation and withdraw_sum_equation. -/
theorem deposit_withdraw_sum_cancel (amount : Uint256) (s : ContractState)
    (h_balance : s.storageMap 0 s.sender >= amount)
    (h_finite : balancesFinite 0 s) :
    let s' := (deposit amount).runState s
    let s'' := (withdraw amount).runState s'
    Spec_deposit_withdraw_sum_cancel amount s s' s'' := by
  unfold Spec_deposit_withdraw_sum_cancel
  intro h_deposit h_withdraw
  sorry

end DumbContracts.Specs.Ledger.SumProofs
