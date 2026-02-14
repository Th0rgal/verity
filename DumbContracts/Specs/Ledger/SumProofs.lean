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

/-- Deposit increases total balance by the deposited amount -/
theorem deposit_sum_equation (amount : Uint256) (s : ContractState)
    (h_finite : balancesFinite 0 s) :
    let s' := (deposit amount).runState s
    Spec_deposit_sum_equation amount s s' := by
  unfold Spec_deposit_sum_equation totalBalance
  -- Strategy:
  -- 1. Use deposit_increases_balance to get: s'.storageMap 0 s.sender = add (s.storageMap 0 s.sender) amount
  -- 2. Determine if s.sender was in knownAddresses before deposit
  -- 3. Apply sumBalances_insert_new or sumBalances_insert_existing accordingly
  -- 4. Handle Uint256 arithmetic
  sorry

/-- Deposit on singleton set with only sender -/
theorem deposit_sum_singleton_sender (amount : Uint256) (s : ContractState)
    (h_finite : balancesFinite 0 s) :
    let s' := (deposit amount).runState s
    Spec_deposit_sum_singleton_sender amount s s' := by
  unfold Spec_deposit_sum_singleton_sender totalBalance
  -- Strategy:
  -- 1. Use hypothesis that only sender has non-zero balance
  -- 2. Show totalBalance s = s.storageMap 0 s.sender
  -- 3. Show totalBalance s' = add (s.storageMap 0 s.sender) amount
  -- 4. Apply deposit_increases_balance
  sorry

/-! ## Withdraw Sum Properties -/

/-- Withdraw decreases total balance by the withdrawn amount -/
theorem withdraw_sum_equation (amount : Uint256) (s : ContractState)
    (h_balance : s.storageMap 0 s.sender >= amount)
    (h_finite : balancesFinite 0 s) :
    let s' := (withdraw amount).runState s
    Spec_withdraw_sum_equation amount s s' := by
  unfold Spec_withdraw_sum_equation totalBalance
  -- Strategy:
  -- 1. Use withdraw_decreases_balance to get: s'.storageMap 0 s.sender = sub (s.storageMap 0 s.sender) amount
  -- 2. Show knownAddresses doesn't change (only value changes)
  -- 3. Apply sumBalances properties to show sum decreases by amount
  sorry

/-- Withdraw on singleton set with only sender -/
theorem withdraw_sum_singleton_sender (amount : Uint256) (s : ContractState)
    (h_balance : s.storageMap 0 s.sender >= amount)
    (h_finite : balancesFinite 0 s) :
    let s' := (withdraw amount).runState s
    Spec_withdraw_sum_singleton_sender amount s s' := by
  unfold Spec_withdraw_sum_singleton_sender totalBalance
  -- Strategy:
  -- 1. Use hypothesis that only sender has non-zero balance
  -- 2. Show totalBalance s = s.storageMap 0 s.sender
  -- 3. Show totalBalance s' = sub (s.storageMap 0 s.sender) amount
  -- 4. Apply withdraw_decreases_balance
  sorry

/-! ## Transfer Sum Properties -/

/-- Transfer preserves total balance -/
theorem transfer_sum_preservation (to : Address) (amount : Uint256) (s : ContractState)
    (h_balance : s.storageMap 0 s.sender >= amount)
    (h_finite : balancesFinite 0 s) :
    let s' := (transfer to amount).runState s
    Spec_transfer_sum_preservation to amount s s' := by
  unfold Spec_transfer_sum_preservation totalBalance
  -- Strategy:
  -- Case 1: s.sender == to
  --   Use transfer_self_preserves_balance
  --   Show balances unchanged, so sum unchanged
  -- Case 2: s.sender ≠ to
  --   Use transfer_decreases_sender and transfer_increases_recipient
  --   Show sum of (balance - amount) + (balance' + amount) = sum of balances
  --   The amount cancels out in the total
  by_cases h_eq : s.sender = to
  · sorry  -- Case: sender == to
  · sorry  -- Case: sender ≠ to

/-- Transfer with unique addresses preserves total balance -/
theorem transfer_sum_preserved_unique (to : Address) (amount : Uint256) (s : ContractState)
    (h_ne : s.sender ≠ to)
    (h_balance : s.storageMap 0 s.sender >= amount)
    (h_finite : balancesFinite 0 s) :
    let s' := (transfer to amount).runState s
    Spec_transfer_sum_preserved_unique to amount s s' := by
  unfold Spec_transfer_sum_preserved_unique totalBalance
  -- Strategy:
  -- Use h_ne explicitly (sender ≠ to)
  -- Apply transfer_decreases_sender and transfer_increases_recipient
  -- Show the arithmetic: (balance_sender - amount) + (balance_to + amount) = balance_sender + balance_to
  sorry

/-! ## Composition Properties -/

/-- Deposit followed by withdraw cancels out in total balance -/
theorem deposit_withdraw_sum_cancel (amount : Uint256) (s : ContractState)
    (h_balance : s.storageMap 0 s.sender >= amount)  -- Need sufficient balance after deposit
    (h_finite : balancesFinite 0 s) :
    let s' := (deposit amount).runState s
    let s'' := (withdraw amount).runState s'
    Spec_deposit_withdraw_sum_cancel amount s s' s'' := by
  unfold Spec_deposit_withdraw_sum_cancel
  -- Strategy:
  -- 1. Use deposit_sum_equation to show: totalBalance s' = add (totalBalance s) amount
  -- 2. Use withdraw_sum_equation to show: totalBalance s'' = sub (totalBalance s') amount
  -- 3. Substitute and use Uint256 arithmetic: sub (add x amount) amount = x
  -- 4. Apply sub_add_cancel theorem
  sorry

end DumbContracts.Specs.Ledger.SumProofs
