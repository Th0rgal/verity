# Sum Properties Proof Strategy

## Overview

The 7 sum properties in `DumbContracts/Specs/Ledger/SumProofs.lean` prove invariants like "total supply = sum of all balances" using the finite address set abstraction (`FiniteAddressSet` in `DumbContracts/Core/FiniteSet.lean`).

## Proof Approach

All sum-preserving properties follow from basic operations:

1. **Deposit**: Increases one balance → sum increases by that amount
   - Uses `sumBalances_insert_new` or `sumBalances_update_existing`
   - Depends on whether sender was already in `knownAddresses`

2. **Withdraw**: Decreases one balance → sum decreases by that amount
   - Uses `sumBalances_update_existing` (sender must exist to have balance)

3. **Transfer**: Decreases one balance, increases another by same amount → sum unchanged
   - Net effect is zero (amounts cancel via Uint256 arithmetic)
   - Case split on `sender == to`

4. **Composition**: Properties compose via substitution
   - Example: `deposit_withdraw_sum_cancel` uses `sub_add_cancel`

## Required Helper Lemmas

### Straightforward
- `sumBalances_insert_existing` - Sum preserved when re-inserting existing address
- `sumBalances_zero_of_all_zero` - Induction on list with zero values
- `balancesFinite_preserved_deposit` - Case analysis on set membership

### Medium Complexity
- `sumBalances_insert_new` - Properties about `List.foldl` with addition
- `sumBalances_update_existing` - Splitting sum and recombining

Once helper lemmas are proven, main theorems follow directly from `deposit_increases_balance`, `withdraw_decreases_balance`, and arithmetic cancellation.
