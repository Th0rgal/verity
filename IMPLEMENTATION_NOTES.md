# Sum Properties Proof Strategy

> **Status**: ✅ Complete — all 7/7 sum properties proven with zero `sorry` in `Verity/Proofs/Ledger/Conservation.lean`.

## Overview

The 7 sum properties in `Verity/Proofs/Ledger/Conservation.lean` prove invariants like "total supply = sum of all balances" using `List.countOcc` for exact sum equations.

## Proof Approach

All sum-preserving properties follow from basic operations:

1. **Deposit**: Increases one balance → sum increases by that amount
   - Uses `map_sum_point_update` with `countOcc`/`countOccU` helpers
   - Exact equation: `new_sum = old_sum + countOccU(sender) * amount`

2. **Withdraw**: Decreases one balance → sum decreases by that amount
   - Uses `map_sum_point_decrease`
   - Exact equation: `new_sum + countOccU(sender) * amount = old_sum`

3. **Transfer**: Decreases one balance, increases another by same amount → sum unchanged
   - Uses `map_sum_transfer_eq`
   - Net effect: `new_sum + countOccU(sender)*amt = old_sum + countOccU(to)*amt`
   - Case split on `sender == to`

4. **Composition**: Properties compose via substitution
   - Example: `deposit_withdraw_sum_cancel` uses `sub_add_cancel`

## Helper Definitions and Lemmas (all proven)

### Core Definitions
- `countOcc` — count occurrences of an address in `knownAddresses`
- `countOccU` — `countOcc` cast to `Uint256`

### Private Lemmas
- `countOcc_cons_eq` — simplification for matching head
- `countOcc_cons_ne` — simplification for non-matching head
- `countOccU_cons_eq` — `Uint256` version of `countOcc_cons_eq`
- `countOccU_cons_ne` — `Uint256` version of `countOcc_cons_ne`
- `map_sum_point_update` — exact sum after adding: `sum f' = sum f + count * delta`
- `map_sum_point_decrease` — exact sum after subtracting: `sum f' + count * delta = sum f`
- `map_sum_transfer_eq` — exact conservation: `sum f' + count(src)*d = sum f + count(dst)*d`
