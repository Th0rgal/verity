# Goal Scenarios

These scenarios are the “golden paths” we want the DSL compiler and proof tooling to express and prove.

## Scenario A: Token Transfer (Spec → Constraints)

- State variables: `balance[account]`, `totalSupply`.
- Invariants:
  - Non-negative balances.
  - Supply conservation (no mint/burn in transfer).
- Transition: `Transfer(from, to, amount)`.
- Proof model: DSL compiles to postcondition assertions; SMTChecker proves the implementation satisfies them.

## Scenario B: Health Factor (Loan Update)

- State variables: `collateral`, `debt`.
- Invariant: `collateralValue >= debt * minHealthFactor`.
- Transition: `Update(user, newCollateral, newDebt)`.
- Proof model: DSL compiles to a spec harness with `assert` statements; SMTChecker proves the property.
