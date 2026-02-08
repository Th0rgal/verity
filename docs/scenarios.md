# Goal Scenarios

These scenarios are the “golden paths” we want the DSL compiler and proof tooling to express and prove.

## Scenario A: Simple Token Transfer (Spec → Constraints)

- State variables: `balance[account]`, `totalSupply`.
- Transition: `transfer(to, amount)` with explicit preconditions (`to != address(0)` and sufficient balance).
- Postconditions:
  - `balance[msg.sender]` decreases by `amount`.
  - `balance[to]` increases by `amount`.
  - `totalSupply` unchanged.
- Proof model: DSL compiles to a spec harness with `old(...)` capture + `assert`; SMTChecker proves the implementation satisfies them.

## Scenario B: Health Factor (Loan Update)

- State variables: `collateral`, `debt`.
- Invariant: `collateralValue >= debt * minHealthFactor`.
- Transition: `Update(user, newCollateral, newDebt)`.
- Proof model: DSL compiles to a spec harness with `assert` statements; SMTChecker proves the property.

## Scenario C: Mintable Token (Owner-Only Mint)

- State variables: `balance[owner]`, `totalSupply`, `owner`.
- Transition: `mint(amount)` restricted to `owner`.
- Postconditions:
  - `totalSupply` increases by `amount`.
  - `balance[owner]` increases by `amount`.
- Proof model: DSL compiles to a spec harness using `old(...)` capture and `assert` checks.
