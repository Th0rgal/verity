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

## Scenario D: Capped Mint (Invariant Preservation)

- State variables: `balance[owner]`, `totalSupply`, `maxSupply`, `owner`.
- Transition: `mint(amount)` restricted to `owner` and bounded by `maxSupply`.
- Postconditions:
  - `totalSupply` increases by `amount`.
  - `balance[owner]` increases by `amount`.
- Invariant:
  - `totalSupply <= maxSupply`.
- Proof model: DSL compiles to a spec harness that asserts preconditions, postconditions, and invariants.

## Scenario E: Broken Implementation (Negative Proof Case)

- State variables: `balance[account]`, `totalSupply`.
- Transition: `transfer(to, amount)` with the same preconditions and postconditions as Scenario A.
- Intent: show the harness failing when the implementation violates the spec (receiver balance not updated).
- Proof model: DSL compiles to a spec harness; a unit test demonstrates the `assert` failure.

## Scenario F: Broken Cap Invariant (Negative Proof Case)

- State variables: `balance[owner]`, `totalSupply`, `maxSupply`, `owner`.
- Transition: `mint(amount)` with the same preconditions as Scenario D.
- Intent: show the harness failing when the implementation violates postconditions/invariant (supply over-increment).
- Proof model: DSL compiles to a spec harness; a unit test demonstrates the `assert` failure.

## Scenario G: Implementation Hints (Metadata)

- State variables: none (metadata-only).
- Transition: any spec with optional `hint:` lines.
- Intent: capture human guidance for frontends/LLMs without affecting proof constraints.
- Proof model: hints are emitted as comments in the generated harness (no semantic impact).

## Scenario H: Witness-Based "Forall" Approximation

- State variables: `balance[account]`, `totalSupply`.
- Transition: `transferWitness(to, amount, other)` on a wrapper contract.
- Postconditions:
  - `balance[msg.sender]` decreases by `amount`.
  - `balance[to]` increases by `amount`.
  - `balance[other]` unchanged (witness for "all other accounts").
  - `totalSupply` unchanged.
- Proof model: DSL compiles a `forall other: <pre> => <post>` line into a witness-based `require` + `assert` pair, approximating a quantified invariant without encoding `forall`.
