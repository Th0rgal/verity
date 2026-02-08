# POC: DSL -> Constraint Harness

This proof-of-concept compiles a tiny DSL into a Solidity harness that asserts the
postconditions of an implementation contract.

## Supported DSL

```
contract Loan

spec update(address user, uint256 newCollateral, uint256 newDebt):
  ensure: debt[user] == 0 || collateral[user] * 1e18 >= debt[user] * minHealthFactor
```

## Run

```bash
python3 research/poc_constraints/dsl_to_constraints.py specs/loan.dc src/LoanSpecHarness.sol
```

## Notes

- The harness calls the implementation and asserts the `ensure` clause.
- This is intentionally minimal to keep the pipeline auditable.
