# POC: DSL -> Constraint Harness

This proof-of-concept compiles a tiny DSL into a Solidity harness that asserts the
postconditions of an implementation contract.

## Supported DSL

```
contract SimpleToken

constructor(address owner, uint256 supply)

spec transfer(address to, uint256 amount):
  require: to != address(0)
  require: balance[msg.sender] >= amount
  ensure: balance[msg.sender] == old(balance[msg.sender]) - amount
  ensure: balance[to] == old(balance[to]) + amount
  ensure: totalSupply == old(totalSupply)
```

## Run

```bash
python3 research/poc_constraints/dsl_to_constraints.py specs/simple_token.dc src/SimpleTokenSpecHarness.sol
```

## Notes

- The harness calls the implementation and asserts the `ensure` clause.
- Multiple `ensure:` lines are supported (each becomes an `assert`).
- `old(<expr>)` captures pre-state values (currently limited to `uint256`).
- This is intentionally minimal to keep the pipeline auditable.
