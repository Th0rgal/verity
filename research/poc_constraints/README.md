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
  hint: update sender balance then receiver balance, emit Transfer
  forall other: other != msg.sender && other != to => balance[other] == old(balance[other])
  ensure: balance[msg.sender] == old(balance[msg.sender]) - amount
  ensure: balance[to] == old(balance[to]) + amount
  ensure: totalSupply == old(totalSupply)
```

## Run

```bash
python3 research/poc_constraints/dsl_to_constraints.py specs/simple_token.dc src/SimpleTokenSpecHarness.sol
```

Generate all harnesses listed in the manifest:

```bash
./script/generate_constraints.sh
```

## Notes

- The harness calls the implementation and asserts the `ensure` clause.
- Multiple `ensure:` lines are supported (each becomes an `assert`).
- `old(<expr>)` captures pre-state values (currently limited to `uint256`).
- `hint:` lines are emitted as comments to preserve implementation guidance.
- `forall` lines compile into a witness-based `require` + `assert` pair.
- This is intentionally minimal to keep the pipeline auditable.
