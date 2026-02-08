# POC: Dumb Contract DSL -> Solidity

This proof-of-concept parses a minimal DSL (see `specs/token.dc`) and emits a Solidity
skeleton that captures requires/ensures with on-chain assertions.

## What it demonstrates

- Translating simple `require` and `ensure` clauses into Solidity `require`/`assert`.
- Capturing `old(...)` values for postcondition checks.
- Emitting TODOs for quantified statements (not supported in this POC).

## Run

```bash
python3 research/poc_dsl/dsl_to_sol.py specs/token.dc research/poc_dsl/generated/Token.sol
```

## Limitations

- No parsing of complex expressions beyond the example.
- Quantifiers are only emitted as comments.
- Assumes token-like state variables exist.
- This is not safe for production use.
