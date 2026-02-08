# Ethereum Dumb Contracts (Draft Notes)

Note: This is the historical idea draft. The active plan is Lean-only and
documented in `docs/roadmap.md` and `docs/formal-approach.md`.

## Context

Smart contracts are too smart for their own good. Implementation detail often diverges from the intended rules, creating entire classes of bugs.

A "dumb" contract expresses *rules* rather than how to follow them. For example:

```text
invariant NonNegativeBalances:
  forall account: balance[account] >= 0

invariant SupplyConservation:
  sum(balance) == totalSupply

spec Transfer(from, to, amount):
  require: to != address(0)
  ensure:
    balance[from] == old(balance[from]) - amount
    balance[to] == old(balance[to]) + amount
    forall addr != from && addr != to:
      balance[addr] == old(balance[addr])
```

If the Euler invariant below could have been enforced, the exploit might have been prevented:

```text
collateralValue >= debt * minHealthFactor
```

## Why It Isn't The Case Now

1. A specification isn't enough; you still need an implementation. The opposite is not true.
2. Even if you do create a spec, you have no guarantee it matches the implementation.

tl;dr: Historically, effort outweighed the benefit.

But as LLMs improve, the marginal cost of writing code collapses, while the cost of bugs remains. This flips the calculus.

## End Goal (Vision)

- You write simple specs for variables you own. This is the “dumb contract”.
- Anyone can submit state diffs to the chain, as long as they can prove the rules for each updated variable were followed.
- Frontends provide implementation logic.
- Privacy is default because only resulting state changes are public.

## MVP

- A simple DSL for specs with “implementation hints”.
- The DSL compiles to Solidity (or an EVM subset).
- Formal proof generation links specs and compiled code.

## Next Steps

- Investigate if LLMs can generate implementations from specs.
