# Status

Last updated: 2026-02-09

## Current Focus
- Lean-only specs + implementations + proofs.
- Yul/ASM/bytecode as first-class artifacts.
- Keep the repo small and auditable.
- Track the external tooling landscape (specs + formal verification).
- Resolve spec aliasing hazards (sequential reads vs. forbid `from = to`).
- Make examples smaller + build an ergonomic EDSL surface (stdlib, macros, patterns).

## In Progress
- First compiler correctness lemma (arith + storage).
- Memory model for ABI return encoding.
- Spec shape for reverts (keep `Spec` minimal, add `SpecR`).
- External landscape refresh (Act/Scribble/Certora/SMTChecker/KEVM).
- Reconcile sequential-read vs old-state transfer specs (aliasing boundary).
- Decide whether to guard old-state specs with `from ≠ to` or adopt sequential reads by default.
- Supply accounting abstraction (list vs set/dedup semantics).
- EDSL ergonomics: add helpers, notations, and a minimal stdlib for common patterns.

## Recently Done
- Lean -> Yul pipeline with runtime + creation bytecode artifacts.
- Selector map (fixed + ABI keccak) and Foundry tests.
- Spec-style wrappers for storage and Euler-style risk examples.
- `SpecR` (specs with reverts) plus proofs for guarded storage + health check.
- Token-style transfer `SpecR` (address != 0, balance checks) with proofs.
- Transfer sum invariant for distinct accounts (small ERC20-style lemma).
- Transfer locality lemma (other balances unchanged).
- Transfer sum invariant for a list of non-updated accounts.
- Transfer sum invariant for `(from :: to :: rest)` lists (sum preserved with `from/to` included).
- Transfer totalSupply preservation lemma (transfer does not touch totalSupply slot).
- Transfer supply conservation lemma for a tracked list (`from :: to :: rest`).
- Transfer self-case lemma (when `from = to`, exec is a no-op after both writes).
- Added a sequential-read transfer spec (`transferSpecRSeq`) that matches exec semantics.
- Proved `transferSpecRSeq` meets execution and self-transfer implies no-op under the sequential spec.
- Added a self-transfer counterexample lemma showing `transferSpecR` cannot hold for `from = to` when `amount > 0`.
- Proved sequential transfer spec is equivalent to old-state spec when `from ≠ to`.
- Added a guarded transfer spec (`transferSpecRNoSelf`) and proof it meets execution when `from ≠ to`.
- Added a counterexample lemma showing list-based supply accounting breaks with duplicates.
- Split `Examples.lean` into multiple focused example modules (store ops, risk, token base, supply, transfer).
- Added a minimal EDSL stdlib (`require`, `unless`, `assert`, `sloadSlot`, `sstoreSlot`, `v`, `n`) to reduce syntax noise.
- Added `sloadVar`/`sstoreVar` helpers to cut boilerplate when using variable slots.
- Added a `maxStore` example (stores max(a,b) into a slot) plus selector + Foundry test.
- Minimal docs frontend and compressed docs.
- Further docs tightening (shorter guide + text).
- External landscape scan (spec languages, model checkers, prover stacks).

## Next
- Formalize ABI model and prove dispatcher + return path.
- Decide on selector strategy (fixed vs ABI keccak).
- Decide whether `SpecR` becomes the default `Spec` or stays optional.
- Pick one external tool to mirror in the DSL (Act or Scribble).
