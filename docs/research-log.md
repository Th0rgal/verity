# Research Log

## 2026-02-09
- Added spec-style wrappers for storage and risk examples.
- Added `SpecR` (specs with explicit revert predicates) and proofs.
- Added token-style transfer `SpecR` + proofs (revert on zero address or low balance).
- Added sum-preservation lemma for transfer (distinct accounts).
- Added transfer locality lemma (other balances unchanged).
- Added transfer sum lemma for a list of non-updated accounts.
- Added transfer sum lemma for `(from :: to :: rest)` lists (sum preserved with `from/to` included).
- Added totalSupply slot model + lemma showing transfer does not modify totalSupply.
- Added supply conservation lemma for a tracked list (`from :: to :: rest`) under transfer.
- Added transfer self-case lemma (when `from = to`, exec is a no-op after both writes).
- Added sequential-read transfer spec (`transferSpecRSeq`) to match exec semantics.
- Proved `transferSpecRSeq` meets execution and self-transfer is a no-op under the sequential spec.
- Added a self-transfer counterexample lemma showing `transferSpecR` cannot hold for `from = to` when `amount > 0`.
- Proved sequential transfer spec is equivalent to old-state spec when `from ≠ to`.
- Added a guarded transfer spec (`transferSpecRNoSelf`) and proof it meets execution when `from ≠ to`.
- Added a small counterexample lemma showing list-based supply accounting breaks with duplicates (motivation for sets/dedup).
- Split `Examples.lean` into multiple focused example modules.
- Added a minimal EDSL stdlib with common helpers (`require`, `unless`, `assert`, slot helpers, var/lit helpers).
- Added `sloadVar`/`sstoreVar` stdlib helpers for variable slot access.
- Added a tiny `maxStore` example (store max(a,b) into a slot) plus selector + Foundry test.
- Refreshed external landscape notes (Act, Scribble, Certora, SMTChecker, KEVM, Kontrol).
- Added selector map artifact (fixed + ABI keccak).
- Fixed Foundry selectors and moved to Shanghai EVM.
- Added Foundry tests for generated contracts.
- Compressed docs + tightened minimal frontend.
- Scanned external tooling landscape (Act, Scribble, Certora, SMTChecker, KEVM/Kontrol, VerX, Move Prover).
