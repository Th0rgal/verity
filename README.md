<p align="center">
  <img src="verity.svg" alt="Verity" width="200" />
</p>

<h1 align="center">Verity</h1>

<p align="center">
  <strong>A formally verified smart contract compiler. Read the <a href="https://lfglabs.dev/research/verity">paper</a>.</strong>
</p>

<p align="center">
  <a href="https://github.com/lfglabs-dev/verity/blob/main/LICENSE.md"><img src="https://img.shields.io/badge/license-MIT-blue.svg" alt="MIT License"></a>
  <a href="https://github.com/lfglabs-dev/verity"><img src="https://img.shields.io/badge/built%20with-Lean%204-blueviolet.svg" alt="Built with Lean 4"></a>
  <a href="https://github.com/lfglabs-dev/verity/blob/main/docs/VERIFICATION_STATUS.md"><img src="https://img.shields.io/badge/verification%20status-live-brightgreen.svg" alt="Verification status"></a>
  <a href="https://github.com/lfglabs-dev/verity/actions"><img src="https://img.shields.io/github/actions/workflow/status/lfglabs-dev/verity/verify.yml?label=verify" alt="Verify"></a>
</p>

---

Verity is a formally verified smart contract compiler written in [Lean 4](https://lean-lang.org/). You write contracts in an embedded DSL, state what they should do, prove those properties hold, and compile to EVM bytecode. The compiler itself is proven to preserve semantics across three verified layers.

<!-- BEGIN GENERATED STATS -->
| Metric | Value |
|--------|-------|
| Theorems | 277 (277 proven, 0 sorry) |
| Axioms | 0 |
| Foundry tests | 520 (239 property) |
| Verified contracts | 11 |
| Core EDSL | 635 lines |
| Lean | 4.22.0 |
<!-- END GENERATED STATS -->

Every number above is extracted from the codebase and verified on every commit. `0 sorry` means no proof is left incomplete. `0 axioms` means no unproven assumptions remain in the compiler stack.

## What is verified

Verity proves that compilation preserves behavior at three stages. Each layer is a machine-checked Lean theorem.

**Layer 1** (EDSL to CompilationModel): the `verity_contract` macro generates both an executable Lean program and a compiler-facing model from a single definition. Per-contract bridge theorems prove they agree.

**Layer 2** (CompilationModel to IR): a generic whole-contract theorem covers the supported fragment with zero axioms. No per-contract proof effort needed.

**Layer 3** (IR to Yul): all statement types are proven equivalent. The dispatch bridge is an explicit theorem hypothesis, not an axiom.

The Yul-to-bytecode step is handled by `solc` (v0.8.33, pinned) and is not verified by Verity. See [TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md) for the complete trust boundary.

## How it works

```
verity_contract Counter where
  storage count : Uint256 := slot 0
  function increment () : Unit := do
    let current <- getStorage count
    setStorage count (add current 1)
```

```lean
theorem increment_correct (s : ContractState) :
    let s' := ((increment).run s).snd
    s'.storage 0 = add (s.storage 0) 1 := by rfl
```

The proof passes by `rfl` (reflexivity): Lean's kernel evaluates both sides and confirms they are definitionally equal. No external solver, no bounded model checker, no trust in anything beyond Lean's type theory.

## Quick start

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.elan/env
git clone https://github.com/lfglabs-dev/verity.git && cd verity
lake build                        # verify all proofs (~20 min first build)
make check                        # run full CI validation suite
FOUNDRY_PROFILE=difftest forge test  # differential tests: EDSL vs EVM
```

## How Verity compares

| | Certora | Halmos | Verity |
|---|---|---|---|
| **Approach** | Bounded model checking | Symbolic execution | Theorem proving in Lean 4 |
| **Proof scope** | Bounded (configurable depth) | Bounded (path explosion) | Unbounded (all inputs, all paths) |
| **Compiler trust** | Trusts solc entirely | Trusts solc entirely | Verifies 3 compilation layers |
| **Best for** | Production audits at scale | Bug-finding in Foundry | High-assurance contracts |

Verity is complementary to these tools. It is for cases where you need mathematical certainty across all inputs and all execution paths.

## Documentation

| Resource | Description |
|----------|-------------|
| [veritylang.com](https://veritylang.com/) | Full documentation site |
| [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md) | Theorem counts, proof status, test coverage |
| [TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md) | What is verified vs. what is trusted |
| [AXIOMS.md](AXIOMS.md) | Documented axioms (currently 0) |
| [AUDIT.md](AUDIT.md) | Trust-boundary audit evidence and CI guards |
| [CONTRIBUTING.md](CONTRIBUTING.md) | Contribution guidelines |

### Research

- [Verity: A Formally Verified Smart Contract Compiler](https://lfglabs.dev/research/verity)
- [Verity Benchmark: AI-Driven Proof Generation](https://lfglabs.dev/research/verity-benchmark)
- [What is a formal proof?](https://lfglabs.dev/research/what-is-a-formal-proof)

## Support

Verity is a public good. If you'd like to support the project, you can donate via Giveth:

[verity: Smart Contracts Security for the Age of AI](https://giveth.io/project/verity:-smart-contracts-security-for-the-age-of-ai)
