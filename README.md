<p align="center">
  <img src="verity.svg" alt="Verity" width="200" />
</p>

<h1 align="center">Verity</h1>

<p align="center">
  <strong>Formally verified smart contracts. From spec to bytecode.</strong>
</p>

<p align="center">
  <a href="https://github.com/lfglabs-dev/verity/blob/main/LICENSE.md"><img src="https://img.shields.io/badge/license-MIT-blue.svg" alt="MIT License"></a>
  <a href="https://github.com/lfglabs-dev/verity"><img src="https://img.shields.io/badge/built%20with-Lean%204-blueviolet.svg" alt="Built with Lean 4"></a>
  <a href="https://github.com/lfglabs-dev/verity/blob/main/docs/VERIFICATION_STATUS.md"><img src="https://img.shields.io/badge/verification%20status-live-brightgreen.svg" alt="Verification status"></a>
  <a href="https://github.com/lfglabs-dev/verity/actions"><img src="https://img.shields.io/github/actions/workflow/status/lfglabs-dev/verity/verify.yml?label=verify" alt="Verify"></a>
</p>

---

Verity is a **formally verified smart contract compiler** written in [Lean 4](https://lean-lang.org/). Write contracts in an embedded DSL, state what they should do, prove the specs hold, and compile to EVM bytecode — with machine-checked proofs that compilation preserves semantics.

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

## How it works

```
verity_contract Counter where     -- 1. Write a contract
  storage count : Uint256 := slot 0
  function increment () : Unit := do
    let current <- getStorage count
    setStorage count (add current 1)
```

```lean
-- 2. Prove a spec
theorem increment_meets_spec (s : ContractState) :
    let s' := ((increment).run s).snd
    s'.storage 0 = add (s.storage 0) 1 := by rfl
```

```
EDSL (Lean)  ->  CompilationModel  ->  IR  ->  Yul  ->  EVM bytecode
   Layer 1 [proven]    Layer 2 [proven]   Layer 3 [proven]   solc [trusted]
```

Layer 2 now has a generic whole-contract theorem for the explicit supported fragment. Layer 2: CompilationModel → IR        [GENERIC WHOLE-CONTRACT THEOREM] — its function-level closure now runs by theorem rather than axiom. There are currently 0 documented Lean axioms. Layer 3 keeps its remaining dispatch bridge as an explicit theorem hypothesis rather than a Lean axiom.

See [TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md) and [AXIOMS.md](AXIOMS.md) for the full trust boundary.

## Quick start

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.elan/env
git clone https://github.com/lfglabs-dev/verity.git && cd verity
lake build                        # verify all proofs
lake exe verity-compiler --manifest packages/verity-examples/contracts.manifest
FOUNDRY_PROFILE=difftest forge test
```

## How Verity compares

| | Certora | Halmos | Verity |
|---|---|---|---|
| **Approach** | Bounded model checking | Symbolic execution | Interactive theorem proving |
| **Compiler trust** | Trusts solc entirely | Trusts solc entirely | Verifies 3 compilation layers |
| **Best for** | Production audits at scale | Bug-finding in Foundry | High-assurance contracts |

## Documentation

| Resource | Link |
|----------|------|
| Full docs site | [verity.thomas.md](https://verity.thomas.md/) |
| Verification status | [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md) |
| Trust boundaries | [TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md) |
| Axioms | [AXIOMS.md](AXIOMS.md) |
| Research | [lfglabs.dev/verity](https://www.lfglabs.dev/verity) |
| Contributing | [CONTRIBUTING.md](CONTRIBUTING.md) |

## Project structure

```
verity/
├── Verity/              # EDSL framework (core types, macro, stdlib)
├── Contracts/           # Verified contract implementations + specs + proofs
├── Compiler/            # Compilation pipeline + proofs (Layers 1-3)
├── packages/            # Independent sub-packages
├── test/                # Foundry tests
├── scripts/             # CI validation and tooling
└── docs-site/           # Published documentation site
```

## License

MIT — See [LICENSE.md](LICENSE.md).
