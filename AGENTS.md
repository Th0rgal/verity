# DumbContracts TLDR

DumbContracts is a Lean 4 project for writing smart contracts in a small EDSL, proving their behavior in Lean, and compiling verified specs to Yul/EVM bytecode. The repo includes:

- A minimal contract DSL in `DumbContracts/` with executable semantics and proof-friendly lemmas.
- Declarative compiler specs and an IR/Yul compiler in `Compiler/` (see `Compiler/Specs.lean`).
- User-facing specs in `DumbContracts/Specs/`, implementations in `DumbContracts/Examples/`, and local proofs in `DumbContracts/Specs/<Name>/Proofs.lean`.
- Reusable proof infrastructure in `DumbContracts/Proofs/Stdlib/` (spec semantics + automation lemmas).
- Machine-checked compiler proofs for IR generation and Yul codegen in `Compiler/Proofs/`.
- Solidity/Yul fixtures in `compiler/` and Foundry tests in `test/` (including property and differential tests).

Start with `README.md` for the high-level tour and `Compiler/Proofs/README.md` for proof structure.
