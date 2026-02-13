# Dumb Contracts

DumbContracts is a Lean 4 project for writing smart contracts in a tiny EDSL, proving their behavior in Lean, and compiling verified specs to Yul/EVM bytecode. It contains executable semantics, a compiler pipeline, and machine-checked proofs across the EDSL, IR generation, and Yul codegen.

## Example

```lean
-- Implementation
def storedData : StorageSlot Uint256 := ⟨0⟩

def store (value : Uint256) : Contract Unit := do
  setStorage storedData value

def retrieve : Contract Uint256 := do
  getStorage storedData

-- Proof: retrieve returns what store stored
theorem store_retrieve_correct (s : ContractState) (value : Uint256) :
  let s' := ((store value).run s).snd
  let result := ((retrieve).run s').fst
  result = value := by
  have h_store := store_meets_spec s value
  have h_retrieve := retrieve_meets_spec ((store value).run s |>.2)
  simp [store_spec] at h_store
  simp [retrieve_spec] at h_retrieve
  simp only [h_retrieve, h_store.1]
```

## What’s Verified

- **EDSL correctness**: Each example contract satisfies its specification in Lean.
- **Spec semantics**: ContractSpec execution matches the intended DSL behavior.
- **Compiler correctness**: IR generation and Yul codegen preserve semantics.
- **Automation**: Common proof patterns are captured in reusable lemmas.

See `Compiler/Proofs/README.md` for the proof inventory and layout across layers.

## Assumptions and Trust Model

These are the remaining trusted components outside Lean:

- **`solc` Yul compiler**: The Solidity compiler is trusted to compile Yul to EVM bytecode.
- **EVM semantics**: The EVM execution model is assumed to match the specification used in proofs.
- **Function selectors**: Precomputed `keccak256` hashes in `Compiler/Selector.lean` are assumed correct.

Semantics are defined in Lean here:

- EDSL semantics: `DumbContracts/Core.lean`
- Spec semantics: `DumbContracts/Proofs/Stdlib/SpecInterpreter.lean`
- IR semantics: `Compiler/Proofs/IRGeneration/IRInterpreter.lean`
- Yul semantics: `Compiler/Proofs/YulGeneration/Semantics.lean`

## Repository Structure

```
DumbContracts/                       # EDSL core + stdlib + examples/specs/proofs
Compiler/                            # Compiler (spec DSL, IR, codegen, selector, Yul AST)
Compiler/Proofs/                     # Compiler correctness proofs (3 layers)
compiler/                            # Generated Yul output + fixtures (used in tests/docs)
docs/                                # Design notes and verification summaries
docs-site/                           # Documentation site (MDX)
examples/solidity/                   # Solidity/Yul fixtures and test outputs
scripts/                             # build/test scripts
test/                                # Foundry tests (unit, property, differential)
```

## Where Things Live (Spec → Impl → Proof)

- **User-facing specs**: `DumbContracts/Specs/<Name>/Spec.lean` (+ `Invariants.lean`)
- **Implementations (EDSL)**: `DumbContracts/Examples/<Name>.lean`
- **User-facing proofs**: `DumbContracts/Specs/<Name>/Proofs.lean`
- **Reusable proof infrastructure**: `DumbContracts/Proofs/Stdlib/` (spec interpreter + automation)
- **Compiler specs (for codegen)**: `Compiler/Specs.lean` (separate from user specs)
- **Compiler proofs**: `Compiler/Proofs/` (IR generation + Yul preservation)

## Examples and Proofs

- **Lean examples (EDSL implementations)**: `DumbContracts/Examples/`
- **Specifications + invariants + Layer 1 proofs**: `DumbContracts/Specs/`
- **Contract-level proofs (EDSL properties)**: `DumbContracts/Proofs/`
- **Compiler proofs**: `Compiler/Proofs/` (Layer 1 infra, Layer 2: IR, Layer 3: Yul)

## Build and Test

```bash
# Type-check DumbContracts (EDSL + proofs)
lake build

# Build compiler executable
lake build dumbcontracts-compiler

# Run Foundry tests (unit + property + differential)
forge test
```

## Documentation

- `Compiler/Proofs/README.md` — Proof structure and navigation
- `docs-site/` — Documentation website (MDX)
- Roadmap, milestones, and progress updates: `docs-site/content/research.mdx` and `docs-site/content/research/iterations.mdx`

## License

MIT
