# External Library Examples

This directory contains example Yul library files that can be linked with Verity at compile time.

## Files

- **PoseidonT3.yul**: Placeholder Poseidon hash function for 2 inputs
- **PoseidonT4.yul**: Placeholder Poseidon hash function for 3 inputs

## Usage

Compile a contract with external library linking:

```bash
lake exec verity-compiler \
    --link examples/external-libs/PoseidonT3.yul \
    --link examples/external-libs/PoseidonT4.yul \
    -o compiler/yul
```

## Note

These are **placeholder implementations** for demonstration purposes. In production, you would use:

1. Real Poseidon hash implementations from audited libraries
2. Groth16 verification functions from audited zk-SNARK libraries
3. Other cryptographic primitives from trusted sources

The key benefit is that you can prove properties about your contract logic using simple placeholders in Lean, then link with production-grade cryptographic implementations at compile time.
