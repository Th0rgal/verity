# External Library Examples

This directory contains example Yul library files that can be linked with Verity at compile time.

## Files

- **PoseidonT3.yul**: Placeholder Poseidon hash function for 2 inputs
- **PoseidonT4.yul**: Placeholder Poseidon hash function for 3 inputs (1 input + padding)

## TL;DR - 5 Minute Quickstart

Want to add a cryptographic hash function to your contract? Here's the minimum you need:

### Step 1: Create your Yul library (`examples/external-libs/MyHash.yul`)

```yul
function myHash(a, b) -> result {
    result := add(xor(a, b), 0x42)
}
```

### Step 2: Add the external call in `Compiler/Specs.lean`

Find your contract spec and add (`Expr.param` takes the parameter **name** as a string, matching the `name` field in your function's `params` list):
```lean
Stmt.letVar "h" (Expr.externalCall "myHash" [Expr.param "a", Expr.param "b"])
```

### Step 3: Compile with linking

```bash
lake exe verity-compiler --link examples/external-libs/MyHash.yul -o compiler/yul
```

That's it! The compiler validates your library and injects it into the generated Yul.

## Why use external libraries?

| Use Case | Example |
|----------|---------|
| Cryptographic primitives | Poseidon, SHA256, Keccak |
| Complex math | Elliptic curve operations |
| Gas optimization | Hand-optimized Yul implementations |
| Reuse audited code | Battle-tested libraries |

The key benefit: **prove with simple placeholders, deploy with real code**.

## Quick Reference

**CLI Options:**
```bash
--link <path>      # Link external Yul library (use multiple times for multiple libs)
-o <dir>           # Output directory (default: compiler/yul)
-v, --verbose      # Verbose output
```

**Error Solutions:**

| Error | Solution |
|-------|----------|
| `Unresolved external references: myFunc` | Add `--link examples/external-libs/MyFunc.yul` to your command |
| `Arity mismatch` | Check parameter count in `Expr.externalCall` matches Yul function |
| `Function shadows Yul builtin` | Rename your function (e.g., `myAdd` instead of `add`) |
| `Duplicate function names` | Each library must have unique function names |

## Step-by-Step Example

### 1. Create Your Library (e.g., `examples/external-libs/MyHash.yul`)

```yul
// Simple hash function for demonstration
function myHash(a, b) -> result {
    result := add(xor(a, b), 0x42)
}
```

### 2. Use Placeholder in Your Contract

In your EDSL contract, define a placeholder:

```lean
-- Placeholder: models the hash as addition (for proving)
def myHash (a b : Uint256) : Contract Uint256 := do
  return add a b
```

### 3. Add External Call to ContractSpec

In `Compiler/Specs.lean`, reference the library function:

```lean
Stmt.letVar "h" (Expr.externalCall "myHash" [Expr.param "a", Expr.param "b"])
```

### 4. Compile with Linking

```bash
lake exe verity-compiler --link examples/external-libs/MyHash.yul -o compiler/yul
```

## Complete Guide

For a comprehensive guide on using external libraries, see the [Linking External Libraries](../docs-site/content/guides/linking-libraries.mdx) documentation.

The guide covers:
- Writing library files
- Creating Lean placeholders
- Adding external calls to your ContractSpec
- Validation and error handling
- Trust model considerations

## Common Pitfalls

### 1. Object Wrappers Not Supported

```yul
// Bad: object wrapper will cause parsing errors
object "MyLib" {
    function foo(x) -> y { y := add(x, 1) }
}

// Good: plain function definitions
function foo(x) -> y { y := add(x, 1) }
```

### 2. Function Name Mismatch

The function name in your `.yul` file must exactly match what's called in your ContractSpec:

```yul
// In MyHash.yul
function myHash(a, b) -> result { ... }  // Name is "myHash"
```

```lean
-- In Specs.lean - must match exactly
Expr.externalCall "myHash" [...]  -- Must be "myHash", not "MyHash" or "my_hash"
```

### 3. Parameter Count Mismatch

If your Yul function expects 2 parameters but you call it with 3, you'll get an arity error:

```
Arity mismatch: myHash called with 3 args but library defines 2 params
```

### 4. Shadowing Builtins

Don't use names that conflict with Yul builtins:

```yul
// Bad: "add" is a Yul builtin
function add(a, b) -> result { result := a }

// Good: unique names
function myAdd(a, b) -> result { result := a }
```

## Validation

The Linker performs several safety checks (see `Compiler/Linker.lean`):

1. **Duplicate names**: Detects if two libraries define the same function
2. **Name collisions**: Catches libraries that shadow generated code or Yul builtins
3. **External references**: Ensures all function calls are resolved by linked libraries
4. **Arity matching**: Validates that call sites match library function signatures

If validation fails, you'll get clear error messages:

```
Unresolved external references: myHash
Library function(s) shadow Yul builtins: add
Arity mismatch: myFunc called with 2 args but library defines 3 params
```

## Production Use

These are **placeholder implementations** for demonstration purposes. In production, use:

1. Real Poseidon hash implementations from audited libraries (e.g., [HorizenLabs](https://github.com/HorizenLabs/poseidon))
2. Groth16 verification functions from audited zk-SNARK libraries
3. Other cryptographic primitives from trusted sources

The key benefit: prove properties about contract logic using simple placeholders, then link production-grade implementations at compile time.

## Trust Model

External libraries are **outside the formal verification boundary**. Your Lean proofs verify the contract logic against placeholders. You must:

1. Use audited, battle-tested library implementations
2. Add Foundry tests that exercise linked contracts end-to-end
3. Document the trust assumption (see [TRUST_ASSUMPTIONS.md](../TRUST_ASSUMPTIONS.md#5-external-library-code-linker))

## Related Files

- [CryptoHash Example](../Verity/Examples/CryptoHash.lean) - Shows placeholder usage
- [Linker Module](../Compiler/Linker.lean) - Full linker implementation
- [ContractSpec](../Compiler/ContractSpec.lean) - External call syntax
