# Dumb Contracts: Lean to Yul Compiler Mission

You are building a minimal compiler that translates DumbContracts Lean EDSL definitions into Yul (EVM intermediate representation). The goal is human-readable, auditable Yul output, not performance.

## What exists

The project has:

- **7 Lean contracts** in `DumbContracts/Examples/` (SimpleStorage, Counter, SafeCounter, Owned, OwnedCounter, Ledger, SimpleToken)
- **7 matching Solidity contracts** in `contracts/` with Foundry tests in `test/`
- **A Lean 4 build** (v4.15.0, no Mathlib) with `~/.elan/bin/lake build`
- **A Foundry setup** with `forge test` to run the Solidity tests

The Lean EDSL core (`DumbContracts/Core.lean`, 212 lines) defines exactly these primitives:

| Primitive | Type | Yul equivalent |
|-----------|------|----------------|
| `getStorage slot` | `Contract Uint256` | `sload(slot)` |
| `setStorage slot value` | `Contract Unit` | `sstore(slot, value)` |
| `getStorageAddr slot` | `Contract Address` | `sload(slot)` |
| `setStorageAddr slot value` | `Contract Unit` | `sstore(slot, value)` |
| `getMapping slot key` | `Contract Uint256` | `sload(keccak256(key, slot))` |
| `setMapping slot key value` | `Contract Unit` | `sstore(keccak256(key, slot), value)` |
| `msgSender` | `Contract Address` | `caller()` |
| `require cond msg` | `Contract Unit` | `if iszero(cond) { revert(...) }` |
| `pure a` | `Contract a` | value on stack |
| `bind ma f` | `Contract b` | sequencing (do-notation) |

Additional: `Stdlib/Math.lean` defines `safeAdd`, `safeSub`, `safeMul`, `safeDiv` (checked arithmetic returning `Option`) and `requireSomeUint` (unwrap or revert).

Types: `Uint256 := Nat`, `Address := String`. On EVM, both are 256-bit words. Addresses are 160-bit but stored in 256-bit slots.

## What to build

A Lean program that reads a contract definition and emits a `.yul` file. The compiler lives in a new `Compiler/` directory alongside the existing `DumbContracts/` code.

### Scope

Compile these contracts in order (each one adds a feature):

1. **SimpleStorage** -- `getStorage`, `setStorage`, function dispatch
2. **Counter** -- arithmetic (`add`, `sub`), read-modify-write
3. **Owned** -- `getStorageAddr`, `setStorageAddr`, `msgSender`, `require`
4. **OwnedCounter** -- composition of Owned + Counter patterns
5. **Ledger** -- `getMapping`, `setMapping` (keccak256 slot computation)
6. **SimpleToken** -- everything combined (owner, mappings, require, arithmetic)
7. **SafeCounter** -- checked arithmetic (`safeAdd`/`safeSub` + `requireSomeUint`)

### Out of scope

- Optimization (readable output is the goal)
- Events/logs
- Constructor arguments from calldata (constructors can be hardcoded or skipped)
- Payable functions / msg.value
- Gas tracking
- Nested mappings
- Compiler verification proofs (future work)

## Architecture

```
Compiler/
  Yul/
    Ast.lean          -- Yul AST types
    PrettyPrint.lean  -- Yul AST -> String
  IR.lean             -- Intermediate representation
  Translate.lean      -- Lean EDSL -> IR
  Codegen.lean        -- IR -> Yul AST
  Main.lean           -- Entry point, emit .yul files
```

Keep it simple. The compiler does not need to parse Lean source. It can work directly with the Lean definitions at the meta level (using the existing Lean types). Each contract is compiled by a hand-written translation function that calls into shared codegen utilities.

### Yul AST

Minimal types covering what we need:

```lean
inductive YulExpr
  | lit (n : Nat)
  | ident (name : String)
  | call (func : String) (args : List YulExpr)

inductive YulStmt
  | let_ (name : String) (value : YulExpr)
  | assign (name : String) (value : YulExpr)
  | expr (e : YulExpr)
  | if_ (cond : YulExpr) (body : List YulStmt)
  | switch (expr : YulExpr) (cases : List (Nat × List YulStmt)) (default : Option (List YulStmt))
  | block (stmts : List YulStmt)
  | funcDef (name : String) (params : List String) (rets : List String) (body : List YulStmt)

structure YulObject where
  name : String
  deployCode : List YulStmt
  runtimeCode : List YulStmt
```

### Pretty printer

Emit clean, indented Yul. Example output for Counter:

```yul
object "Counter" {
    code {
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        return(0, datasize("runtime"))
    }
    object "runtime" {
        code {
            switch shr(224, calldataload(0))
            case 0xd09de08a /* increment() */ {
                let current := sload(0)
                sstore(0, add(current, 1))
                stop()
            }
            case 0x2baeceb7 /* decrement() */ {
                let current := sload(0)
                sstore(0, sub(current, 1))
                stop()
            }
            case 0xa87d942c /* getCount() */ {
                mstore(0, sload(0))
                return(0, 32)
            }
            default { revert(0, 0) }
        }
    }
}
```

### Function selectors

Compute `keccak256("functionName(types)")` truncated to 4 bytes. The selector for each public function must match Solidity's ABI encoding so that existing Foundry tests work against the compiled Yul.

Selectors for the 7 contracts:

| Contract | Function | Solidity Signature | Selector |
|----------|----------|--------------------|----------|
| SimpleStorage | store | `store(uint256)` | `0x6057361d` |
| SimpleStorage | retrieve | `retrieve()` | `0x2e64cec1` |
| Counter | increment | `increment()` | `0xd09de08a` |
| Counter | decrement | `decrement()` | `0x2baeceb7` |
| Counter | getCount | `getCount()` | `0xa87d942c` |
| Owned | constructor | (deploy only) | -- |
| Owned | transferOwnership | `transferOwnership(address)` | `0xf2fde38b` |
| Owned | getOwner | `owner()` | `0x8da5cb5b` |
| OwnedCounter | constructor | (deploy only) | -- |
| OwnedCounter | increment | `increment()` | `0xd09de08a` |
| OwnedCounter | decrement | `decrement()` | `0x2baeceb7` |
| OwnedCounter | getCount | `getCount()` | `0xa87d942c` |
| OwnedCounter | getOwner | `owner()` | `0x8da5cb5b` |
| OwnedCounter | transferOwnership | `transferOwnership(address)` | `0xf2fde38b` |
| Ledger | deposit | `deposit(uint256)` | `0xb6b55f25` |
| Ledger | withdraw | `withdraw(uint256)` | `0x2e1a7d4d` |
| Ledger | transfer | `transfer(address,uint256)` | `0xa9059cbb` |
| Ledger | getBalance | `balanceOf(address)` | `0x70a08231` |
| SimpleToken | constructor | (deploy only) | -- |
| SimpleToken | mint | `mint(address,uint256)` | `0x40c10f19` |
| SimpleToken | transfer | `transfer(address,uint256)` | `0xa9059cbb` |
| SimpleToken | balanceOf | `balanceOf(address)` | `0x70a08231` |
| SimpleToken | totalSupply | `totalSupply()` | `0x18160ddd` |
| SimpleToken | owner | `owner()` | `0x8da5cb5b` |
| SafeCounter | increment | `increment()` | `0xd09de08a` |
| SafeCounter | decrement | `decrement()` | `0x2baeceb7` |
| SafeCounter | getCount | `getCount()` | `0xa87d942c` |

You should verify these by checking against the existing Solidity ABIs (`forge inspect Counter abi`).

### Mapping slot computation

Solidity stores `mapping(address => uint256)` at slot `keccak256(abi.encode(key, baseSlot))`. In Yul:

```yul
function mappingSlot(baseSlot, key) -> slot {
    mstore(0, key)
    mstore(32, baseSlot)
    slot := keccak256(0, 64)
}
```

This matches `getMapping`/`setMapping` behavior where `slot.slot` is the base slot number.

### Calldata decoding

Parameters come from calldata after the 4-byte selector:
- `uint256` at offset 4: `calldataload(4)`
- `address` at offset 4: `and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)`
- Second param at offset 36: `calldataload(36)` (or masked for address)

### Return values

- `uint256`: `mstore(0, value)` then `return(0, 32)`
- `address`: same (ABI-encoded as 256-bit)
- `Unit` (void): `stop()`

### Revert encoding

For `require cond msg`, emit:

```yul
if iszero(cond) { revert(0, 0) }
```

Simple zero-data revert is fine for the MVP. Error strings can be added later.

### Checked arithmetic (SafeCounter)

`safeAdd(a, b)` becomes:
```yul
let result := add(a, b)
if lt(result, a) { revert(0, 0) }
```

`safeSub(a, b)` becomes:
```yul
if gt(b, a) { revert(0, 0) }
let result := sub(a, b)
```

## Testing

The existing Foundry test suite is the acceptance test. For each contract:

1. Compile the Lean contract to a `.yul` file
2. Compile the `.yul` to bytecode with `solc --strict-assembly --bin`
3. Deploy the bytecode in a Foundry test
4. Run the same test cases as the Solidity version

Create a `test/yul/` directory with comparison tests that deploy both the Solidity and Yul versions and verify identical behavior.

Start simple: manually verify that `solc --strict-assembly Counter.yul` produces valid bytecode, then write a Foundry test that deploys it and calls `increment()`.

## Iteration process

Each iteration should:

1. Pick the next contract from the list
2. Write the translation for any new primitives it uses
3. Emit the `.yul` file
4. Compile with `solc --strict-assembly`
5. Test with Foundry (or manually if tests aren't wired up yet)
6. Commit: "Compile Counter to Yul: passes all tests"

## Constraints

- **Readable output**: The generated Yul should be easy for a human to audit. Add comments with function names. Use descriptive variable names.
- **Correct over fast**: Prioritize correctness. Naive codegen is fine. No optimization passes needed.
- **Match Solidity ABI**: Function selectors and calldata encoding must match so existing tests work.
- **Minimal code**: The compiler itself should be as small and simple as possible. No frameworks, no complex abstractions.
- **Lean 4 only**: The compiler is written in Lean 4. No external dependencies beyond what Lake provides.

## Existing test baseline

62 Foundry tests across 7 contracts, all passing:

| Test Suite | Tests |
|------------|-------|
| SimpleStorageTest | 4 |
| CounterTest | 7 |
| OwnedTest | 8 |
| OwnedCounterTest | 11 |
| LedgerTest | 11 |
| SimpleTokenTest | 12 |
| SafeCounterTest | 9 |

These are the acceptance tests for the compiler output.

## Success criteria

The compiler is done when:

1. All 7 contracts compile to `.yul` files
2. Each `.yul` file compiles with `solc --strict-assembly` without errors
3. Foundry tests pass against the Yul-compiled bytecode
4. The generated Yul is readable and matches the Lean EDSL structure

## Git workflow

- Work in a branch called `compiler`
- Commit after each contract compiles and tests pass
- Push regularly
