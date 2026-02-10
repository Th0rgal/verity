# Dumb Contracts

**Minimal Lean 4 EDSL for Smart Contracts with Formal Verification**

[![Build](https://img.shields.io/badge/build-passing-brightgreen)]()
[![Lean](https://img.shields.io/badge/lean-4.15.0-blue)]()
[![License](https://img.shields.io/badge/license-MIT-blue)]()

> *From runtime testing to mathematical proof*

## What Makes This Different?

**Dumb Contracts** combines minimalism with mathematical rigor:

- **🎯 Minimal Core**: Just **82 lines** of Lean code
- **✅ Proven Correct**: Machine-checked formal proofs, not just tests
- **🔬 Research-Driven**: 7 iterations documenting every design decision
- **🧩 Composable**: Patterns naturally combine without special support
- **📊 Well-Tested**: 62 runtime tests + 11 formal proofs

## The Value Proposition

### Before: Runtime Testing Only
```lean
def store (value : Uint256) : Contract Unit := ...
def retrieve : Contract Uint256 := ...
```
✅ 4 Foundry tests pass
✅ 256 fuzz runs
❓ *"Is it correct?"* → **High confidence**

### Now: Testing + Formal Verification
```lean
theorem store_retrieve_correct (s : ContractState) (value : Uint256) :
  let s' := (store value).run s |>.2
  let result := retrieve.run s' |>.1
  result = value := by
  -- Proof here
```
✅ 4 Foundry tests pass
✅ 256 fuzz runs
✅ **11 theorems proven**
❓ *"Is it correct?"* → **Mathematical certainty**

## Quick Start

### See It In Action

```lean
-- SimpleStorage contract
def storedData : StorageSlot Uint256 := ⟨0⟩

def store (value : Uint256) : Contract Unit := do
  setStorage storedData value

def retrieve : Contract Uint256 := do
  getStorage storedData

-- PROVEN: After storing v, retrieve returns v
theorem store_retrieve_correct (s : ContractState) (value : Uint256) :
  let s' := (store value).run s |>.2
  let result := retrieve.run s' |>.1
  result = value := by
  -- Machine-checked proof
```

### Build & Verify

```bash
# Build Lean project (includes verification)
lake build

# Run runtime tests
forge test

# All examples evaluate
lake build  # Shows #eval outputs
```

## Architecture: Three Layers

```
DumbContracts/
├── Examples/           # 🔧 Implementations (82-line core)
│   ├── SimpleStorage   # Basic state management
│   ├── Counter         # Arithmetic operations
│   ├── Owned           # Access control
│   └── SimpleToken     # Full token contract
│
├── Specs/             # 📐 Formal specifications
│   └── SimpleStorage/
│       ├── Spec.lean        # What it should do
│       └── Invariants.lean  # What must always hold
│
└── Proofs/            # ✓ Machine-checked proofs
    └── SimpleStorage/
        └── Basic.lean       # 11 proven theorems
```

**Clean separation**: Implementation, specification, and proofs never mix.

## Proven Properties

### SimpleStorage (11 theorems ✓)

**Basic Correctness:**
- ✅ `store_retrieve_correct` - Store then retrieve returns the stored value
- ✅ `store_meets_spec` - Store satisfies its specification
- ✅ `retrieve_meets_spec` - Retrieve satisfies its specification

**Isolation:**
- ✅ `setStorage_preserves_other_slots` - No interference between slots
- ✅ `setStorage_preserves_addr_storage` - Type isolation maintained
- ✅ `setStorage_preserves_map_storage` - Mapping storage untouched

**State Preservation:**
- ✅ `store_preserves_wellformedness` - Well-formed state maintained
- ✅ `retrieve_preserves_state` - Read operations don't modify state

[See VERIFICATION_ITERATION_1_SUMMARY.md for details]

## Examples: From Simple to Complex

| Contract | Lines | Tests | Proofs | Description |
|----------|-------|-------|--------|-------------|
| **SimpleStorage** | 38 | 4 | ✅ 11 | Basic state management |
| **Counter** | 50 | 7 | 🔄 Next | Arithmetic operations |
| **Owned** | 59 | 8 | 🔜 Soon | Access control |
| **OwnedCounter** | 80 | 11 | 🔜 Soon | Pattern composition |
| **Ledger** | 70 | 11 | 🔜 Soon | Mapping storage |
| **SimpleToken** | 96 | 12 | 🔜 Soon | Full ERC20-like token |

**Total:** 7 contracts, 62 tests (100% passing), 11 proofs (100% verified)

## Core API: Type-Safe by Design

```lean
-- Types
abbrev Address := String
abbrev Uint256 := Nat
structure StorageSlot (α : Type)
abbrev Contract (α : Type) := StateM ContractState α

-- Storage operations (type-safe!)
def getStorage : StorageSlot Uint256 → Contract Uint256
def setStorage : StorageSlot Uint256 → Uint256 → Contract Unit
def getMapping : StorageSlot (Address → Uint256) → Address → Contract Uint256

-- Context
def msgSender : Contract Address
def contractAddress : Contract Address

-- Guards
def require : Bool → String → Contract Unit
```

**Type safety prevents errors at compile-time:**
```lean
def owner : StorageSlot Address := ⟨0⟩
def count : StorageSlot Uint256 := ⟨1⟩

let x ← getStorage owner    -- ❌ Compile error! owner is Address, not Uint256
let x ← getStorageAddr owner -- ✅ Correct
```

## Research: Documented Design Decisions

Every choice is documented with:
- ✅ What was tried
- ✅ What worked / didn't work
- ✅ Why this approach was chosen
- ✅ Metrics and evidence

See:
- **RESEARCH.md** - Complete 7-iteration research log
- **ITERATION_*_SUMMARY.md** - Detailed iteration summaries
- **VERIFICATION_ITERATION_1_SUMMARY.md** - Verification details

## Project Philosophy

### Minimalism
- **82-line core** - Only essentials
- **4 out of 7 iterations** needed zero core changes
- **Example-driven** - Only add what examples need

### Rigor
- **Separation of concerns** - Specs, implementations, proofs separate
- **Incremental verification** - Start simple, build up
- **Document everything** - Every decision explained

### Practicality
- **Real contracts** - SimpleToken is deployable
- **Runtime testing** - Foundry validates behavior
- **Formal proofs** - Lean validates correctness

## Verification Roadmap

- [x] **SimpleStorage** - 11 theorems proven
- [ ] **Counter** - Arithmetic correctness
- [ ] **Owned** - Access control guarantees
- [ ] **SimpleToken** - Complex invariants (supply = Σ balances)

## Getting Started

### Prerequisites

- [Lean 4](https://leanprover.github.io/) (4.15.0+)
- [Foundry](https://getfoundry.sh/) (for testing)

### Installation

```bash
# Clone repository
git clone https://github.com/Th0rgal/dumbcontracts.git
cd dumbcontracts

# Build Lean project
lake build

# Run tests
forge test
```

### Writing Your First Verified Contract

1. **Write implementation** in `DumbContracts/Examples/`
2. **Write specification** in `DumbContracts/Specs/`
3. **Prove properties** in `DumbContracts/Proofs/`
4. **Test runtime behavior** in `test/`

See `VERIFICATION_ITERATION_1_SUMMARY.md` for a complete example.

## Documentation

- 📖 **[Research Log](RESEARCH.md)** - Complete design history
- 📊 **[Iteration Summaries](ITERATION_*_SUMMARY.md)** - Detailed breakdowns
- ✓ **[Verification Summary](VERIFICATION_ITERATION_1_SUMMARY.md)** - Proof details
- 🌐 **[Docs Website](docs-site/)** - AI-friendly documentation

## Contributing

This is a research project exploring:
- How minimal can a practical EDSL be?
- How to verify smart contracts incrementally?
- What proof patterns work well in Lean 4?

Contributions welcome! See current research goals in `STATUS.md`.

## Key Achievements

🎯 **Minimalism Validated**
- 82-line core sufficient for realistic contracts
- 4/7 iterations with zero core changes

✅ **Verification Established**
- 11 theorems proven for SimpleStorage
- Clear path to verifying complex contracts

🧩 **Composability Proven**
- Patterns combine naturally (OwnedCounter, SimpleToken)
- No special composition support needed

📊 **Well-Tested**
- 62 Foundry tests (100% passing)
- 2,816 fuzz runs
- 11 formal proofs

## License

MIT License - See [LICENSE](LICENSE) for details

---

**Built with ❤️ using Lean 4**

*From runtime confidence to mathematical certainty*
