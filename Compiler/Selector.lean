/-
  Compiler.Selector: Function Selector Computation

  Implements Solidity-compatible function selector generation.
  Selector = keccak256("functionName(type1,type2,...)")[0:4]

  Since Lean doesn't have built-in keccak256, we'll use a lookup table
  for now with pre-computed selectors from the manual translations.

  TODO: Integrate proper keccak256 implementation for full automation.
-/

namespace Compiler.Selector

import Compiler.IR

open Compiler

-- Solidity type signatures for function selector computation
private def typeSignature : IRType → String
  | IRType.uint256 => "uint256"
  | IRType.address => "address"
  | IRType.unit => ""  -- unit doesn't appear in signatures

-- Generate function signature string for selector computation
def functionSignature (name : String) (params : List IRParam) : String :=
  let paramTypes := params.map (fun p => typeSignature p.ty)
  name ++ "(" ++ String.intercalate "," paramTypes ++ ")"

-- Pre-computed selectors from Solidity (from manual Translate.lean)
-- These are the actual keccak256 results
private def knownSelectors : List (String × Nat) := [
  -- SimpleStorage
  ("store(uint256)", 0x6057361d),
  ("retrieve()", 0x2e64cec1),
  -- Counter
  ("increment()", 0xd09de08a),
  ("decrement()", 0x2baeceb7),
  ("getCount()", 0xa87d942c),
  -- Owned
  ("transferOwnership(address)", 0xf2fde38b),
  ("getOwner()", 0x893d20e8),
  -- Ledger
  ("deposit(uint256)", 0xb6b55f25),
  ("withdraw(uint256)", 0x2e1a7d4d),
  ("transfer(address,uint256)", 0xa9059cbb),
  ("getBalance(address)", 0xf8b2cb4f),
  -- SimpleToken
  ("mint(address,uint256)", 0x40c10f19),
  ("balanceOf(address)", 0x70a08231),
  ("totalSupply()", 0x18160ddd),
  ("owner()", 0x8da5cb5b)
]

-- Lookup selector from pre-computed table
def lookupSelector (sig : String) : Option Nat :=
  knownSelectors.find? (fun (s, _) => s == sig) |>.map (·.2)

-- Get selector for a function (PANICS if not in lookup table)
def getSelector (name : String) (params : List IRParam) : Nat :=
  let sig := functionSignature name params
  match lookupSelector sig with
  | some sel => sel
  | none => panic! s!"Selector not found for '{sig}'. Add to knownSelectors table or integrate keccak256."

-- Validate that provided selector matches expected signature
def validateSelector (name : String) (params : List IRParam) (providedSelector : Nat) : Bool :=
  let sig := functionSignature name params
  match lookupSelector sig with
  | some expectedSel => expectedSel == providedSelector
  | none => false  -- Unknown signature, can't validate

end Compiler.Selector
