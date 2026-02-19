/-
  Compiler.RandomGen: Random Transaction Generator

  Generates random but valid transactions for differential testing.
  Uses a simple pseudo-random number generator for reproducibility.
-/

import Verity.Core
import Compiler.DiffTestTypes
import Compiler.Hex

namespace Compiler.RandomGen

open Verity
open Compiler.DiffTestTypes
open Compiler.Hex

/-!
## SplitMix64 PRNG

64-bit SplitMix generator for reproducible randomness with good
distribution properties.  Replaces the previous 31-bit LCG which had
only 2^31 distinct states and poor high-bit distribution.

Reference: Steele, Lea & Flood, "Fast Splittable Pseudorandom Number
Generators", OOPSLA 2014.
-/

structure RNG where
  seed : Nat
  deriving Repr

private def mask64 : Nat := 2^64 - 1

/-- Advance the state by the SplitMix64 golden-gamma increment and
    mix the result through two xor-shift-multiply rounds. -/
def RNG.next (rng : RNG) : RNG × Nat :=
  let s := (rng.seed + 0x9e3779b97f4a7c15) &&& mask64
  let z := s
  let z := ((z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9) &&& mask64
  let z := ((z ^^^ (z >>> 27)) * 0x94d049bb133111eb) &&& mask64
  let z := z ^^^ (z >>> 31)
  ({ seed := s }, z)

def RNG.init (seed : Nat) : RNG := { seed := seed &&& mask64 }

/-!
## Random Value Generation

Values are drawn from a mix of edge cases and bounded random values
so that differential tests exercise overflow, underflow, and boundary
conditions alongside typical small-value scenarios.  The generator
covers the full uint256 range via multiple draws.
-/

-- Edge-case uint256 values that trigger overflow/underflow/boundary bugs
private def edgeUint256Values : List Nat :=
  [ 0
  , 1
  , 2
  , 255                  -- max uint8
  , 256                  -- 2^8
  , 2^16 - 1             -- max uint16
  , 2^128                -- midpoint
  , 2^128 - 1
  , 2^255                -- high bit
  , 2^255 - 1
  , 2^256 - 2            -- type(uint256).max - 1
  , 2^256 - 1            -- type(uint256).max
  ]

/-- Build a full-range 256-bit value from four 64-bit draws. -/
private def gen256Bits (rng : RNG) : RNG × Nat :=
  let (rng, a) := rng.next
  let (rng, b) := rng.next
  let (rng, c) := rng.next
  let (rng, d) := rng.next
  (rng, ((a &&& mask64) <<< 192) + ((b &&& mask64) <<< 128)
      + ((c &&& mask64) <<< 64) + (d &&& mask64))

/-- Generate random uint256 with mixed distribution.
    Distribution (by selector mod 32):
      0..11  → deterministic edge-case value
      12..19 → small value 0..999_999 (typical amounts)
      20..23 → medium value 0..2^128 (intermediate range)
      24..31 → full-range 256-bit value (overflow/wrapping territory) -/
def genUint256 (rng : RNG) : RNG × Nat :=
  let (rng, n) := rng.next
  let selector := n % 32
  match edgeUint256Values.get? selector with
  | some v =>
    -- Deterministic edge case
    (rng, v)
  | none =>
    if selector < 20 then
      -- Small value band
      let (rng, v) := rng.next
      (rng, v % 1000000)
    else if selector < 24 then
      -- Medium value band (up to 2^128)
      let (rng, v) := rng.next
      let (rng, w) := rng.next
      (rng, ((v &&& mask64) <<< 64) + (w &&& mask64))
    else
      -- Full 256-bit range
      gen256Bits rng

-- Convert Address to Nat for calldata args (keeps parity with Interpreter)
private def addressToNatNormalized (addr : Address) : Nat :=
  addr.val

-- Address pool including edge-case addresses (zero address, high address)
private def addressPool : List Address :=
  [ Verity.Core.Address.ofNat 0xa11ce
  , Verity.Core.Address.ofNat 0xb0b
  , Verity.Core.Address.ofNat 0xca201
  , Verity.Core.Address.ofNat 0xdave
  , Verity.Core.Address.ofNat 0xeve
  , (0 : Address)                                                  -- zero address
  , Verity.Core.Address.ofNat (2^160 - 1)                         -- max address
  , Verity.Core.Address.ofNat 1                                    -- address(1)
  ]

-- Generate random address from an expanded pool that includes edge cases
def genAddress (rng : RNG) : RNG × Address :=
  let (rng', n) := rng.next
  let addr := match addressPool.get? (n % addressPool.length) with
    | some a => a
    | none   => (0 : Address)  -- fallback; unreachable when addressPool is non-empty
  (rng', addr)

-- Generate random bool
def genBool (rng : RNG) : RNG × Bool :=
  let (rng', n) := rng.next
  (rng', n % 2 == 0)

/-!
## Contract-Specific Transaction Generation
-/

-- Generate random SimpleStorage transaction
def genSimpleStorageTx (rng : RNG) : RNG × Transaction :=
  let (rng, sender) := genAddress rng
  let (rng, useStore) := genBool rng
  if useStore then
    let (rng, value) := genUint256 rng
    (rng, { sender := sender, functionName := "store", args := [value] })
  else
    (rng, { sender := sender, functionName := "retrieve", args := [] })

-- Generate random Counter transaction
def genCounterTx (rng : RNG) : RNG × Transaction :=
  let (rng, sender) := genAddress rng
  let (rng, choice) := genUint256 rng
  match choice % 3 with
  | 0 => (rng, { sender := sender, functionName := "increment", args := [] })
  | 1 => (rng, { sender := sender, functionName := "decrement", args := [] })
  | _ => (rng, { sender := sender, functionName := "getCount", args := [] })

-- Generate random SafeCounter transaction
def genSafeCounterTx (rng : RNG) : RNG × Transaction :=
  genCounterTx rng

-- Generate random Owned transaction
def genOwnedTx (rng : RNG) : RNG × Transaction :=
  let (rng, sender) := genAddress rng
  let (rng, choice) := genUint256 rng
  if choice % 2 == 0 then
    (rng, { sender := sender, functionName := "getOwner", args := [] })
  else
    let (rng, newOwner) := genAddress rng
    (rng, { sender := sender, functionName := "transferOwnership", args := [addressToNatNormalized newOwner] })

-- Generate random Ledger transaction
def genLedgerTx (rng : RNG) : RNG × Transaction :=
  let (rng, sender) := genAddress rng
  let (rng, choice) := genUint256 rng
  match choice % 4 with
  | 0 =>
      let (rng, amount) := genUint256 rng
      (rng, { sender := sender, functionName := "deposit", args := [amount] })
  | 1 =>
      let (rng, amount) := genUint256 rng
      (rng, { sender := sender, functionName := "withdraw", args := [amount] })
  | 2 =>
      let (rng, toAddr) := genAddress rng
      let (rng, amount) := genUint256 rng
      (rng, { sender := sender, functionName := "transfer", args := [addressToNatNormalized toAddr, amount] })
  | _ =>
      let (rng, addr) := genAddress rng
      (rng, { sender := sender, functionName := "getBalance", args := [addressToNatNormalized addr] })

-- Generate random OwnedCounter transaction
def genOwnedCounterTx (rng : RNG) : RNG × Transaction :=
  let (rng, sender) := genAddress rng
  let (rng, choice) := genUint256 rng
  match choice % 5 with
  | 0 => (rng, { sender := sender, functionName := "increment", args := [] })
  | 1 => (rng, { sender := sender, functionName := "decrement", args := [] })
  | 2 => (rng, { sender := sender, functionName := "getCount", args := [] })
  | 3 => (rng, { sender := sender, functionName := "getOwner", args := [] })
  | _ =>
      let (rng, newOwner) := genAddress rng
      (rng, { sender := sender, functionName := "transferOwnership", args := [addressToNatNormalized newOwner] })

-- Generate random SimpleToken transaction
def genSimpleTokenTx (rng : RNG) : RNG × Transaction :=
  let (rng, sender) := genAddress rng
  let (rng, choice) := genUint256 rng
  match choice % 5 with
  | 0 =>
      let (rng, toAddr) := genAddress rng
      let (rng, amount) := genUint256 rng
      (rng, { sender := sender, functionName := "mint", args := [addressToNatNormalized toAddr, amount] })
  | 1 =>
      let (rng, toAddr) := genAddress rng
      let (rng, amount) := genUint256 rng
      (rng, { sender := sender, functionName := "transfer", args := [addressToNatNormalized toAddr, amount] })
  | 2 =>
      let (rng, addr) := genAddress rng
      (rng, { sender := sender, functionName := "balanceOf", args := [addressToNatNormalized addr] })
  | 3 =>
      (rng, { sender := sender, functionName := "totalSupply", args := [] })
  | _ =>
      (rng, { sender := sender, functionName := "owner", args := [] })

-- Generate random block timestamp (range: 0 to ~year 2100 in seconds)
def genTimestamp (rng : RNG) : RNG × Nat :=
  let (rng', n) := rng.next
  (rng', n % 4102444800)

-- Generate random transaction for any contract
-- Attaches a random blockTimestamp to each transaction.
-- msgValue is 0 for all current contracts (none are payable).
def genTransaction (contractType : ContractType) (rng : RNG) : Except String (RNG × Transaction) :=
  let (rng, timestamp) := genTimestamp rng
  let result := match contractType with
  | ContractType.simpleStorage => Except.ok (genSimpleStorageTx rng)
  | ContractType.counter => Except.ok (genCounterTx rng)
  | ContractType.safeCounter => Except.ok (genSafeCounterTx rng)
  | ContractType.owned => Except.ok (genOwnedTx rng)
  | ContractType.ledger => Except.ok (genLedgerTx rng)
  | ContractType.ownedCounter => Except.ok (genOwnedCounterTx rng)
  | ContractType.simpleToken => Except.ok (genSimpleTokenTx rng)
  result.map fun (rng', tx) => (rng', { tx with blockTimestamp := timestamp })

/-!
## Generate Test Sequence
-/

-- Generate N random transactions
def genTransactions (contractType : ContractType) (count : Nat) (rng : RNG) : Except String (List Transaction) :=
  match count with
  | 0 => Except.ok []
  | n + 1 =>
    match genTransaction contractType rng with
    | Except.error msg => Except.error msg
    | Except.ok (rng', tx) =>
        match genTransactions contractType n rng' with
        | Except.ok rest => Except.ok (tx :: rest)
        | Except.error msg => Except.error msg

-- Generate test sequence with a seed
def genTestSequence (contractType : ContractType) (count : Nat) (seed : Nat) : Except String (List Transaction) :=
  let rng := RNG.init seed
  genTransactions contractType count rng

end Compiler.RandomGen

/-!
## CLI Entry Point

For generating test sequences from command line.
-/

open Compiler.RandomGen
open Compiler.DiffTestTypes

def main (args : List String) : IO Unit := do
  match args with
  | [contractType, countStr, seedStr] =>
    let count := match countStr.toNat? with
      | some n => n
      | none => throw <| IO.userError s!"Invalid count: {countStr}"
    let seed := match seedStr.toNat? with
      | some n => n
      | none => throw <| IO.userError s!"Invalid seed: {seedStr}"
    let contractTypeEnum? : Option ContractType := match contractType with
      | "SimpleStorage" => some ContractType.simpleStorage
      | "Counter" => some ContractType.counter
      | "Owned" => some ContractType.owned
      | "Ledger" => some ContractType.ledger
      | "OwnedCounter" => some ContractType.ownedCounter
      | "SimpleToken" => some ContractType.simpleToken
      | "SafeCounter" => some ContractType.safeCounter
      | _ => none
    match contractTypeEnum? with
    | some contractTypeEnum =>
      match genTestSequence contractTypeEnum count seed with
      | Except.error msg =>
          throw <| IO.userError msg
      | Except.ok txs =>
          -- Output as JSON array
          IO.println "["
          let mut isFirst := true
          for tx in txs do
            if !isFirst then IO.println ","
            let argsStr := String.intercalate "," (tx.args.map toString)
            let jsonStr := "  {" ++ "\"sender\":\"" ++ toString tx.sender.val ++ "\",\"function\":\"" ++ tx.functionName ++ "\",\"args\":[" ++ argsStr ++ "],\"msgValue\":" ++ toString tx.msgValue ++ ",\"blockTimestamp\":" ++ toString tx.blockTimestamp ++ "}"
            IO.print jsonStr
            isFirst := false
          IO.println ""
          IO.println "]"
    | none =>
      throw <| IO.userError
        s!"Unknown contract type: {contractType}. Supported: SimpleStorage, Counter, Owned, Ledger, OwnedCounter, SimpleToken, SafeCounter"
  | _ =>
    IO.println "Usage: random-gen <contract> <count> <seed>"
    IO.println "Example: random-gen SimpleStorage 100 42"
