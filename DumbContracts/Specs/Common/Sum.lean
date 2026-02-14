/-
  Sum helper functions for proving sum properties.

  This module provides utilities for summing balances over finite address sets.
-/

import DumbContracts.Core
import DumbContracts.EVM.Uint256

namespace DumbContracts.Specs.Common

open DumbContracts
open DumbContracts.Core
open DumbContracts.EVM.Uint256

/-- Sum balances from a mapping over a finite set of addresses -/
def sumBalances (slot : Nat) (addrs : FiniteAddressSet) (balances : Nat → Address → Uint256) : Uint256 :=
  addrs.addresses.sum (fun addr => balances slot addr)

/-- Invariant: only known addresses have non-zero balances -/
def balancesFinite (slot : Nat) (s : ContractState) : Prop :=
  ∀ addr, addr ∉ (s.knownAddresses slot).addresses.elements →
    s.storageMap slot addr = 0

/-- Helper: sum is preserved when adding to known address -/
theorem sumBalances_insert_existing {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256}
    (h : addr ∈ addrs.addresses.elements) :
    sumBalances slot (addrs.insert addr) balances = sumBalances slot addrs balances := by
  unfold sumBalances FiniteAddressSet.insert FiniteSet.insert
  simp [h]

/-- Helper: sum increases when adding balance to new address -/
theorem sumBalances_insert_new {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256} {amount : Uint256}
    (h : addr ∉ addrs.addresses.elements)
    (h_zero : balances slot addr = 0) :
    sumBalances slot (addrs.insert addr) (fun s a =>
      if s == slot && a == addr then amount else balances s a) =
    add (sumBalances slot addrs balances) amount := by
  -- This proof requires developing lemmas about:
  -- 1. List.foldl with Uint256 addition
  -- 2. Function extensionality over list elements
  -- 3. Uint256.add commutativity and associativity
  -- This is complex theorem proving work that requires careful development
  sorry  -- Proof requires foldl lemmas - to be completed in Phase 2

end DumbContracts.Specs.Common
