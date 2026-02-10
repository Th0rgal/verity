/-
  Basic correctness proofs for SimpleToken operations

  This file proves fundamental properties about SimpleToken operations:
  - Constructor correctness
  - Mint operation correctness
  - Transfer operation correctness
  - Read operations (balanceOf, getTotalSupply, getOwner)
  - Invariant preservation
-/

import DumbContracts.Examples.SimpleToken
import DumbContracts.Specs.SimpleToken.Spec
import DumbContracts.Specs.SimpleToken.Invariants

namespace DumbContracts.Proofs.SimpleToken

open DumbContracts
open DumbContracts.Examples.SimpleToken (constructor mint transfer balanceOf getTotalSupply getOwner isOwner)
open DumbContracts.Specs.SimpleToken hiding owner balances totalSupply

/-! ## Basic Lemmas for Storage Operations -/

/-- setStorageAddr updates the owner address -/
theorem setStorageAddr_updates_owner (s : ContractState) (addr : Address) :
  let slot : StorageSlot Address := Examples.SimpleToken.owner
  let s' := (setStorageAddr slot addr).run s |>.2
  s'.storageAddr 0 = addr := by
  simp [setStorageAddr, Examples.SimpleToken.owner]

/-- setStorage updates the total supply -/
theorem setStorage_updates_supply (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := Examples.SimpleToken.totalSupply
  let s' := (setStorage slot value).run s |>.2
  s'.storage 2 = value := by
  simp [setStorage, Examples.SimpleToken.totalSupply]

/-- setMapping updates a balance -/
theorem setMapping_updates_balance (s : ContractState) (addr : Address) (value : Uint256) :
  let slot : StorageSlot (Address → Uint256) := Examples.SimpleToken.balances
  let s' := (setMapping slot addr value).run s |>.2
  s'.storageMap 1 addr = value := by
  simp [setMapping, Examples.SimpleToken.balances]

/-- getMapping reads a balance -/
theorem getMapping_reads_balance (s : ContractState) (addr : Address) :
  let slot : StorageSlot (Address → Uint256) := Examples.SimpleToken.balances
  let result := (getMapping slot addr).run s |>.1
  result = s.storageMap 1 addr := by
  simp [getMapping, Examples.SimpleToken.balances]

/-- getStorage reads total supply -/
theorem getStorage_reads_supply (s : ContractState) :
  let slot : StorageSlot Uint256 := Examples.SimpleToken.totalSupply
  let result := (getStorage slot).run s |>.1
  result = s.storage 2 := by
  simp [getStorage, Examples.SimpleToken.totalSupply]

/-- getStorageAddr reads owner -/
theorem getStorageAddr_reads_owner (s : ContractState) :
  let slot : StorageSlot Address := Examples.SimpleToken.owner
  let result := (getStorageAddr slot).run s |>.1
  result = s.storageAddr 0 := by
  simp [getStorageAddr, Examples.SimpleToken.owner]

/-- setMapping preserves other addresses -/
theorem setMapping_preserves_other_addresses (s : ContractState) (slot_val : StorageSlot (Address → Uint256))
  (addr value : _) (other_addr : Address) (h : other_addr ≠ addr) :
  let s' := (setMapping slot_val addr value).run s |>.2
  s'.storageMap slot_val.slot other_addr = s.storageMap slot_val.slot other_addr := by
  simp [setMapping, h]

/-! ## Constructor Correctness -/

theorem constructor_meets_spec (s : ContractState) (initialOwner : Address) :
  let s' := (constructor initialOwner).run s |>.2
  constructor_spec initialOwner s s' := by
  simp [constructor, constructor_spec, setStorageAddr, setStorage, Examples.SimpleToken.owner, Examples.SimpleToken.totalSupply]
  constructor
  · intro slot h1 h2; contradiction
  · intro slot h1 h2; contradiction

theorem constructor_sets_owner (s : ContractState) (initialOwner : Address) :
  let s' := (constructor initialOwner).run s |>.2
  s'.storageAddr 0 = initialOwner := by
  have h := constructor_meets_spec s initialOwner
  simp [constructor_spec] at h
  exact h.1

theorem constructor_sets_supply_zero (s : ContractState) (initialOwner : Address) :
  let s' := (constructor initialOwner).run s |>.2
  s'.storage 2 = 0 := by
  have h := constructor_meets_spec s initialOwner
  simp [constructor_spec] at h
  exact h.2.1

/-! ## Mint Correctness

Note: These proofs assume onlyOwner succeeds (caller is owner).
Full verification requires modeling require behavior.
-/

-- Axiom: require succeeds when condition is true
axiom require_succeeds (cond : Bool) (msg : String) (s : ContractState) :
  cond = true →
  (require cond msg).run s = ((), s)

-- Helper: isOwner returns true when sender is owner
theorem isOwner_true_when_owner (s : ContractState) (h : s.sender = s.storageAddr 0) :
  (isOwner.run s).1 = true := by
  simp [isOwner, msgSender, getStorageAddr, Examples.SimpleToken.owner, h]

-- Mint correctness when caller is owner
theorem mint_meets_spec_when_owner (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := (mint to amount).run s |>.2
  mint_spec to amount s s' := by
  sorry -- Requires onlyOwner modeling

theorem mint_increases_balance (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := (mint to amount).run s |>.2
  s'.storageMap 1 to = s.storageMap 1 to + amount := by
  sorry -- Requires onlyOwner modeling

theorem mint_increases_supply (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := (mint to amount).run s |>.2
  s'.storage 2 = s.storage 2 + amount := by
  sorry -- Requires onlyOwner modeling

/-! ## Transfer Correctness

Note: These proofs assume require succeeds (sender has sufficient balance).
-/

theorem transfer_meets_spec_when_sufficient (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) :
  let s' := (transfer to amount).run s |>.2
  transfer_spec s.sender to amount s s' := by
  sorry -- Requires require modeling

theorem transfer_preserves_supply_when_sufficient (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) :
  let s' := (transfer to amount).run s |>.2
  s'.storage 2 = s.storage 2 := by
  sorry -- Requires require modeling

theorem transfer_decreases_sender_balance (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) :
  let s' := (transfer to amount).run s |>.2
  s'.storageMap 1 s.sender = s.storageMap 1 s.sender - amount := by
  sorry -- Requires require modeling

theorem transfer_increases_recipient_balance (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) :
  let s' := (transfer to amount).run s |>.2
  s'.storageMap 1 to = s.storageMap 1 to + amount := by
  sorry -- Requires require modeling

/-! ## Read Operations Correctness -/

theorem balanceOf_meets_spec (s : ContractState) (addr : Address) :
  let result := (balanceOf addr).run s |>.1
  balanceOf_spec addr result s := by
  simp [balanceOf, balanceOf_spec, getMapping, Examples.SimpleToken.balances]

theorem balanceOf_returns_balance (s : ContractState) (addr : Address) :
  let result := (balanceOf addr).run s |>.1
  result = s.storageMap 1 addr := by
  have h := balanceOf_meets_spec s addr
  simp [balanceOf_spec] at h
  exact h

theorem balanceOf_preserves_state (s : ContractState) (addr : Address) :
  let s' := (balanceOf addr).run s |>.2
  s' = s := by
  simp [balanceOf, getMapping]

theorem getTotalSupply_meets_spec (s : ContractState) :
  let result := getTotalSupply.run s |>.1
  getTotalSupply_spec result s := by
  simp [getTotalSupply, getTotalSupply_spec, getStorage, Examples.SimpleToken.totalSupply]

theorem getTotalSupply_returns_supply (s : ContractState) :
  let result := getTotalSupply.run s |>.1
  result = s.storage 2 := by
  have h := getTotalSupply_meets_spec s
  simp [getTotalSupply_spec] at h
  exact h

theorem getTotalSupply_preserves_state (s : ContractState) :
  let s' := getTotalSupply.run s |>.2
  s' = s := by
  simp [getTotalSupply, getStorage]

theorem getOwner_meets_spec (s : ContractState) :
  let result := getOwner.run s |>.1
  getOwner_spec result s := by
  simp [getOwner, getOwner_spec, getStorageAddr, Examples.SimpleToken.owner]

theorem getOwner_returns_owner (s : ContractState) :
  let result := getOwner.run s |>.1
  result = s.storageAddr 0 := by
  have h := getOwner_meets_spec s
  simp [getOwner_spec] at h
  exact h

theorem getOwner_preserves_state (s : ContractState) :
  let s' := getOwner.run s |>.2
  s' = s := by
  simp [getOwner, getStorageAddr]

/-! ## Composition Properties -/

theorem constructor_getTotalSupply_correct (s : ContractState) (initialOwner : Address) :
  let s' := (constructor initialOwner).run s |>.2
  let result := getTotalSupply.run s' |>.1
  constructor_getTotalSupply_spec initialOwner s result := by
  have h_constr := constructor_sets_supply_zero s initialOwner
  have h_get := getTotalSupply_returns_supply ((constructor initialOwner).run s |>.2)
  simp [constructor_getTotalSupply_spec]
  rw [h_get, h_constr]

theorem constructor_getOwner_correct (s : ContractState) (initialOwner : Address) :
  let s' := (constructor initialOwner).run s |>.2
  let result := getOwner.run s' |>.1
  result = initialOwner := by
  simp [constructor, getOwner, setStorageAddr, setStorage, getStorageAddr, Examples.SimpleToken.owner, Examples.SimpleToken.totalSupply]

/-! ## Invariant Preservation -/

theorem constructor_preserves_wellformedness (s : ContractState) (initialOwner : Address)
  (h : WellFormedState s) (h_owner : initialOwner ≠ "") :
  let s' := (constructor initialOwner).run s |>.2
  WellFormedState s' := by
  have h_spec := constructor_meets_spec s initialOwner
  simp [constructor_spec] at h_spec
  obtain ⟨h_owner_set, h_supply_set, h_other_addr, h_other_uint, h_map, h_sender, h_this⟩ := h_spec
  constructor
  · exact h_sender ▸ h.sender_nonempty
  · exact h_this ▸ h.contract_nonempty
  · exact h_owner_set ▸ h_owner

theorem balanceOf_preserves_wellformedness (s : ContractState) (addr : Address) (h : WellFormedState s) :
  let s' := (balanceOf addr).run s |>.2
  WellFormedState s' := by
  have h_pres := balanceOf_preserves_state s addr
  rw [h_pres]
  exact h

theorem getTotalSupply_preserves_wellformedness (s : ContractState) (h : WellFormedState s) :
  let s' := getTotalSupply.run s |>.2
  WellFormedState s' := by
  have h_pres := getTotalSupply_preserves_state s
  rw [h_pres]
  exact h

theorem getOwner_preserves_wellformedness (s : ContractState) (h : WellFormedState s) :
  let s' := getOwner.run s |>.2
  WellFormedState s' := by
  have h_pres := getOwner_preserves_state s
  rw [h_pres]
  exact h

/-! ## Documentation of Limitations

The following properties require full modeling of require behavior:

1. mint_meets_spec_when_owner - Requires onlyOwner guard verification
2. mint_increases_balance - Requires onlyOwner guard verification
3. mint_increases_supply - Requires onlyOwner guard verification
4. transfer_meets_spec_when_sufficient - Requires balance check verification
5. transfer_preserves_supply_when_sufficient - Requires balance check verification
6. transfer_decreases_sender_balance - Requires balance check verification
7. transfer_increases_recipient_balance - Requires balance check verification

These are marked with 'sorry' and require extending the EDSL to model:
- require success/failure paths
- onlyOwner guard enforcement
- Balance sufficiency checks

The proofs for read operations (balanceOf, getTotalSupply, getOwner) are complete.
-/

end DumbContracts.Proofs.SimpleToken
