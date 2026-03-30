/-
  Basic proofs for ERC20 foundation scaffold.
-/

import Contracts.ERC20.Spec
import Contracts.ERC20.ERC20
import Verity.Proofs.Stdlib.Math
import Verity.Proofs.Stdlib.Automation

namespace Contracts.ERC20.Proofs

open Verity
open Contracts.ERC20.Spec
open Contracts.ERC20
open Verity.Stdlib.Math (MAX_UINT256 requireSomeUint)
open Verity.Proofs.Stdlib.Math (safeAdd_some)
open Verity.Proofs.Stdlib.Automation (address_beq_false_of_ne uint256_ge_val_le)

private def constructorCompat (initialOwner : Address) : Contract Unit := do
  setStorageAddr ownerSlot initialOwner
  setStorage totalSupplySlot 0

/-- `constructor` sets owner slot 0 and initializes supply slot 1. -/
theorem constructor_meets_spec (s : ContractState) (initialOwner : Address) :
    constructor_spec initialOwner s ((constructorCompat initialOwner).runState s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [constructorCompat, ownerSlot, setStorageAddr, setStorage, Contract.runState, Verity.bind, Bind.bind]
  · simp [constructorCompat, totalSupplySlot, setStorageAddr, setStorage, Contract.runState, Verity.bind, Bind.bind]
  · intro slotIdx h_neq
    simp [constructorCompat, ownerSlot, setStorageAddr, setStorage, Contract.runState, Verity.bind,
      Bind.bind, h_neq]
  · intro slotIdx h_neq
    simp [constructorCompat, ownerSlot, totalSupplySlot, setStorageAddr, setStorage, Contract.runState,
      Verity.bind, Bind.bind, h_neq]
  · simp [Specs.sameStorageMap, constructorCompat, ownerSlot, totalSupplySlot, setStorageAddr, setStorage,
      Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameStorageMap2, constructorCompat, ownerSlot, totalSupplySlot, setStorageAddr, setStorage,
      Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameStorageArray, constructorCompat, ownerSlot, totalSupplySlot, setStorageAddr, setStorage,
      Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameContext, constructorCompat, ownerSlot, totalSupplySlot, setStorageAddr, setStorage,
      Contract.runState, Verity.bind, Bind.bind]

/-- `approve` writes allowance(sender, spender) and leaves other state unchanged. -/
theorem approve_meets_spec (s : ContractState) (spender : Address) (amount : Uint256) :
    approve_spec s.sender spender amount s ((approve spender amount).runState s) := by
  unfold approve_spec Specs.storageMap2UpdateSpec Specs.storageMap2UnchangedExceptKeyPair
    Specs.sameStorageAddrMapContext
  refine ⟨?_, ?_, ?_⟩
  · simp [approve, allowancesSlot, setMapping2, msgSender, Contract.runState, Verity.bind, Bind.bind]
  · refine ⟨?_, ?_⟩
    · intro o' sp' h_neq
      simp [approve, allowancesSlot, setMapping2, msgSender, Contract.runState, Verity.bind, Bind.bind,
        h_neq]
    · intro sp' h_neq
      simp [approve, allowancesSlot, setMapping2, msgSender, Contract.runState, Verity.bind, Bind.bind,
        h_neq]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · exact Specs.sameContext_rfl _

/-- `balanceOf` returns the value stored in balances slot 2 for `addr`. -/
theorem balanceOf_meets_spec (s : ContractState) (addr : Address) :
    balanceOf_spec addr ((balanceOf addr).runValue s) s := by
  simp [balanceOf, balanceOf_spec, Contract.runValue, getMapping, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, balancesSlot]

/-- `allowanceOf` returns the value stored in allowances slot 3 for `(owner, spender)`. -/
theorem allowanceOf_meets_spec (s : ContractState) (ownerAddr spender : Address) :
    allowance_spec ownerAddr spender ((allowanceOf ownerAddr spender).runValue s) s := by
  simp [allowanceOf, allowance_spec, Contract.runValue, getMapping2, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, allowancesSlot]

/-- `getTotalSupply` returns slot 1. -/
theorem totalSupply_meets_spec (s : ContractState) :
    totalSupply_spec ((getTotalSupply).runValue s) s := by
  simp [getTotalSupply, totalSupply_spec, Contract.runValue, totalSupply, getStorage, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, totalSupplySlot]

/-- `getOwner` returns owner slot 0. -/
theorem getOwner_meets_spec (s : ContractState) :
    getOwner_spec ((getOwner).runValue s) s := by
  simp [getOwner, getOwner_spec, Contract.runValue, owner, getStorageAddr, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, ownerSlot]

/-- Helper: unfold `mint` on the successful owner/non-overflow path. -/
private theorem mint_unfold (s : ContractState) (to : Address) (amount : Uint256)
    (h_owner : s.sender = s.storageAddr 0)
    (h_no_bal_overflow : (s.storageMap 2 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
    (h_no_sup_overflow : (s.storage 1 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
    (mint to amount).run s = ContractResult.success ()
      { «storage» := fun slotIdx =>
          if slotIdx == 1 then EVM.Uint256.add (s.storage 1) amount else s.storage slotIdx,
        transientStorage := s.transientStorage,
        storageAddr := s.storageAddr,
        storageMap := fun slotIdx addr =>
          if (slotIdx == 2 && addr == to) = true then EVM.Uint256.add (s.storageMap 2 to) amount
        else s.storageMap slotIdx addr,
        storageMapUint := s.storageMapUint,
        storageMap2 := s.storageMap2,
        storageArray := s.storageArray,
        sender := s.sender,
        thisAddress := s.thisAddress,
        msgValue := s.msgValue,
        blockTimestamp := s.blockTimestamp,
        blockNumber := s.blockNumber,
        chainId := s.chainId,
        blobBaseFee := s.blobBaseFee,
        calldataSize := s.calldataSize,
        knownAddresses := fun slotIdx =>
          if slotIdx == 2 then (s.knownAddresses slotIdx).insert to else s.knownAddresses slotIdx,
        events := s.events } := by
  have h_safe_bal := safeAdd_some (s.storageMap 2 to) amount h_no_bal_overflow
  have h_safe_sup := safeAdd_some (s.storage 1) amount h_no_sup_overflow
  verity_unfold mint
  simp only [ownerSlot, balancesSlot, totalSupplySlot,
    h_owner, beq_self_eq_true, ite_true]
  unfold requireSomeUint
  rw [h_safe_bal]
  simp only [Verity.pure, Pure.pure, Bind.bind]
  rw [h_safe_sup]
  simp only [Verity.pure]
  simp only [HAdd.hAdd, h_owner]

/-- `mint` satisfies `mint_spec` under owner and no-overflow preconditions. -/
theorem mint_meets_spec_when_owner (s : ContractState) (to : Address) (amount : Uint256)
    (h_owner : s.sender = s.storageAddr 0)
    (h_no_bal_overflow : (s.storageMap 2 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
    (h_no_sup_overflow : (s.storage 1 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
    mint_spec to amount s ((mint to amount).runState s) := by
  have h_unfold := mint_unfold s to amount h_owner h_no_bal_overflow h_no_sup_overflow
  have h_unfold_apply := Contract.eq_of_run_success h_unfold
  simp only [Contract.runState, mint_spec]
  rw [h_unfold_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · refine ⟨?_, ?_⟩
    · intro addr h_ne
      simp [h_ne]
    · intro slotIdx h_ne addr
      simp [h_ne]
  · intro slotIdx h_ne
    simp [h_ne]
  · rfl
  · rfl
  · rfl
  · exact Specs.sameContext_rfl _

/-- Under successful-owner assumptions, `mint` increases recipient balance by `amount`. -/
theorem mint_increases_balance_when_owner (s : ContractState) (to : Address) (amount : Uint256)
    (h_owner : s.sender = s.storageAddr 0)
    (h_no_bal_overflow : (s.storageMap 2 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
    (h_no_sup_overflow : (s.storage 1 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
    ((mint to amount).runState s).storageMap 2 to = EVM.Uint256.add (s.storageMap 2 to) amount := by
  have h := mint_meets_spec_when_owner s to amount h_owner h_no_bal_overflow h_no_sup_overflow
  exact h.1

/-- Under successful-owner assumptions, `mint` increases total supply by `amount`. -/
theorem mint_increases_supply_when_owner (s : ContractState) (to : Address) (amount : Uint256)
    (h_owner : s.sender = s.storageAddr 0)
    (h_no_bal_overflow : (s.storageMap 2 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
    (h_no_sup_overflow : (s.storage 1 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
    ((mint to amount).runState s).storage 1 = EVM.Uint256.add (s.storage 1) amount := by
  have h := mint_meets_spec_when_owner s to amount h_owner h_no_bal_overflow h_no_sup_overflow
  exact h.2.1

/-- Helper: unfold `transfer` on the successful self-transfer path. -/
private theorem transfer_unfold_self (s : ContractState) (to : Address) (amount : Uint256)
    (h_balance : s.storageMap 2 s.sender ≥ amount)
    (h_eq : s.sender = to) :
    (transfer to amount).run s = ContractResult.success () s := by
  have h_balance' := uint256_ge_val_le (h_eq ▸ h_balance)
  verity_unfold transfer
  simp [balancesSlot, Verity.pure, h_balance', h_eq]

/-- Helper: unfold `transfer` on the successful non-self path with no overflow. -/
private theorem transfer_unfold_other (s : ContractState) (to : Address) (amount : Uint256)
    (h_balance : s.storageMap 2 s.sender ≥ amount)
    (h_ne : s.sender ≠ to)
    (h_no_overflow : (s.storageMap 2 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
    (transfer to amount).run s = ContractResult.success ()
      { «storage» := s.storage,
        transientStorage := s.transientStorage,
        storageAddr := s.storageAddr,
        storageMap := fun slotIdx addr =>
          if (slotIdx == 2 && addr == to) = true then EVM.Uint256.add (s.storageMap 2 to) amount
          else if (slotIdx == 2 && addr == s.sender) = true then EVM.Uint256.sub (s.storageMap 2 s.sender) amount
        else s.storageMap slotIdx addr,
        storageMapUint := s.storageMapUint,
        storageMap2 := s.storageMap2,
        storageArray := s.storageArray,
        sender := s.sender,
        thisAddress := s.thisAddress,
        msgValue := s.msgValue,
        blockTimestamp := s.blockTimestamp,
        blockNumber := s.blockNumber,
        chainId := s.chainId,
        blobBaseFee := s.blobBaseFee,
        calldataSize := s.calldataSize,
        knownAddresses := fun slotIdx =>
          if slotIdx == 2 then ((s.knownAddresses slotIdx).insert s.sender).insert to
          else s.knownAddresses slotIdx,
        events := s.events } := by
  have h_balance' := uint256_ge_val_le h_balance
  have h_safe := safeAdd_some (s.storageMap 2 to) amount h_no_overflow
  simp only [transfer, balancesSlot, msgSender, getMapping, setMapping, requireSomeUint,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, h_balance, h_ne, beq_iff_eq, h_safe, decide_eq_true_eq,
    ite_true, ite_false, HAdd.hAdd]
  congr 1
  congr 1
  funext slotIdx
  split <;> simp [*]

/-- `transfer` satisfies `transfer_spec` under balance/overflow preconditions. -/
theorem transfer_meets_spec_when_sufficient (s : ContractState) (to : Address) (amount : Uint256)
    (h_balance : s.storageMap 2 s.sender ≥ amount)
    (h_no_overflow : s.sender ≠ to → (s.storageMap 2 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
    transfer_spec s.sender to amount s ((transfer to amount).runState s) := by
  by_cases h_eq : s.sender = to
  · have h_unfold := transfer_unfold_self s to amount h_balance h_eq
    have h_unfold_apply := Contract.eq_of_run_success h_unfold
    simp only [Contract.runState, transfer_spec]
    rw [h_unfold_apply]
    refine ⟨h_balance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [h_eq]
    · simp [h_eq]
    · simp [h_eq, Specs.storageMapUnchangedExceptKeyAtSlot,
        Specs.storageMapUnchangedExceptKey, Specs.storageMapUnchangedExceptSlot]
    · trivial
    · trivial
    · rfl
    · rfl
    · exact Specs.sameContext_rfl _
  · have h_unfold := transfer_unfold_other s to amount h_balance h_eq (h_no_overflow h_eq)
    have h_unfold_apply := Contract.eq_of_run_success h_unfold
    simp only [Contract.runState, transfer_spec]
    rw [h_unfold_apply]
    have h_ne' := address_beq_false_of_ne s.sender to h_eq
    refine ⟨h_balance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [h_ne']
    · simp [h_ne']
    · simp [h_ne']
      refine ⟨?_, ?_⟩
      · intro addr h_ne_sender h_ne_to
        simp [h_ne_sender, h_ne_to]
      · intro slotIdx h_neq addr'
        simp [h_neq]
    · trivial
    · trivial
    · rfl
    · rfl
    · exact Specs.sameContext_rfl _

/-- On successful non-self transfer, sender balance decreases by `amount`. -/
theorem transfer_decreases_sender_balance_when_sufficient
    (s : ContractState) (to : Address) (amount : Uint256)
    (h_balance : s.storageMap 2 s.sender ≥ amount)
    (h_ne : s.sender ≠ to)
    (h_no_overflow : (s.storageMap 2 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
    ((transfer to amount).runState s).storageMap 2 s.sender =
      EVM.Uint256.sub (s.storageMap 2 s.sender) amount := by
  have h := transfer_meets_spec_when_sufficient s to amount h_balance (fun _ => h_no_overflow)
  simp [transfer_spec, h_ne, beq_iff_eq] at h
  simpa [Contract.runState_eq_snd_run] using h.2.1

/-- On successful non-self transfer, recipient balance increases by `amount`. -/
theorem transfer_increases_recipient_balance_when_sufficient
    (s : ContractState) (to : Address) (amount : Uint256)
    (h_balance : s.storageMap 2 s.sender ≥ amount)
    (h_ne : s.sender ≠ to)
    (h_no_overflow : (s.storageMap 2 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
    ((transfer to amount).runState s).storageMap 2 to =
      EVM.Uint256.add (s.storageMap 2 to) amount := by
  have h := transfer_meets_spec_when_sufficient s to amount h_balance (fun _ => h_no_overflow)
  simp [transfer_spec, h_ne, beq_iff_eq] at h
  simpa [Contract.runState_eq_snd_run] using h.2.2.1

end Contracts.ERC20.Proofs
