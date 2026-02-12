/-
  Compiler.Proofs.SpecCorrectness.Ledger

  Prove that ledgerSpec accurately represents the Ledger EDSL.

  This establishes that the manually written ContractSpec matches
  the verified EDSL semantics for Ledger with mapping storage.

  Strategy:
  - Define state conversion with mapping storage (Address → Uint256)
  - Prove deposit adds to caller's balance
  - Prove withdraw subtracts from caller's balance (with checks)
  - Prove transfer moves balance between addresses (with checks)
  - Prove getBalance retrieves correct balance
  - Show spec interpretation matches EDSL execution with mapping semantics
-/

import Compiler.Specs
import Compiler.Proofs.SpecInterpreter
import Compiler.Hex
import DumbContracts.Examples.Ledger
import DumbContracts.Core.Uint256
import DumbContracts.Proofs.Ledger.Basic

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open Compiler.Proofs
open Compiler.Hex
open DumbContracts
open DumbContracts.Examples.Ledger

/-!
## Helper Lemmas for Address Encoding
-/

/-- Ethereum addresses are 160-bit values, so addressToNat is always less than 2^256 -/
private theorem addressToNat_lt_modulus (addr : Address) :
    addressToNat addr < DumbContracts.Core.Uint256.modulus := by
  unfold addressToNat
  split
  · have h_160_lt_mod : (2^160 : Nat) < DumbContracts.Core.Uint256.modulus := by
      decide
    rename_i n _
    have h_mod : n % 2^160 < 2^160 := by
      exact Nat.mod_lt _ (by decide : 2^160 > 0)
    exact Nat.lt_trans h_mod h_160_lt_mod
  · rename_i _
    have h_mod : stringToNat addr % 2^160 < 2^160 := Nat.mod_lt _ (by decide : 2^160 > 0)
    have h_160_lt_mod : (2^160 : Nat) < DumbContracts.Core.Uint256.modulus := by decide
    exact Nat.lt_trans h_mod h_160_lt_mod

/-- addressToNat mod modulus is identity -/
private theorem addressToNat_mod_eq (addr : Address) :
    addressToNat addr % DumbContracts.Core.Uint256.modulus = addressToNat addr := by
  exact Nat.mod_eq_of_lt (addressToNat_lt_modulus addr)

/- State Conversion -/

/-- Convert EDSL ContractState to SpecStorage for Ledger (placeholder) -/
def ledgerEdslToSpecStorage (_state : ContractState) : SpecStorage :=
  { slots := []
    -- Note: We can't easily convert the full mapping. For proofs, we'll need to
    -- specify which addresses we care about and convert those entries.
    -- This is a limitation we'll address in the actual proof.
    mappings := [(0, [])]  -- Placeholder, will be refined per-theorem
  }

/-- Convert EDSL mapping to SpecStorage mapping for specific addresses -/
def ledgerEdslToSpecStorageWithAddrs (state : ContractState) (addrs : List Address) : SpecStorage :=
  { slots := []
    mappings := [(0, addrs.map (fun addr => (addressToNat addr, (state.storageMap 0 addr).val)))] }

/- Correctness Theorems -/

/-- The `deposit` function correctly adds to caller's balance -/
theorem ledger_deposit_correct (state : ContractState) (amount : Nat) (sender : Address) :
    let edslResult := (deposit (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "deposit"
      args := [amount]
    }
    let specResult := interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender]) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getMapping 0 (addressToNat sender) =
      (edslResult.getState.storageMap 0 sender).val := by
  sorry

/-- The `withdraw` function correctly subtracts when balance is sufficient -/
theorem ledger_withdraw_correct_sufficient (state : ContractState) (amount : Nat) (sender : Address)
    (h : (state.storageMap 0 sender).val ≥ amount) :
    let edslResult := (withdraw (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "withdraw"
      args := [amount]
    }
    let specResult := interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender]) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getMapping 0 (addressToNat sender) =
      (edslResult.getState.storageMap 0 sender).val := by
  sorry

/-- The `withdraw` function correctly reverts when balance is insufficient -/
theorem ledger_withdraw_reverts_insufficient (state : ContractState) (amount : Nat) (sender : Address)
    (h : (state.storageMap 0 sender).val < amount) :
    let edslResult := (withdraw (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "withdraw"
      args := [amount]
    }
    let specResult := interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender]) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  sorry

/-- The `transfer` function correctly moves balance when sufficient -/
theorem ledger_transfer_correct_sufficient (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : (state.storageMap 0 sender).val ≥ amount) :
    let edslResult := (transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transfer"
      args := [addressToNat to, amount]
    }
    let specResult := interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender, to]) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getMapping 0 (addressToNat sender) =
      (edslResult.getState.storageMap 0 sender).val ∧
    specResult.finalStorage.getMapping 0 (addressToNat to) =
      (edslResult.getState.storageMap 0 to).val := by
  sorry

/-- The `transfer` function correctly reverts when balance is insufficient -/
theorem ledger_transfer_reverts_insufficient (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : (state.storageMap 0 sender).val < amount) :
    let edslResult := (transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transfer"
      args := [addressToNat to, amount]
    }
    let specResult := interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender, to]) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  sorry

/-- The `getBalance` function correctly retrieves balance -/
theorem ledger_getBalance_correct (state : ContractState) (addr : Address) (sender : Address) :
    let edslValue := (getBalance addr).runValue { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "getBalance"
      args := [addressToNat addr]
    }
    let specResult := interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [addr]) specTx
    specResult.success = true ∧
    specResult.returnValue = some edslValue.val := by
  -- Reduce Spec execution and EDSL result to the same mapping lookup.
  have h_edsl : (getBalance addr).runValue { state with sender := sender } =
      state.storageMap 0 addr := by
    simpa [Contract.runValue] using
      DumbContracts.Proofs.Ledger.getBalance_returns_balance { state with sender := sender } addr
  have h_mod := addressToNat_mod_eq addr
  -- Spec side: interpretSpec returns the mapping value at key addressToNat addr.
  -- The Spec storage is initialized with exactly that mapping entry.
  simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
    ledgerSpec, ledgerEdslToSpecStorageWithAddrs, h_edsl, h_mod,
    SpecStorage.getMapping, SpecStorage.getSlot, SpecStorage.setSlot, SpecStorage.setMapping]

/- Helper Properties -/

/-- `getBalance` does not modify storage -/
theorem ledger_getBalance_preserves_state (state : ContractState) (addr : Address) (sender : Address) :
    let finalState := (getBalance addr).runState { state with sender := sender }
    ∀ a, finalState.storageMap 0 a = state.storageMap 0 a := by
  dsimp
  intro addr'
  have h_state :
      (getBalance addr).runState { state with sender := sender } =
        { state with sender := sender } := by
    simpa [Contract.runState] using
      DumbContracts.Proofs.Ledger.getBalance_preserves_state { state with sender := sender } addr
  -- runState returns the same state for getBalance, so storageMap is unchanged.
  rw [h_state]

/-- Deposit increases balance -/
theorem ledger_deposit_increases (state : ContractState) (amount : Nat) (sender : Address)
    (_h : amount > 0)
    (h2 : (state.storageMap 0 sender).val + amount < DumbContracts.Core.Uint256.modulus) :
    let finalState := (deposit (DumbContracts.Core.Uint256.ofNat amount)).runState { state with sender := sender }
    (finalState.storageMap 0 sender).val = (state.storageMap 0 sender).val + amount := by
  have h_deposit :=
    DumbContracts.Proofs.Ledger.deposit_increases_balance { state with sender := sender }
      (DumbContracts.Core.Uint256.ofNat amount)
  have h_amount_lt : amount < DumbContracts.Core.Uint256.modulus := by
    have h_le : amount ≤ (state.storageMap 0 sender).val + amount := by
      exact Nat.le_add_left _ _
    exact Nat.lt_of_le_of_lt h_le h2
  -- Use non-overflow to relate Uint256.add to Nat addition.
  have h_add :
      ((DumbContracts.EVM.Uint256.add (state.storageMap 0 sender)
        (DumbContracts.Core.Uint256.ofNat amount) : DumbContracts.Core.Uint256) : Nat) =
        (state.storageMap 0 sender).val + amount := by
    -- Convert ofNat value to Nat and apply the add_eq_of_lt lemma.
    have h2' : (state.storageMap 0 sender).val + (DumbContracts.Core.Uint256.ofNat amount).val <
        DumbContracts.Core.Uint256.modulus := by
      simpa [DumbContracts.Core.Uint256.ofNat, Nat.mod_eq_of_lt h_amount_lt] using h2
    simpa [DumbContracts.Core.Uint256.ofNat, Nat.mod_eq_of_lt h_amount_lt] using
      DumbContracts.EVM.Uint256.add_eq_of_lt (a := state.storageMap 0 sender)
        (b := DumbContracts.Core.Uint256.ofNat amount) h2'
  -- Convert the deposit lemma to Nat equality on the stored value.
  have h_deposit_val :
      ((deposit (DumbContracts.Core.Uint256.ofNat amount)).runState { state with sender := sender }).storageMap 0 sender =
        DumbContracts.EVM.Uint256.add (state.storageMap 0 sender) (DumbContracts.Core.Uint256.ofNat amount) := by
    simpa [Contract.runState] using h_deposit
  have h_deposit_val_nat :
      (((deposit (DumbContracts.Core.Uint256.ofNat amount)).runState { state with sender := sender }).storageMap 0 sender).val =
        (DumbContracts.EVM.Uint256.add (state.storageMap 0 sender) (DumbContracts.Core.Uint256.ofNat amount)).val := by
    simpa using congrArg (fun v : DumbContracts.Core.Uint256 => v.val) h_deposit_val
  -- Rewrite with the addition lemma and the runState definition.
  simpa [h_add] using h_deposit_val_nat

/-- Transfer preserves total balance (sender + recipient) -/
theorem ledger_transfer_preserves_total (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : sender ≠ to)
    (h2 : (state.storageMap 0 sender).val ≥ amount)
    (h3 : (state.storageMap 0 to).val + amount < DumbContracts.Core.Uint256.modulus) :
    let finalState := (transfer to (DumbContracts.Core.Uint256.ofNat amount)).runState { state with sender := sender }
    (finalState.storageMap 0 sender).val + (finalState.storageMap 0 to).val =
    (state.storageMap 0 sender).val + (state.storageMap 0 to).val := by
  sorry

/-- Other balances unchanged by deposit -/
theorem ledger_deposit_isolates_other (state : ContractState) (amount : Nat) (sender other : Address)
    (h : sender ≠ other) :
    let finalState := (deposit (DumbContracts.Core.Uint256.ofNat amount)).runState { state with sender := sender }
    finalState.storageMap 0 other = state.storageMap 0 other := by
  have h_ne : other ≠ ( { state with sender := sender } ).sender := by
    intro h_eq
    exact h h_eq.symm
  have h_preserve :=
    DumbContracts.Proofs.Ledger.deposit_preserves_other_balances { state with sender := sender }
      (DumbContracts.Core.Uint256.ofNat amount) other h_ne
  simp [Contract.runState] at h_preserve
  simpa using h_preserve

end Compiler.Proofs.SpecCorrectness
