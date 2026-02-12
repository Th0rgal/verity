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
import Compiler.Proofs.Automation
import Compiler.Hex
import DumbContracts.Examples.Ledger
import DumbContracts.Core.Uint256
import DumbContracts.Proofs.Ledger.Basic

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open Compiler.Proofs
open Compiler.Proofs.Automation
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
  constructor
  · -- EDSL success
    simp [deposit, msgSender, getMapping, setMapping, balances,
      DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
      Contract.run, ContractResult.isSuccess]
  constructor
  · -- Spec success
    simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
      ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping,
      SpecStorage.getSlot, SpecStorage.setMapping]
  · -- Spec mapping equals EDSL mapping
    have h_spec_val :
        (let specTx : DiffTestTypes.Transaction := {
          sender := sender
          functionName := "deposit"
          args := [amount]
        };
        let specResult :=
          interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender]) specTx;
        specResult.finalStorage.getMapping 0 (addressToNat sender)) =
          ((state.storageMap 0 sender).val + amount) % DumbContracts.Core.Uint256.modulus := by
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage_getMapping_setMapping_same]
    have h_edsl_state :
        (ContractResult.getState
            ((deposit (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
          ).storageMap 0 sender =
          DumbContracts.EVM.Uint256.add (state.storageMap 0 sender)
            (DumbContracts.Core.Uint256.ofNat amount) := by
      simpa [ContractResult.snd, ContractResult.getState] using
        (DumbContracts.Proofs.Ledger.deposit_increases_balance
          { state with sender := sender } (DumbContracts.Core.Uint256.ofNat amount))
    have h_edsl_val :
        ((ContractResult.getState
            ((deposit (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
          ).storageMap 0 sender).val =
          (DumbContracts.EVM.Uint256.add (state.storageMap 0 sender)
            (DumbContracts.Core.Uint256.ofNat amount)).val := by
      simpa using congrArg (fun v : DumbContracts.Core.Uint256 => v.val) h_edsl_state
    have h_add_val :
        (DumbContracts.EVM.Uint256.add (state.storageMap 0 sender)
          (DumbContracts.Core.Uint256.ofNat amount)).val =
          ((state.storageMap 0 sender).val + amount) % DumbContracts.Core.Uint256.modulus := by
      let m := DumbContracts.Core.Uint256.modulus
      have h_ofNat_add :
          (DumbContracts.Core.Uint256.ofNat (amount % m) +
            DumbContracts.Core.Uint256.ofNat (state.storageMap 0 sender).val).val =
            (amount + (state.storageMap 0 sender).val) % m := by
        have h_mod_state : (state.storageMap 0 sender).val % m = (state.storageMap 0 sender).val := by
          exact Nat.mod_eq_of_lt (state.storageMap 0 sender).isLt
        calc
          (DumbContracts.Core.Uint256.ofNat (amount % m) +
              DumbContracts.Core.Uint256.ofNat (state.storageMap 0 sender).val).val
              = ((amount % m) + (state.storageMap 0 sender).val % m) % m := by
                  simp [HAdd.hAdd, DumbContracts.Core.Uint256.add, DumbContracts.Core.Uint256.ofNat,
                    DumbContracts.Core.Uint256.val_ofNat]
          _ = ((amount % m) + (state.storageMap 0 sender).val) % m := by
                  simp [h_mod_state]
          _ = ((state.storageMap 0 sender).val + (amount % m)) % m := by
                  simp [Nat.add_comm]
          _ = ((state.storageMap 0 sender).val + amount) % m := by
                  calc
                    ((state.storageMap 0 sender).val + (amount % m)) % m
                        = ((state.storageMap 0 sender).val % m + (amount % m) % m) % m := by
                            exact (Nat.add_mod _ _ _)
                    _ = ((state.storageMap 0 sender).val % m + amount % m) % m := by
                            simp [Nat.mod_mod]
                    _ = ((state.storageMap 0 sender).val + amount) % m := by
                            symm
                            exact (Nat.add_mod _ _ _)
          _ = (amount + (state.storageMap 0 sender).val) % m := by
                  simp [Nat.add_comm]
      calc
        (DumbContracts.EVM.Uint256.add (state.storageMap 0 sender)
            (DumbContracts.Core.Uint256.ofNat amount)).val
            = (DumbContracts.Core.Uint256.ofNat (amount % m) +
                DumbContracts.Core.Uint256.ofNat (state.storageMap 0 sender).val).val := by
                simp [DumbContracts.EVM.Uint256.add, DumbContracts.Core.Uint256.add,
                  DumbContracts.Core.Uint256.val_ofNat, Nat.add_comm]
        _ = ((state.storageMap 0 sender).val + amount) % m := by
            simpa [Nat.add_comm] using h_ofNat_add
    calc
      (let specTx : DiffTestTypes.Transaction := {
        sender := sender
        functionName := "deposit"
        args := [amount]
      };
      let specResult :=
        interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender]) specTx;
      specResult.finalStorage.getMapping 0 (addressToNat sender))
          = ((state.storageMap 0 sender).val + amount) % DumbContracts.Core.Uint256.modulus := h_spec_val
      _ = (DumbContracts.EVM.Uint256.add (state.storageMap 0 sender)
            (DumbContracts.Core.Uint256.ofNat amount)).val := by
            symm
            exact h_add_val
      _ = ((ContractResult.getState
            ((deposit (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
          ).storageMap 0 sender).val := by
            symm
            exact h_edsl_val

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
  have h_amount_lt : amount < DumbContracts.Core.Uint256.modulus := by
    have hlt : (state.storageMap 0 sender).val < DumbContracts.Core.Uint256.modulus := by
      exact (state.storageMap 0 sender).isLt
    exact Nat.lt_of_le_of_lt h hlt
  have h_balance_u :
      (state.storageMap 0 sender) ≥ DumbContracts.Core.Uint256.ofNat amount := by
    simp [DumbContracts.Core.Uint256.le_def, DumbContracts.Core.Uint256.val_ofNat,
      Nat.mod_eq_of_lt h_amount_lt, h]
  constructor
  · -- EDSL success
    simp [withdraw, msgSender, getMapping, setMapping, balances,
      DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
      Contract.run, ContractResult.isSuccess, h_balance_u]
  constructor
  · -- Spec success
    have h_not_lt : ¬ (state.storageMap 0 sender).val < amount := by
      exact Nat.not_lt_of_ge h
    simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
      ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
      SpecStorage.setMapping, h, h_not_lt, Nat.mod_eq_of_lt h_amount_lt]
  · -- Spec mapping equals EDSL mapping
    have h_not_lt : ¬ (state.storageMap 0 sender).val < amount := by
      exact Nat.not_lt_of_ge h
    have h_spec_val :
        (let specTx : DiffTestTypes.Transaction := {
          sender := sender
          functionName := "withdraw"
          args := [amount]
        };
        let specResult :=
          interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender]) specTx;
        specResult.finalStorage.getMapping 0 (addressToNat sender)) =
          (state.storageMap 0 sender).val - amount := by
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage_getMapping_setMapping_same, h, h_not_lt,
        Nat.mod_eq_of_lt h_amount_lt]
    have h_edsl_state :
        (ContractResult.getState
            ((withdraw (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
          ).storageMap 0 sender =
          DumbContracts.EVM.Uint256.sub (state.storageMap 0 sender)
            (DumbContracts.Core.Uint256.ofNat amount) := by
      simpa [ContractResult.snd, ContractResult.getState] using
        (DumbContracts.Proofs.Ledger.withdraw_decreases_balance
          { state with sender := sender } (DumbContracts.Core.Uint256.ofNat amount) h_balance_u)
    have h_edsl_val :
        ((ContractResult.getState
            ((withdraw (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
          ).storageMap 0 sender).val =
          (state.storageMap 0 sender).val - amount := by
      have h_val := congrArg (fun v : DumbContracts.Core.Uint256 => v.val) h_edsl_state
      -- Subtraction uses Nat subtraction when no underflow; amount ≤ balance by h
      have h_le : (DumbContracts.Core.Uint256.ofNat amount).val ≤ (state.storageMap 0 sender).val := by
        simpa [DumbContracts.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_amount_lt] using h
      -- Convert the Uint256 subtraction to Nat subtraction using sub_eq_of_le.
      have h_val' :
          ((ContractResult.getState
              ((withdraw (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 0 sender).val =
            ((state.storageMap 0 sender - DumbContracts.Core.Uint256.ofNat amount :
              DumbContracts.Core.Uint256) : Nat) := by
        simpa [DumbContracts.EVM.Uint256.sub] using h_val
      have h_val'' :
          ((state.storageMap 0 sender - DumbContracts.Core.Uint256.ofNat amount :
            DumbContracts.Core.Uint256) : Nat) =
            (state.storageMap 0 sender).val - amount := by
        simpa [DumbContracts.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_amount_lt] using
          (DumbContracts.Core.Uint256.sub_eq_of_le (a := state.storageMap 0 sender)
            (b := DumbContracts.Core.Uint256.ofNat amount) h_le)
      calc
        ((ContractResult.getState
            ((withdraw (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
          ).storageMap 0 sender).val
            = ((state.storageMap 0 sender - DumbContracts.Core.Uint256.ofNat amount :
              DumbContracts.Core.Uint256) : Nat) := h_val'
        _ = (state.storageMap 0 sender).val - amount := h_val''
    calc
      (let specTx : DiffTestTypes.Transaction := {
        sender := sender
        functionName := "withdraw"
        args := [amount]
      };
      let specResult :=
        interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender]) specTx;
      specResult.finalStorage.getMapping 0 (addressToNat sender))
          = (state.storageMap 0 sender).val - amount := h_spec_val
      _ = ((ContractResult.getState
            ((withdraw (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
          ).storageMap 0 sender).val := by
            symm
            exact h_edsl_val

/-- The `withdraw` function correctly reverts when balance is insufficient -/
theorem ledger_withdraw_reverts_insufficient (state : ContractState) (amount : Nat) (sender : Address)
    (h_amount : amount < DumbContracts.Core.Uint256.modulus)
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
  -- EDSL side: withdraw reverts when balance is insufficient.
  have h_insufficient : ¬ (amount ≤ (state.storageMap 0 sender).val) := by
    exact Nat.not_le_of_gt h
  have h_insufficient_u :
      ¬ ((state.storageMap 0 sender) ≥ DumbContracts.Core.Uint256.ofNat amount) := by
    simpa [ge_iff_le, DumbContracts.Core.Uint256.le_def, DumbContracts.Core.Uint256.val_ofNat,
      Nat.mod_eq_of_lt h_amount] using h_insufficient
  constructor
  · obtain ⟨msg, hrun⟩ :=
      DumbContracts.Proofs.Ledger.withdraw_reverts_insufficient
        { state with sender := sender } (DumbContracts.Core.Uint256.ofNat amount) h_insufficient_u
    simp [ContractResult.isSuccess, hrun]
  · -- Spec side: require fails, so interpreter returns success = false.
    simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
      ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
      h, h_insufficient, Nat.mod_eq_of_lt h_amount]

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
  have h_amount_lt : amount < DumbContracts.Core.Uint256.modulus := by
    have hlt : (state.storageMap 0 sender).val < DumbContracts.Core.Uint256.modulus := by
      exact (state.storageMap 0 sender).isLt
    exact Nat.lt_of_le_of_lt h hlt
  have h_balance_u :
      (state.storageMap 0 sender) ≥ DumbContracts.Core.Uint256.ofNat amount := by
    simp [DumbContracts.Core.Uint256.le_def, DumbContracts.Core.Uint256.val_ofNat,
      Nat.mod_eq_of_lt h_amount_lt, h]
  by_cases h_eq : sender = to
  · subst h_eq
    constructor
    · -- EDSL success
      simp [transfer, msgSender, getMapping, setMapping, balances,
        DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
        Contract.run, ContractResult.isSuccess, h_balance_u]
    constructor
    · -- Spec success
      have h_not_lt : ¬ (state.storageMap 0 sender).val < amount := by
        exact Nat.not_lt_of_ge h
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, h, h_not_lt, Nat.mod_eq_of_lt h_amount_lt]
    constructor
    · -- Spec sender mapping equals EDSL sender mapping (self-transfer case)
      have h_not_lt : ¬ (state.storageMap 0 sender).val < amount := by
        exact Nat.not_lt_of_ge h
      have h_spec_val :
          (let specTx : DiffTestTypes.Transaction := {
            sender := sender
            functionName := "transfer"
            args := [addressToNat sender, amount]
          };
          let specResult :=
            interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender, sender]) specTx;
          specResult.finalStorage.getMapping 0 (addressToNat sender)) =
            ((state.storageMap 0 sender).val + amount) % DumbContracts.Core.Uint256.modulus := by
        simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
          ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
          SpecStorage.setMapping, SpecStorage_getMapping_setMapping_same, h, h_not_lt,
          Nat.mod_eq_of_lt h_amount_lt]
      have h_edsl_val :
          ((ContractResult.getState
              ((transfer sender (DumbContracts.Core.Uint256.ofNat amount)).run
                { state with sender := sender })
            ).storageMap 0 sender).val =
            ((state.storageMap 0 sender).val + amount) % DumbContracts.Core.Uint256.modulus := by
        simp [transfer, msgSender, getMapping, setMapping, balances,
          DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
          Contract.run, ContractResult.getState, ContractResult.snd, ContractResult.fst,
          DumbContracts.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_amount_lt, h_balance_u]
      simpa [h_spec_val] using h_edsl_val.symm
    · -- Spec recipient mapping equals EDSL recipient mapping (same as sender)
      simpa using (by
        have h_not_lt : ¬ (state.storageMap 0 sender).val < amount := by
          exact Nat.not_lt_of_ge h
        have h_spec_val :
            (let specTx : DiffTestTypes.Transaction := {
              sender := sender
              functionName := "transfer"
              args := [addressToNat sender, amount]
            };
            let specResult :=
              interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender, sender]) specTx;
            specResult.finalStorage.getMapping 0 (addressToNat sender)) =
              ((state.storageMap 0 sender).val + amount) % DumbContracts.Core.Uint256.modulus := by
          simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
            ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
            SpecStorage.setMapping, SpecStorage_getMapping_setMapping_same, h, h_not_lt,
            Nat.mod_eq_of_lt h_amount_lt]
        have h_edsl_val :
            ((ContractResult.getState
                ((transfer sender (DumbContracts.Core.Uint256.ofNat amount)).run
                  { state with sender := sender })
              ).storageMap 0 sender).val =
              ((state.storageMap 0 sender).val + amount) % DumbContracts.Core.Uint256.modulus := by
          simp [transfer, msgSender, getMapping, setMapping, balances,
            DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
            Contract.run, ContractResult.getState, ContractResult.snd, ContractResult.fst,
            DumbContracts.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_amount_lt, h_balance_u]
        simpa [h_spec_val] using h_edsl_val.symm)
  · have h_ne : sender ≠ to := h_eq
    constructor
    · -- EDSL success
      simp [transfer, msgSender, getMapping, setMapping, balances,
        DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
        Contract.run, ContractResult.isSuccess, h_balance_u]
    constructor
    · -- Spec success
      have h_not_lt : ¬ (state.storageMap 0 sender).val < amount := by
        exact Nat.not_lt_of_ge h
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, h, h_not_lt, Nat.mod_eq_of_lt h_amount_lt]
    constructor
    · -- Spec sender mapping equals EDSL sender mapping
      have h_not_lt : ¬ (state.storageMap 0 sender).val < amount := by
        exact Nat.not_lt_of_ge h
      have h_spec_val :
          (let specTx : DiffTestTypes.Transaction := {
            sender := sender
            functionName := "transfer"
            args := [addressToNat to, amount]
          };
          let specResult :=
            interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender, to]) specTx;
          specResult.finalStorage.getMapping 0 (addressToNat sender)) =
            (state.storageMap 0 sender).val - amount := by
        simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
          ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
          SpecStorage.setMapping, SpecStorage_getMapping_setMapping_same, h, h_not_lt,
          Nat.mod_eq_of_lt h_amount_lt]
      have h_edsl_state :
          (ContractResult.getState
              ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 0 sender =
            DumbContracts.EVM.Uint256.sub (state.storageMap 0 sender)
              (DumbContracts.Core.Uint256.ofNat amount) := by
        simpa [ContractResult.snd, ContractResult.getState] using
          (DumbContracts.Proofs.Ledger.transfer_decreases_sender
            { state with sender := sender } to (DumbContracts.Core.Uint256.ofNat amount) h_balance_u h_ne)
      have h_edsl_val :
          ((ContractResult.getState
              ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 0 sender).val =
            (state.storageMap 0 sender).val - amount := by
        have h_val := congrArg (fun v : DumbContracts.Core.Uint256 => v.val) h_edsl_state
        have h_le : (DumbContracts.Core.Uint256.ofNat amount).val ≤ (state.storageMap 0 sender).val := by
          simpa [DumbContracts.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_amount_lt] using h
        have h_val' :
            ((ContractResult.getState
                ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
              ).storageMap 0 sender).val =
              ((state.storageMap 0 sender - DumbContracts.Core.Uint256.ofNat amount :
                DumbContracts.Core.Uint256) : Nat) := by
          simpa [DumbContracts.EVM.Uint256.sub] using h_val
        have h_val'' :
            ((state.storageMap 0 sender - DumbContracts.Core.Uint256.ofNat amount :
              DumbContracts.Core.Uint256) : Nat) =
              (state.storageMap 0 sender).val - amount := by
          simpa [DumbContracts.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_amount_lt] using
            (DumbContracts.Core.Uint256.sub_eq_of_le (a := state.storageMap 0 sender)
              (b := DumbContracts.Core.Uint256.ofNat amount) h_le)
        calc
          ((ContractResult.getState
              ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 0 sender).val
              = ((state.storageMap 0 sender - DumbContracts.Core.Uint256.ofNat amount :
                DumbContracts.Core.Uint256) : Nat) := h_val'
          _ = (state.storageMap 0 sender).val - amount := h_val''
      calc
        (let specTx : DiffTestTypes.Transaction := {
          sender := sender
          functionName := "transfer"
          args := [addressToNat to, amount]
        };
        let specResult :=
          interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender, to]) specTx;
        specResult.finalStorage.getMapping 0 (addressToNat sender))
            = (state.storageMap 0 sender).val - amount := h_spec_val
        _ = ((ContractResult.getState
              ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 0 sender).val := by
              symm
              exact h_edsl_val
    · -- Spec recipient mapping equals EDSL recipient mapping
      have h_not_lt : ¬ (state.storageMap 0 sender).val < amount := by
        exact Nat.not_lt_of_ge h
      have h_spec_val :
          (let specTx : DiffTestTypes.Transaction := {
            sender := sender
            functionName := "transfer"
            args := [addressToNat to, amount]
          };
          let specResult :=
            interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender, to]) specTx;
          specResult.finalStorage.getMapping 0 (addressToNat to)) =
            ((state.storageMap 0 to).val + amount) % DumbContracts.Core.Uint256.modulus := by
        simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
          ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
          SpecStorage.setMapping, SpecStorage_getMapping_setMapping_same, h, h_not_lt,
          Nat.mod_eq_of_lt h_amount_lt]
      have h_edsl_state :
          (ContractResult.getState
              ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 0 to =
            DumbContracts.EVM.Uint256.add (state.storageMap 0 to)
              (DumbContracts.Core.Uint256.ofNat amount) := by
        simpa [ContractResult.snd, ContractResult.getState] using
          (DumbContracts.Proofs.Ledger.transfer_increases_recipient
            { state with sender := sender } to (DumbContracts.Core.Uint256.ofNat amount) h_balance_u h_ne)
      have h_edsl_val :
          ((ContractResult.getState
              ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 0 to).val =
            ((state.storageMap 0 to).val + amount) % DumbContracts.Core.Uint256.modulus := by
        have h_val := congrArg (fun v : DumbContracts.Core.Uint256 => v.val) h_edsl_state
        have h_lt :
            (state.storageMap 0 to).val + amount < DumbContracts.Core.Uint256.modulus := by
          have h0 : (state.storageMap 0 to).val < DumbContracts.Core.Uint256.modulus := by
            exact (state.storageMap 0 to).isLt
          exact Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h0
        simpa [DumbContracts.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_amount_lt] using
          (DumbContracts.EVM.Uint256.add_eq_of_lt (a := state.storageMap 0 to)
            (b := DumbContracts.Core.Uint256.ofNat amount) h_lt)
      calc
        (let specTx : DiffTestTypes.Transaction := {
          sender := sender
          functionName := "transfer"
          args := [addressToNat to, amount]
        };
        let specResult :=
          interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender, to]) specTx;
        specResult.finalStorage.getMapping 0 (addressToNat to))
            = ((state.storageMap 0 to).val + amount) % DumbContracts.Core.Uint256.modulus := h_spec_val
        _ = ((ContractResult.getState
              ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 0 to).val := by
              symm
              exact h_edsl_val

/-- The `transfer` function correctly reverts when balance is insufficient -/
theorem ledger_transfer_reverts_insufficient (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h_amount : amount < DumbContracts.Core.Uint256.modulus)
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
  -- EDSL side: transfer reverts when balance is insufficient.
  have h_insufficient : ¬ (amount ≤ (state.storageMap 0 sender).val) := by
    exact Nat.not_le_of_gt h
  have h_insufficient_u :
      ¬ ((state.storageMap 0 sender) ≥ DumbContracts.Core.Uint256.ofNat amount) := by
    simpa [ge_iff_le, DumbContracts.Core.Uint256.le_def, DumbContracts.Core.Uint256.val_ofNat,
      Nat.mod_eq_of_lt h_amount] using h_insufficient
  constructor
  · obtain ⟨msg, hrun⟩ :=
      DumbContracts.Proofs.Ledger.transfer_reverts_insufficient
        { state with sender := sender } to (DumbContracts.Core.Uint256.ofNat amount) h_insufficient_u
    simp [ContractResult.isSuccess, hrun]
  · -- Spec side: require fails, so interpreter returns success = false.
    have h_senderBal :
        (List.lookup "senderBal"
            [("recipientBal",
                (List.lookup (addressToNat to % DumbContracts.Core.Uint256.modulus)
                      [(addressToNat sender, (state.storageMap 0 sender).val),
                        (addressToNat to, (state.storageMap 0 to).val)]).getD
                  0),
              ("senderBal", (state.storageMap 0 sender).val)]).getD 0 =
          (state.storageMap 0 sender).val := by
      simp [List.lookup, beq_iff_eq]
    simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
      ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
      h, h_insufficient, Nat.mod_eq_of_lt h_amount, h_senderBal]

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
  have h_amount_lt : amount < DumbContracts.Core.Uint256.modulus := by
    have hlt : (state.storageMap 0 sender).val < DumbContracts.Core.Uint256.modulus := by
      exact (state.storageMap 0 sender).isLt
    exact Nat.lt_of_le_of_lt h2 hlt
  have h_balance_u :
      (state.storageMap 0 sender) ≥ DumbContracts.Core.Uint256.ofNat amount := by
    simp [DumbContracts.Core.Uint256.le_def, DumbContracts.Core.Uint256.val_ofNat,
      Nat.mod_eq_of_lt h_amount_lt, h2]
  have h_sender :
      (transfer to (DumbContracts.Core.Uint256.ofNat amount)).runState { state with sender := sender } |>.storageMap 0 sender =
        DumbContracts.EVM.Uint256.sub (state.storageMap 0 sender)
          (DumbContracts.Core.Uint256.ofNat amount) := by
    simpa [Contract.runState] using
      (DumbContracts.Proofs.Ledger.transfer_decreases_sender
        { state with sender := sender } to (DumbContracts.Core.Uint256.ofNat amount) h_balance_u h)
  have h_recipient :
      (transfer to (DumbContracts.Core.Uint256.ofNat amount)).runState { state with sender := sender } |>.storageMap 0 to =
        DumbContracts.EVM.Uint256.add (state.storageMap 0 to)
          (DumbContracts.Core.Uint256.ofNat amount) := by
    simpa [Contract.runState] using
      (DumbContracts.Proofs.Ledger.transfer_increases_recipient
        { state with sender := sender } to (DumbContracts.Core.Uint256.ofNat amount) h_balance_u h)
  have h_sender_val :
      (finalState.storageMap 0 sender).val =
        (state.storageMap 0 sender).val - amount := by
    have h_le : (DumbContracts.Core.Uint256.ofNat amount).val ≤ (state.storageMap 0 sender).val := by
      simpa [DumbContracts.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_amount_lt] using h2
    have h_val :
        ((DumbContracts.EVM.Uint256.sub (state.storageMap 0 sender)
          (DumbContracts.Core.Uint256.ofNat amount) : DumbContracts.Core.Uint256) : Nat) =
          (state.storageMap 0 sender).val - amount := by
      simpa [DumbContracts.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_amount_lt] using
        (DumbContracts.Core.Uint256.sub_eq_of_le (a := state.storageMap 0 sender)
          (b := DumbContracts.Core.Uint256.ofNat amount) h_le)
    have h_final : (finalState.storageMap 0 sender) =
        DumbContracts.EVM.Uint256.sub (state.storageMap 0 sender)
          (DumbContracts.Core.Uint256.ofNat amount) := by
      simpa [finalState, h_sender] using h_sender
    simpa [h_final] using h_val
  have h_recipient_val :
      (finalState.storageMap 0 to).val =
        (state.storageMap 0 to).val + amount := by
    have h_val :
        ((DumbContracts.EVM.Uint256.add (state.storageMap 0 to)
          (DumbContracts.Core.Uint256.ofNat amount) : DumbContracts.Core.Uint256) : Nat) =
          (state.storageMap 0 to).val + amount := by
      have h_lt :
          (state.storageMap 0 to).val + (DumbContracts.Core.Uint256.ofNat amount).val < 2^256 := by
        simpa [DumbContracts.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_amount_lt] using h3
      simpa using
        (DumbContracts.EVM.Uint256.add_eq_of_lt (a := state.storageMap 0 to)
          (b := DumbContracts.Core.Uint256.ofNat amount) h_lt)
    have h_final : (finalState.storageMap 0 to) =
        DumbContracts.EVM.Uint256.add (state.storageMap 0 to)
          (DumbContracts.Core.Uint256.ofNat amount) := by
      simpa [finalState, h_recipient] using h_recipient
    simpa [h_final] using h_val
  calc
    (finalState.storageMap 0 sender).val + (finalState.storageMap 0 to).val
        = ((state.storageMap 0 sender).val - amount) + ((state.storageMap 0 to).val + amount) := by
            simp [h_sender_val, h_recipient_val]
    _ = (state.storageMap 0 sender).val + (state.storageMap 0 to).val := by
            omega

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
