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
import Verity.Proofs.Stdlib.SpecInterpreter
import Verity.Proofs.Stdlib.Automation
import Verity.Examples.Ledger
import Verity.Proofs.Ledger.Basic

-- Increased heartbeats due to additional struct fields (mappings2, events, etc.)
set_option maxHeartbeats 400000

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open Verity.Proofs.Stdlib.SpecInterpreter
open Verity.Proofs.Stdlib.Automation
open Compiler.Hex
open Verity
open Verity.Stdlib.Math (MAX_UINT256)
open Verity.Examples.Ledger

-- Address encoding lemmas are provided by Automation.

-- Local variable and mapping lookup lemmas are provided by Automation.

-- Helper: EVM add (Uint256) matches modular Nat addition.
-- (uint256_add_val) is provided by Automation.

/- State Conversion -/

/-- Convert EDSL mapping to SpecStorage mapping for specific addresses -/
def ledgerEdslToSpecStorageWithAddrs (state : ContractState) (addrs : List Address) : SpecStorage :=
  { slots := []
    mappings := [(0, addrs.map (fun addr => (addressToNat addr, (state.storageMap 0 addr).val)))]
    mappings2 := []
    events := [] }

/- Correctness Theorems -/

/-- The `deposit` function correctly adds to caller's balance -/
theorem ledger_deposit_correct (state : ContractState) (amount : Nat) (sender : Address) :
    let edslResult := (deposit (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender }
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
      Verity.bind, Bind.bind, Verity.pure, Pure.pure,
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
          ((state.storageMap 0 sender).val + amount) % Verity.Core.Uint256.modulus := by
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage_getMapping_setMapping_same]
    have h_edsl_state :
        (ContractResult.getState
            ((deposit (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
          ).storageMap 0 sender =
          Verity.EVM.Uint256.add (state.storageMap 0 sender)
            (Verity.Core.Uint256.ofNat amount) := by
      simpa [ContractResult.snd, ContractResult.getState] using
        (Verity.Proofs.Ledger.deposit_increases_balance
          { state with sender := sender } (Verity.Core.Uint256.ofNat amount))
    have h_edsl_val :
        ((ContractResult.getState
            ((deposit (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
          ).storageMap 0 sender).val =
          ((state.storageMap 0 sender).val + amount) % Verity.Core.Uint256.modulus := by
      have h_val := congrArg Verity.Core.Uint256.val h_edsl_state
      simpa [uint256_add_val] using h_val
    calc
      (let specTx : DiffTestTypes.Transaction := {
        sender := sender
        functionName := "deposit"
        args := [amount]
      };
      let specResult :=
        interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender]) specTx;
      specResult.finalStorage.getMapping 0 (addressToNat sender))
          = ((state.storageMap 0 sender).val + amount) % Verity.Core.Uint256.modulus := h_spec_val
      _ = ((ContractResult.getState
            ((deposit (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
          ).storageMap 0 sender).val := by
            symm
            exact h_edsl_val

/-- The `withdraw` function correctly subtracts when balance is sufficient -/
theorem ledger_withdraw_correct_sufficient (state : ContractState) (amount : Nat) (sender : Address)
    (h : (state.storageMap 0 sender).val ≥ amount) :
    let edslResult := (withdraw (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender }
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
  have h_amount_lt := amount_lt_modulus_of_val_ge (state.storageMap 0 sender) amount h
  have h_balance_u := uint256_ofNat_le_of_val_ge (state.storageMap 0 sender) amount h
  have h_not_lt : ¬ (state.storageMap 0 sender).val < amount := Nat.not_lt_of_ge h
  constructor
  · -- EDSL success
    simp [withdraw, msgSender, getMapping, setMapping, balances,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.isSuccess, h_balance_u]
  constructor
  · -- Spec success
    simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
      ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
      SpecStorage.setMapping, h, h_not_lt, Nat.mod_eq_of_lt h_amount_lt]
  · -- Spec mapping equals EDSL mapping
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
            ((withdraw (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
          ).storageMap 0 sender =
          Verity.EVM.Uint256.sub (state.storageMap 0 sender)
            (Verity.Core.Uint256.ofNat amount) := by
      simpa [ContractResult.snd, ContractResult.getState] using
        (Verity.Proofs.Ledger.withdraw_decreases_balance
          { state with sender := sender } (Verity.Core.Uint256.ofNat amount) h_balance_u)
    have h_edsl_val :
        ((ContractResult.getState
            ((withdraw (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
          ).storageMap 0 sender).val =
          (state.storageMap 0 sender).val - amount :=
      h_edsl_state ▸ uint256_sub_val_of_le _ _ h
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
            ((withdraw (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
          ).storageMap 0 sender).val := by
            symm
            exact h_edsl_val

/-- The `withdraw` function correctly reverts when balance is insufficient -/
theorem ledger_withdraw_reverts_insufficient (state : ContractState) (amount : Nat) (sender : Address)
    (h_amount : amount < Verity.Core.Uint256.modulus)
    (h : (state.storageMap 0 sender).val < amount) :
    let edslResult := (withdraw (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender }
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
      ¬ ((state.storageMap 0 sender) ≥ Verity.Core.Uint256.ofNat amount) := by
    simpa [ge_iff_le, Verity.Core.Uint256.le_def, Verity.Core.Uint256.val_ofNat,
      Nat.mod_eq_of_lt h_amount] using h_insufficient
  constructor
  · obtain ⟨msg, hrun⟩ :=
      Verity.Proofs.Ledger.withdraw_reverts_insufficient
        { state with sender := sender } (Verity.Core.Uint256.ofNat amount) h_insufficient_u
    simp [ContractResult.isSuccess, hrun]
  · -- Spec side: require fails, so interpreter returns success = false.
    simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
      ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
      h, h_insufficient, Nat.mod_eq_of_lt h_amount]

/-- The `transfer` function correctly moves balance when sufficient and no recipient overflow -/
theorem ledger_transfer_correct_sufficient (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : (state.storageMap 0 sender).val ≥ amount)
    (h_no_overflow : (state.storageMap 0 to).val + amount ≤ MAX_UINT256) :
    let edslResult := (transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender }
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
  have h_amount_lt := amount_lt_modulus_of_val_ge (state.storageMap 0 sender) amount h
  have h_balance_u := uint256_ofNat_le_of_val_ge (state.storageMap 0 sender) amount h
  -- Helper: overflow ge-check for the spec's new require on newRecipientBal
  have h_overflow_mod_eq : ((state.storageMap 0 to).val + amount) % Verity.Core.Uint256.modulus = (state.storageMap 0 to).val + amount := by
    exact Nat.mod_eq_of_lt (lt_modulus_of_le_max_uint256 _ h_no_overflow)
  have h_overflow_ge : ¬ ((state.storageMap 0 to).val + amount < (state.storageMap 0 to).val) := by omega
  by_cases h_eq : sender = to
  · subst h_eq
    -- Self-transfer: amountDelta = 0, so newRecipientBal = recipientBal (no overflow possible)
    have h_sender_lt : (state.storageMap 0 sender).val < Verity.Core.Uint256.modulus := (state.storageMap 0 sender).isLt
    have h_self_mod_eq : ((state.storageMap 0 sender).val + 0) % Verity.Core.Uint256.modulus = (state.storageMap 0 sender).val := by
      simp [Nat.mod_eq_of_lt h_sender_lt]
    have h_self_ge : ¬ ((state.storageMap 0 sender).val < (state.storageMap 0 sender).val) := by omega
    constructor
    · -- EDSL success
      simp [transfer, msgSender, getMapping, setMapping, balances,
        Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Contract.run, ContractResult.isSuccess, h_balance_u, beq_iff_eq]
    have h_not_lt : ¬ (state.storageMap 0 sender).val < amount := Nat.not_lt_of_ge h
    have h_eq_nat : (addressToNat sender == addressToNat sender) = true := by simp
    constructor
    · -- Spec success (self-transfer: amountDelta=0, overflow check trivially passes)
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage_getMapping_setMapping_same, h, h_not_lt,
        Nat.mod_eq_of_lt h_amount_lt, Nat.mod_eq_of_lt h_sender_lt,
        h_eq_nat,
        List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq]
    -- Both sender and recipient are the same address in self-transfer
    have h_spec_val :
        (let specTx : DiffTestTypes.Transaction := {
          sender := sender
          functionName := "transfer"
          args := [addressToNat sender, amount]
        };
        let specResult :=
          interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender, sender]) specTx;
        specResult.finalStorage.getMapping 0 (addressToNat sender)) =
          (state.storageMap 0 sender).val := by
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage_getMapping_setMapping_same, h, h_not_lt,
        Nat.mod_eq_of_lt h_amount_lt, Nat.mod_eq_of_lt h_sender_lt,
        h_eq_nat, h_self_mod_eq, h_self_ge,
        List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq]
    have h_edsl_val :
        ((ContractResult.getState
            ((transfer sender (Verity.Core.Uint256.ofNat amount)).run
              { state with sender := sender })
          ).storageMap 0 sender).val =
          (state.storageMap 0 sender).val := by
      simp [transfer, msgSender, getMapping, setMapping, balances,
        Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Contract.run, ContractResult.getState, ContractResult.snd, ContractResult.fst,
        Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_amount_lt, h_balance_u, beq_iff_eq]
    exact ⟨by simpa [h_spec_val] using h_edsl_val.symm,
           by simpa [h_spec_val] using h_edsl_val.symm⟩
  · have h_ne : sender ≠ to := h_eq
    have h_addr_ne : addressToNat sender ≠ addressToNat to :=
      addressToNat_ne_of_ne sender to h_ne
    have h_addr_ne' : addressToNat to ≠ addressToNat sender :=
      Ne.symm h_addr_ne
    -- Compute safeAdd success for EDSL proof
    have h_no_overflow_u : (state.storageMap 0 to : Nat) + ((Verity.Core.Uint256.ofNat amount) : Nat) ≤ MAX_UINT256 := by
      simp [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_amount_lt]
      exact h_no_overflow
    have h_safe : Verity.Stdlib.Math.safeAdd (state.storageMap 0 to) (Verity.Core.Uint256.ofNat amount) = some (state.storageMap 0 to + Verity.Core.Uint256.ofNat amount) := by
      simp only [Verity.Stdlib.Math.safeAdd]
      have h_not : ¬((state.storageMap 0 to : Nat) + ((Verity.Core.Uint256.ofNat amount) : Nat) > MAX_UINT256) := Nat.not_lt.mpr h_no_overflow_u
      simp [h_not, Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_amount_lt, h_no_overflow]
    have h_not_lt : ¬ (state.storageMap 0 sender).val < amount := Nat.not_lt_of_ge h
    constructor
    · -- EDSL success
      simp [transfer, Verity.Stdlib.Math.requireSomeUint, msgSender, getMapping, setMapping, balances,
        Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Contract.run, ContractResult.isSuccess, h_balance_u, h_eq, beq_iff_eq, h_safe]
    constructor
    · -- Spec success (different addresses: overflow check uses h_no_overflow)
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage_getMapping_setMapping_same, h, h_not_lt,
        Nat.mod_eq_of_lt h_amount_lt,
        h_addr_ne, h_addr_ne',
        h_overflow_mod_eq, h_overflow_ge,
        List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq]
    constructor
    · -- Spec sender mapping equals EDSL sender mapping
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
          Nat.mod_eq_of_lt h_amount_lt, h_addr_ne, h_addr_ne',
          h_overflow_mod_eq, h_overflow_ge,
          List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq]
      have h_edsl_state :
          (ContractResult.getState
              ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 0 sender =
            Verity.EVM.Uint256.sub (state.storageMap 0 sender)
              (Verity.Core.Uint256.ofNat amount) := by
        simpa [ContractResult.snd, ContractResult.getState] using
          (Verity.Proofs.Ledger.transfer_decreases_sender
            { state with sender := sender } to (Verity.Core.Uint256.ofNat amount) h_balance_u h_ne h_no_overflow_u)
      have h_edsl_val :
          ((ContractResult.getState
              ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 0 sender).val =
            (state.storageMap 0 sender).val - amount :=
        h_edsl_state ▸ uint256_sub_val_of_le _ _ h
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
              ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 0 sender).val := by
              symm
              exact h_edsl_val
    · -- Spec recipient mapping equals EDSL recipient mapping
      have h_spec_val :
          (let specTx : DiffTestTypes.Transaction := {
            sender := sender
            functionName := "transfer"
            args := [addressToNat to, amount]
          };
          let specResult :=
            interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender, to]) specTx;
          specResult.finalStorage.getMapping 0 (addressToNat to)) =
            ((state.storageMap 0 to).val + amount) % Verity.Core.Uint256.modulus := by
        simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
          ledgerSpec, ledgerEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
          SpecStorage.setMapping, SpecStorage_getMapping_setMapping_same, h, h_not_lt,
          Nat.mod_eq_of_lt h_amount_lt, h_addr_ne, h_addr_ne',
          h_overflow_mod_eq, h_overflow_ge,
          List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq]
      have h_edsl_state :
          (ContractResult.getState
              ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 0 to =
            Verity.EVM.Uint256.add (state.storageMap 0 to)
              (Verity.Core.Uint256.ofNat amount) := by
        simpa [ContractResult.snd, ContractResult.getState] using
          (Verity.Proofs.Ledger.transfer_increases_recipient
            { state with sender := sender } to (Verity.Core.Uint256.ofNat amount) h_balance_u h_ne h_no_overflow_u)
      have h_edsl_val :
          ((ContractResult.getState
              ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 0 to).val =
            ((state.storageMap 0 to).val + amount) % Verity.Core.Uint256.modulus := by
        have h_val := congrArg Verity.Core.Uint256.val h_edsl_state
        simpa [uint256_add_val] using h_val
      calc
        (let specTx : DiffTestTypes.Transaction := {
          sender := sender
          functionName := "transfer"
          args := [addressToNat to, amount]
        };
        let specResult :=
          interpretSpec ledgerSpec (ledgerEdslToSpecStorageWithAddrs state [sender, to]) specTx;
        specResult.finalStorage.getMapping 0 (addressToNat to))
            = ((state.storageMap 0 to).val + amount) % Verity.Core.Uint256.modulus := h_spec_val
        _ = ((ContractResult.getState
              ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 0 to).val := by
              symm
              exact h_edsl_val

/-- The `transfer` function correctly reverts when balance is insufficient -/
theorem ledger_transfer_reverts_insufficient (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h_amount : amount < Verity.Core.Uint256.modulus)
    (h : (state.storageMap 0 sender).val < amount) :
    let edslResult := (transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender }
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
      ¬ ((state.storageMap 0 sender) ≥ Verity.Core.Uint256.ofNat amount) := by
    simpa [ge_iff_le, Verity.Core.Uint256.le_def, Verity.Core.Uint256.val_ofNat,
      Nat.mod_eq_of_lt h_amount] using h_insufficient
  constructor
  · obtain ⟨msg, hrun⟩ :=
      Verity.Proofs.Ledger.transfer_reverts_insufficient
        { state with sender := sender } to (Verity.Core.Uint256.ofNat amount) h_insufficient_u
    simp [ContractResult.isSuccess, hrun]
  · -- Spec side: require fails, so interpreter returns success = false.
    have h_senderBal :
        (List.lookup "senderBal"
            [("recipientBal",
                (List.lookup (addressToNat to % Verity.Core.Uint256.modulus)
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
      Verity.Proofs.Ledger.getBalance_returns_balance { state with sender := sender } addr
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
      Verity.Proofs.Ledger.getBalance_preserves_state { state with sender := sender } addr
  -- runState returns the same state for getBalance, so storageMap is unchanged.
  rw [h_state]

/-- Deposit increases balance -/
theorem ledger_deposit_increases (state : ContractState) (amount : Nat) (sender : Address)
    (_h : amount > 0)
    (h2 : (state.storageMap 0 sender).val + amount < Verity.Core.Uint256.modulus) :
    let finalState := (deposit (Verity.Core.Uint256.ofNat amount)).runState { state with sender := sender }
    (finalState.storageMap 0 sender).val = (state.storageMap 0 sender).val + amount := by
  have h_deposit :=
    Verity.Proofs.Ledger.deposit_increases_balance { state with sender := sender }
      (Verity.Core.Uint256.ofNat amount)
  have h_amount_lt : amount < Verity.Core.Uint256.modulus := by
    have h_le : amount ≤ (state.storageMap 0 sender).val + amount := by
      exact Nat.le_add_left _ _
    exact Nat.lt_of_le_of_lt h_le h2
  -- Use non-overflow to relate Uint256.add to Nat addition.
  have h_add :
      ((Verity.EVM.Uint256.add (state.storageMap 0 sender)
        (Verity.Core.Uint256.ofNat amount) : Verity.Core.Uint256) : Nat) =
        (state.storageMap 0 sender).val + amount := by
    -- Convert ofNat value to Nat and apply the add_eq_of_lt lemma.
    have h2' : (state.storageMap 0 sender).val + (Verity.Core.Uint256.ofNat amount).val <
        Verity.Core.Uint256.modulus := by
      simpa [Verity.Core.Uint256.ofNat, Nat.mod_eq_of_lt h_amount_lt] using h2
    simpa [Verity.Core.Uint256.ofNat, Nat.mod_eq_of_lt h_amount_lt] using
      Verity.EVM.Uint256.add_eq_of_lt (a := state.storageMap 0 sender)
        (b := Verity.Core.Uint256.ofNat amount) h2'
  -- Convert the deposit lemma to Nat equality on the stored value.
  have h_deposit_val :
      ((deposit (Verity.Core.Uint256.ofNat amount)).runState { state with sender := sender }).storageMap 0 sender =
        Verity.EVM.Uint256.add (state.storageMap 0 sender) (Verity.Core.Uint256.ofNat amount) := by
    simpa [Contract.runState] using h_deposit
  -- Rewrite with the addition lemma and the runState definition.
  simpa [h_add] using congrArg Verity.Core.Uint256.val h_deposit_val

/-- Transfer preserves total balance (sender + recipient) -/
theorem ledger_transfer_preserves_total (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : sender ≠ to)
    (h2 : (state.storageMap 0 sender).val ≥ amount)
    (h3 : (state.storageMap 0 to).val + amount < Verity.Core.Uint256.modulus) :
    let finalState := (transfer to (Verity.Core.Uint256.ofNat amount)).runState { state with sender := sender }
    (finalState.storageMap 0 sender).val + (finalState.storageMap 0 to).val =
    (state.storageMap 0 sender).val + (state.storageMap 0 to).val := by
  have h_amount_lt := amount_lt_modulus_of_val_ge (state.storageMap 0 sender) amount h2
  have h_balance_u := uint256_ofNat_le_of_val_ge (state.storageMap 0 sender) amount h2
  have h_no_overflow_u2 : (state.storageMap 0 to : Nat) + ((Verity.Core.Uint256.ofNat amount) : Nat) ≤ MAX_UINT256 := by
    simp only [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_amount_lt, MAX_UINT256, Verity.Stdlib.Math.MAX_UINT256]
    have h_max : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
    rw [h_max] at h3
    omega
  have h_sender :
      ((transfer to (Verity.Core.Uint256.ofNat amount)).runState { state with sender := sender }).storageMap 0 sender =
        Verity.EVM.Uint256.sub (state.storageMap 0 sender)
          (Verity.Core.Uint256.ofNat amount) := by
    simpa [Contract.runState] using
      (Verity.Proofs.Ledger.transfer_decreases_sender
        { state with sender := sender } to (Verity.Core.Uint256.ofNat amount) h_balance_u h h_no_overflow_u2)
  have h_recipient :
      ((transfer to (Verity.Core.Uint256.ofNat amount)).runState { state with sender := sender }).storageMap 0 to =
        Verity.EVM.Uint256.add (state.storageMap 0 to)
          (Verity.Core.Uint256.ofNat amount) := by
    simpa [Contract.runState] using
      (Verity.Proofs.Ledger.transfer_increases_recipient
        { state with sender := sender } to (Verity.Core.Uint256.ofNat amount) h_balance_u h h_no_overflow_u2)
  have h_sender_val :
      ((Contract.runState (transfer to (Verity.Core.Uint256.ofNat amount))
          { state with sender := sender }).storageMap 0 sender).val =
        (state.storageMap 0 sender).val - amount :=
    h_sender ▸ uint256_sub_val_of_le _ _ h2
  have h_recipient_val :
      ((Contract.runState (transfer to (Verity.Core.Uint256.ofNat amount))
          { state with sender := sender }).storageMap 0 to).val =
        (state.storageMap 0 to).val + amount := by
    have h_val := congrArg Verity.Core.Uint256.val h_recipient
    have h_mod : ((state.storageMap 0 to).val + amount) % Verity.Core.Uint256.modulus =
        (state.storageMap 0 to).val + amount := by
      exact Nat.mod_eq_of_lt h3
    simpa [uint256_add_val, h_mod] using h_val
  calc
    ((Contract.runState (transfer to (Verity.Core.Uint256.ofNat amount))
      { state with sender := sender }).storageMap 0 sender).val +
      ((Contract.runState (transfer to (Verity.Core.Uint256.ofNat amount))
      { state with sender := sender }).storageMap 0 to).val
        = ((state.storageMap 0 sender).val - amount) + ((state.storageMap 0 to).val + amount) := by
            simp [h_sender_val, h_recipient_val]
    _ = ((state.storageMap 0 sender).val - amount + amount) + (state.storageMap 0 to).val := by
            ac_rfl
    _ = (state.storageMap 0 sender).val + (state.storageMap 0 to).val := by
            simp [Nat.sub_add_cancel h2, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Other balances unchanged by deposit -/
theorem ledger_deposit_isolates_other (state : ContractState) (amount : Nat) (sender other : Address)
    (h : sender ≠ other) :
    let finalState := (deposit (Verity.Core.Uint256.ofNat amount)).runState { state with sender := sender }
    finalState.storageMap 0 other = state.storageMap 0 other := by
  have h_ne : other ≠ ( { state with sender := sender } ).sender := by
    intro h_eq
    exact h h_eq.symm
  have h_preserve :=
    Verity.Proofs.Ledger.deposit_preserves_other_balances { state with sender := sender }
      (Verity.Core.Uint256.ofNat amount) other h_ne
  simp [Contract.runState] at h_preserve
  simpa using h_preserve

end Compiler.Proofs.SpecCorrectness
