/-
  Compiler.Proofs.SpecCorrectness.SimpleToken

  Prove that simpleTokenSpec accurately represents the SimpleToken EDSL.

  This establishes that the manually written ContractSpec matches
  the verified EDSL semantics for SimpleToken, which composes
  ownership, balance mappings, and total supply tracking.

  Strategy:
  - Define state conversion with multiple slots and mapping storage
  - Prove constructor initializes owner and totalSupply
  - Prove mint adds to balance and totalSupply (owner-only)
  - Prove transfer moves balances between addresses
  - Prove getters retrieve correct values
  - Show spec interpretation matches EDSL execution with full composition
-/

import Compiler.Specs
import Verity.Proofs.Stdlib.SpecInterpreter
import Verity.Proofs.Stdlib.Automation
import Verity.Examples.SimpleToken
import Verity.Proofs.SimpleToken.Basic
import Verity.Proofs.SimpleToken.Correctness

-- Increased heartbeats due to additional struct fields (mappings2, events, etc.)
set_option maxHeartbeats 400000

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open Verity.Proofs.Stdlib.SpecInterpreter
open Verity.Proofs.Stdlib.Automation
open Compiler.Hex
open Verity
open Verity.Stdlib.Math (MAX_UINT256 safeAdd requireSomeUint)
open Verity.Examples.SimpleToken
open Verity.Proofs.SimpleToken

/- State Conversion -/

/-- Convert EDSL ContractState to SpecStorage for SimpleToken with specific addresses -/
def tokenEdslToSpecStorageWithAddrs (state : ContractState) (addrs : List Address) : SpecStorage :=
  { slots := [
      (0, addressToNat (state.storageAddr 0)),  -- owner at slot 0
      (2, (state.storage 2).val)                -- totalSupply at slot 2
    ]
    mappings := [(1, addrs.map (fun addr => (addressToNat addr, (state.storageMap 1 addr).val)))]
    mappings2 := []
    events := [] }

/-!
## Helper Lemmas for Address and Uint256 Arithmetic
-/

-- Address encoding lemmas are provided by Automation.

-- Mapping lookups for two-address lists.
-- (lookup_senderBal, lookup_recipientBal, lookup_addr_first, lookup_addr_second) are provided by Automation.

-- (uint256_add_val) is provided by Automation.

/- Correctness Theorems -/

/-- The `constructor` correctly initializes owner and totalSupply -/
theorem token_constructor_correct (state : ContractState) (initialOwner : Address) (sender : Address) :
    let edslResult := (constructor initialOwner).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := ""
      args := [addressToNat initialOwner]
    }
    let specResult := interpretSpec simpleTokenSpec SpecStorage.empty specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getSlot 0 = addressToNat (edslResult.getState.storageAddr 0) ∧
    specResult.finalStorage.getSlot 2 = (edslResult.getState.storage 2).val := by
  constructor
  · -- EDSL constructor succeeds
    simp [constructor, Contract.run, ContractResult.isSuccess, setStorageAddr, setStorage,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Examples.SimpleToken.owner, Examples.SimpleToken.totalSupply]
  constructor
  · -- Spec constructor succeeds
    simp [interpretSpec, execConstructor, execStmts, execStmt, evalExpr,
      simpleTokenSpec, requireOwner, SpecStorage.setSlot, SpecStorage.getSlot, SpecStorage.empty,
      addressToNat_mod_eq]
  constructor
  · -- Owner slot matches
    have h_owner :
        (ContractResult.getState
          ((constructor initialOwner).run { state with sender := sender })).storageAddr 0 = initialOwner := by
      -- Use proven EDSL lemma
      simpa [Contract.run, ContractResult.getState, ContractResult.snd] using
        (constructor_sets_owner { state with sender := sender } initialOwner)
    -- Spec side stores constructorArg 0 (addressToNat initialOwner)
    simp [interpretSpec, execConstructor, execStmts, execStmt, evalExpr,
      simpleTokenSpec, requireOwner, SpecStorage.setSlot, SpecStorage.getSlot, SpecStorage.empty,
      addressToNat_mod_eq, h_owner]
  · -- Total supply slot matches
    have h_supply :
        (ContractResult.getState
          ((constructor initialOwner).run { state with sender := sender })).storage 2 = 0 := by
      simpa [Contract.run, ContractResult.getState, ContractResult.snd] using
        (constructor_sets_supply_zero { state with sender := sender } initialOwner)
    simp [interpretSpec, execConstructor, execStmts, execStmt, evalExpr,
      simpleTokenSpec, requireOwner, SpecStorage.setSlot, SpecStorage.getSlot, SpecStorage.empty, h_supply]

/-- The `mint` function correctly mints when called by owner and no overflow -/
theorem token_mint_correct_as_owner (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : state.storageAddr 0 = sender)
    (h_no_bal_overflow : (state.storageMap 1 to : Nat) + amount ≤ MAX_UINT256)
    (h_no_sup_overflow : (state.storage 2 : Nat) + amount ≤ MAX_UINT256) :
    let edslResult := (mint to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "mint"
      args := [addressToNat to, amount]
    }
    let specResult := interpretSpec simpleTokenSpec (tokenEdslToSpecStorageWithAddrs state [to]) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getMapping 1 (addressToNat to) = (edslResult.getState.storageMap 1 to).val ∧
    specResult.finalStorage.getSlot 2 = (edslResult.getState.storage 2).val := by
  -- Convert Nat overflow hypotheses to Uint256 safeAdd results
  have h_amount_lt : amount < Verity.Core.Uint256.modulus := by
    calc amount ≤ (state.storageMap 1 to : Nat) + amount := Nat.le_add_left ..
      _ ≤ MAX_UINT256 := h_no_bal_overflow
      _ < Verity.Core.Uint256.modulus := max_uint256_lt_modulus
  have h_bal_safe : safeAdd (state.storageMap 1 to) (Verity.Core.Uint256.ofNat amount) = some (state.storageMap 1 to + Verity.Core.Uint256.ofNat amount) := by
    simp only [safeAdd, Verity.Core.Uint256.coe_ofNat, Nat.mod_eq_of_lt h_amount_lt]
    simp [Nat.not_lt.mpr h_no_bal_overflow]
  have h_sup_safe : safeAdd (state.storage 2) (Verity.Core.Uint256.ofNat amount) = some (state.storage 2 + Verity.Core.Uint256.ofNat amount) := by
    simp only [safeAdd, Verity.Core.Uint256.coe_ofNat, Nat.mod_eq_of_lt h_amount_lt]
    simp [Nat.not_lt.mpr h_no_sup_overflow]
  constructor
  · -- EDSL success (checks-before-effects: both requireSomeUint before setMapping/setStorage)
    simp only [mint, Verity.Examples.SimpleToken.onlyOwner, isOwner, Contract.run,
      msgSender, getStorageAddr, getMapping, setMapping, getStorage, setStorage,
      Examples.SimpleToken.owner, Examples.SimpleToken.balances, Examples.SimpleToken.totalSupply,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      ContractResult.isSuccess, ContractResult.snd, ContractResult.fst,
      h, beq_self_eq_true, ite_true]
    unfold requireSomeUint
    rw [h_bal_safe]
    simp only [Verity.pure, Pure.pure, Verity.bind, Bind.bind,
      getStorage, Contract.run, ContractResult.snd, ContractResult.fst]
    rw [h_sup_safe]
    simp [Verity.pure, Pure.pure, Verity.bind, Bind.bind,
      setMapping, setStorage,
      Contract.run, ContractResult.snd, ContractResult.fst, ContractResult.isSuccess]
  -- Helper: modular add equals plain add when no overflow
  have h_bal_mod_eq : ((state.storageMap 1 to).val + amount) % Verity.Core.Uint256.modulus = (state.storageMap 1 to).val + amount := by
    exact Nat.mod_eq_of_lt (lt_modulus_of_le_max_uint256 _ h_no_bal_overflow)
  have h_sup_mod_eq : ((state.storage 2).val + amount) % Verity.Core.Uint256.modulus = (state.storage 2).val + amount := by
    exact Nat.mod_eq_of_lt (lt_modulus_of_le_max_uint256 _ h_no_sup_overflow)
  -- Helper: ge check succeeds (no overflow means newBalance >= recipientBal)
  have h_bal_ge : ¬ ((state.storageMap 1 to).val + amount < (state.storageMap 1 to).val) := by omega
  have h_sup_ge : ¬ ((state.storage 2).val + amount < (state.storage 2).val) := by omega
  constructor
  · -- Spec success
    simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
      simpleTokenSpec, requireOwner, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
      SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same,
      addressToNat_mod_eq, h, h_bal_mod_eq, h_bal_ge, h_sup_mod_eq, h_sup_ge,
      List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq]
  have h_bal_of : (({ state with sender := sender } : ContractState).storageMap 1 to : Nat) + ((Verity.Core.Uint256.ofNat amount : Uint256) : Nat) ≤ MAX_UINT256 := by
    simp [Verity.Core.Uint256.coe_ofNat]
    rw [Nat.mod_eq_of_lt h_amount_lt]
    exact h_no_bal_overflow
  have h_sup_of : (({ state with sender := sender } : ContractState).storage 2 : Nat) + ((Verity.Core.Uint256.ofNat amount : Uint256) : Nat) ≤ MAX_UINT256 := by
    simp [Verity.Core.Uint256.coe_ofNat]
    rw [Nat.mod_eq_of_lt h_amount_lt]
    exact h_no_sup_overflow
  constructor
  · -- Mapping update matches EDSL
    have h_edsl_map :
        (ContractResult.getState
          ((mint to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
        ).storageMap 1 to =
        Verity.EVM.Uint256.add (state.storageMap 1 to)
          (Verity.Core.Uint256.ofNat amount) := by
      simpa [Contract.run, ContractResult.getState, ContractResult.snd, h] using
        (mint_increases_balance { state with sender := sender } to
          (Verity.Core.Uint256.ofNat amount) h.symm h_bal_of h_sup_of)
    have h_edsl_map_val :
        ((ContractResult.getState
          ((mint to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
        ).storageMap 1 to).val =
        (Verity.EVM.Uint256.add (state.storageMap 1 to)
          (Verity.Core.Uint256.ofNat amount)).val := by
      simpa using congrArg (fun v : Verity.Core.Uint256 => v.val) h_edsl_map
    have h_spec_val :
        (let specTx : DiffTestTypes.Transaction := {
          sender := sender
          functionName := "mint"
          args := [addressToNat to, amount]
        };
        let specResult := interpretSpec simpleTokenSpec
          (tokenEdslToSpecStorageWithAddrs state [to]) specTx;
        specResult.finalStorage.getMapping 1 (addressToNat to)) =
          ((state.storageMap 1 to).val + amount) % Verity.Core.Uint256.modulus := by
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        simpleTokenSpec, requireOwner, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same,
        List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq,
        addressToNat_mod_eq, h, h_bal_mod_eq, h_bal_ge, h_sup_mod_eq, h_sup_ge,
        List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq]
    calc
      (let specTx : DiffTestTypes.Transaction := {
        sender := sender
        functionName := "mint"
        args := [addressToNat to, amount]
      };
      let specResult := interpretSpec simpleTokenSpec
        (tokenEdslToSpecStorageWithAddrs state [to]) specTx;
      specResult.finalStorage.getMapping 1 (addressToNat to))
          = ((state.storageMap 1 to).val + amount) % Verity.Core.Uint256.modulus := h_spec_val
      _ = (Verity.EVM.Uint256.add (state.storageMap 1 to)
            (Verity.Core.Uint256.ofNat amount)).val := by
            symm
            exact uint256_add_val (state.storageMap 1 to) amount
      _ = ((ContractResult.getState
          ((mint to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
        ).storageMap 1 to).val := by
            symm
            exact h_edsl_map_val
  · -- Total supply update matches EDSL
    have h_edsl_supply :
        (ContractResult.getState
          ((mint to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
        ).storage 2 =
        Verity.EVM.Uint256.add (state.storage 2)
          (Verity.Core.Uint256.ofNat amount) := by
      simpa [Contract.run, ContractResult.getState, ContractResult.snd, h] using
        (mint_increases_supply { state with sender := sender } to
          (Verity.Core.Uint256.ofNat amount) h.symm h_bal_of h_sup_of)
    have h_edsl_supply_val :
        ((ContractResult.getState
          ((mint to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
        ).storage 2).val =
        (Verity.EVM.Uint256.add (state.storage 2)
          (Verity.Core.Uint256.ofNat amount)).val := by
      simpa using congrArg (fun v : Verity.Core.Uint256 => v.val) h_edsl_supply
    have h_spec_val :
        (let specTx : DiffTestTypes.Transaction := {
          sender := sender
          functionName := "mint"
          args := [addressToNat to, amount]
        };
        let specResult := interpretSpec simpleTokenSpec
          (tokenEdslToSpecStorageWithAddrs state [to]) specTx;
        specResult.finalStorage.getSlot 2) =
          ((state.storage 2).val + amount) % Verity.Core.Uint256.modulus := by
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        simpleTokenSpec, requireOwner, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same,
        List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq,
        addressToNat_mod_eq, h, h_bal_mod_eq, h_bal_ge, h_sup_mod_eq, h_sup_ge,
        List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq]
    calc
      (let specTx : DiffTestTypes.Transaction := {
        sender := sender
        functionName := "mint"
        args := [addressToNat to, amount]
      };
      let specResult := interpretSpec simpleTokenSpec
        (tokenEdslToSpecStorageWithAddrs state [to]) specTx;
      specResult.finalStorage.getSlot 2)
          = ((state.storage 2).val + amount) % Verity.Core.Uint256.modulus := h_spec_val
      _ = (Verity.EVM.Uint256.add (state.storage 2)
            (Verity.Core.Uint256.ofNat amount)).val := by
            symm
            exact uint256_add_val (state.storage 2) amount
      _ = ((ContractResult.getState
          ((mint to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
        ).storage 2).val := by
            symm
            exact h_edsl_supply_val

/-- The `mint` function correctly reverts when called by non-owner -/
theorem token_mint_reverts_as_nonowner (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : state.storageAddr 0 ≠ sender) :
    let edslResult := (mint to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "mint"
      args := [addressToNat to, amount]
    }
    let specResult := interpretSpec simpleTokenSpec (tokenEdslToSpecStorageWithAddrs state [to]) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  constructor
  · -- EDSL reverts due to onlyOwner check
    have h_beq : (sender == state.storageAddr 0) = false :=
      address_beq_false_of_ne sender (state.storageAddr 0) (Ne.symm h)
    simp [mint, Verity.Examples.SimpleToken.onlyOwner, isOwner, Contract.run,
      msgSender, getStorageAddr, getMapping, setMapping, getStorage, setStorage,
      Examples.SimpleToken.owner, Examples.SimpleToken.balances, Examples.SimpleToken.totalSupply,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      ContractResult.isSuccess, h_beq]
  · -- Spec reverts due to require failing
    have h_beq : (addressToNat sender == addressToNat (state.storageAddr 0)) = false :=
      addressToNat_beq_false_of_ne sender (state.storageAddr 0) (Ne.symm h)
    simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
      simpleTokenSpec, requireOwner, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
      SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same,
      addressToNat_mod_eq, h_beq]

/-- The `transfer` function correctly transfers when balance is sufficient -/
theorem token_transfer_correct_sufficient (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : (state.storageMap 1 sender).val ≥ amount)
    (h_no_overflow : sender ≠ to → (state.storageMap 1 to).val + amount ≤ MAX_UINT256) :
    let edslResult := (transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transfer"
      args := [addressToNat to, amount]
    }
    let specResult := interpretSpec simpleTokenSpec (tokenEdslToSpecStorageWithAddrs state [sender, to]) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getMapping 1 (addressToNat sender) = (edslResult.getState.storageMap 1 sender).val ∧
    specResult.finalStorage.getMapping 1 (addressToNat to) = (edslResult.getState.storageMap 1 to).val := by
  have h_amount_lt := amount_lt_modulus_of_val_ge (state.storageMap 1 sender) amount h
  have h_balance_u := uint256_ofNat_le_of_val_ge (state.storageMap 1 sender) amount h
  by_cases h_eq : sender = to
  · subst h_eq
    have h_not_lt : ¬ (state.storageMap 1 sender).val < amount := Nat.not_lt_of_ge h
    have h_sender_lt : (state.storageMap 1 sender).val < Verity.Core.Uint256.modulus := (state.storageMap 1 sender).isLt
    have h_eq_nat : (addressToNat sender == addressToNat sender) = true := by simp
    constructor
    · -- EDSL success
      simp [transfer, msgSender, getMapping, setMapping, balances,
        Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Contract.run, ContractResult.isSuccess, h_balance_u]
    constructor
    · -- Spec success
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        simpleTokenSpec, requireOwner, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage.setSlot, h, h_not_lt, Nat.mod_eq_of_lt h_amount_lt,
        Nat.mod_eq_of_lt h_sender_lt,
        List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq]
    -- Both sender and recipient are the same address in self-transfer
    have h_spec_val :
        (let specTx : DiffTestTypes.Transaction := {
          sender := sender
          functionName := "transfer"
          args := [addressToNat sender, amount]
        };
        let specResult := interpretSpec simpleTokenSpec
          (tokenEdslToSpecStorageWithAddrs state [sender, sender]) specTx;
        specResult.finalStorage.getMapping 1 (addressToNat sender)) =
          (state.storageMap 1 sender).val := by
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        simpleTokenSpec, requireOwner, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same, h, h_not_lt,
        Nat.mod_eq_of_lt h_amount_lt, Nat.mod_eq_of_lt h_sender_lt,
        h_eq_nat,
        List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq]
    have h_edsl_val :
        ((ContractResult.getState
            ((transfer sender (Verity.Core.Uint256.ofNat amount)).run
              { state with sender := sender })
          ).storageMap 1 sender).val =
          (state.storageMap 1 sender).val := by
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
    have h_no_overflow_nat : (state.storageMap 1 to).val + amount ≤ MAX_UINT256 :=
      h_no_overflow h_ne
    have h_safe : safeAdd (state.storageMap 1 to) (Verity.Core.Uint256.ofNat amount) = some (state.storageMap 1 to + Verity.Core.Uint256.ofNat amount) := by
      simp only [safeAdd, Verity.Core.Uint256.coe_ofNat, Nat.mod_eq_of_lt h_amount_lt]
      simp [Nat.not_lt.mpr h_no_overflow_nat]
    have h_not_lt : ¬ (state.storageMap 1 sender).val < amount := Nat.not_lt_of_ge h
    have h_recip_add_mod : ((state.storageMap 1 to).val + amount) % Verity.Core.Uint256.modulus = (state.storageMap 1 to).val + amount :=
      Nat.mod_eq_of_lt (lt_modulus_of_le_max_uint256 _ h_no_overflow_nat)
    have h_recip_ge : ¬ ((state.storageMap 1 to).val + amount < (state.storageMap 1 to).val) := by omega
    constructor
    · -- EDSL success
      simp [transfer, msgSender, getMapping, setMapping, balances,
        requireSomeUint, h_safe,
        Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Contract.run, ContractResult.isSuccess, ContractResult.snd, ContractResult.fst,
        h_balance_u, h_ne]
    constructor
    · -- Spec success
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        simpleTokenSpec, requireOwner, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage.setSlot, h, h_not_lt, Nat.mod_eq_of_lt h_amount_lt,
        h_addr_ne, h_addr_ne',
        List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq,
        h_recip_add_mod, h_recip_ge]
    constructor
    · -- Sender mapping equals EDSL mapping
      have h_spec_val :
          (let specTx : DiffTestTypes.Transaction := {
            sender := sender
            functionName := "transfer"
            args := [addressToNat to, amount]
          };
          let specResult := interpretSpec simpleTokenSpec
            (tokenEdslToSpecStorageWithAddrs state [sender, to]) specTx;
          specResult.finalStorage.getMapping 1 (addressToNat sender)) =
            (state.storageMap 1 sender).val - amount := by
        simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
          simpleTokenSpec, requireOwner, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
          SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same,
          h, h_not_lt, Nat.mod_eq_of_lt h_amount_lt,
          h_ne, h_addr_ne, h_addr_ne',
          List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq,
          h_recip_add_mod, h_recip_ge]
      have h_edsl_state :
          (ContractResult.getState
              ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 1 sender =
            Verity.EVM.Uint256.sub (state.storageMap 1 sender)
              (Verity.Core.Uint256.ofNat amount) := by
        simp [transfer, msgSender, getMapping, setMapping, balances,
          requireSomeUint, h_safe,
          Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
          Contract.run, ContractResult.getState, ContractResult.snd, ContractResult.fst,
          h_balance_u, h_ne]
      have h_edsl_val :
          ((ContractResult.getState
              ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 1 sender).val =
            (state.storageMap 1 sender).val - amount :=
        h_edsl_state ▸ uint256_sub_val_of_le _ _ h
      calc
        (let specTx : DiffTestTypes.Transaction := {
          sender := sender
          functionName := "transfer"
          args := [addressToNat to, amount]
        };
        let specResult := interpretSpec simpleTokenSpec
          (tokenEdslToSpecStorageWithAddrs state [sender, to]) specTx;
        specResult.finalStorage.getMapping 1 (addressToNat sender))
            = (state.storageMap 1 sender).val - amount := h_spec_val
        _ = ((ContractResult.getState
              ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 1 sender).val := by
              symm
              exact h_edsl_val
    · -- Recipient mapping equals EDSL mapping
      have h_spec_val :
          (let specTx : DiffTestTypes.Transaction := {
            sender := sender
            functionName := "transfer"
            args := [addressToNat to, amount]
          };
          let specResult := interpretSpec simpleTokenSpec
            (tokenEdslToSpecStorageWithAddrs state [sender, to]) specTx;
          specResult.finalStorage.getMapping 1 (addressToNat to)) =
            ((state.storageMap 1 to).val + amount) % Verity.Core.Uint256.modulus := by
        simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
          simpleTokenSpec, requireOwner, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
          SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same,
          h, h_not_lt, Nat.mod_eq_of_lt h_amount_lt, h_ne, h_addr_ne, h_addr_ne',
          List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq,
          h_recip_add_mod, h_recip_ge]
      have h_edsl_state :
          (ContractResult.getState
              ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 1 to =
            Verity.EVM.Uint256.add (state.storageMap 1 to)
              (Verity.Core.Uint256.ofNat amount) := by
        show _ = state.storageMap 1 to + Verity.Core.Uint256.ofNat amount
        simp [transfer, msgSender, getMapping, setMapping, balances,
          requireSomeUint, h_safe,
          Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
          Contract.run, ContractResult.getState, ContractResult.snd, ContractResult.fst,
          h_balance_u, h_ne]
      have h_edsl_val :
          ((ContractResult.getState
              ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 1 to).val =
            ((state.storageMap 1 to).val + amount) % Verity.Core.Uint256.modulus := by
        have h_val := congrArg (fun v : Verity.Core.Uint256 => v.val) h_edsl_state
        calc
          ((ContractResult.getState
              ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 1 to).val
              = (Verity.EVM.Uint256.add (state.storageMap 1 to)
                (Verity.Core.Uint256.ofNat amount)).val := by
                    simpa using h_val
          _ = ((state.storageMap 1 to).val + amount) % Verity.Core.Uint256.modulus := by
                    exact uint256_add_val (state.storageMap 1 to) amount
      calc
        (let specTx : DiffTestTypes.Transaction := {
          sender := sender
          functionName := "transfer"
          args := [addressToNat to, amount]
        };
        let specResult := interpretSpec simpleTokenSpec
          (tokenEdslToSpecStorageWithAddrs state [sender, to]) specTx;
        specResult.finalStorage.getMapping 1 (addressToNat to))
            = ((state.storageMap 1 to).val + amount) % Verity.Core.Uint256.modulus := h_spec_val
        _ = ((ContractResult.getState
              ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 1 to).val := by
              symm
              exact h_edsl_val

/-- The `transfer` function correctly reverts when balance is insufficient -/
theorem token_transfer_reverts_insufficient (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h_amount : amount < Verity.Core.Uint256.modulus)
    (h : (state.storageMap 1 sender).val < amount) :
    let edslResult := (transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transfer"
      args := [addressToNat to, amount]
    }
    let specResult := interpretSpec simpleTokenSpec (tokenEdslToSpecStorageWithAddrs state [sender, to]) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  -- EDSL side: transfer reverts when balance is insufficient.
  have h_insufficient : ¬ (amount ≤ (state.storageMap 1 sender).val) := by
    exact Nat.not_le_of_gt h
  have h_insufficient_u :
      (state.storageMap 1 sender) < Verity.Core.Uint256.ofNat amount := by
    simpa [Verity.Core.Uint256.lt_def, Verity.Core.Uint256.val_ofNat,
      Nat.mod_eq_of_lt h_amount] using h
  constructor
  · obtain ⟨msg, hrun⟩ :=
      Verity.Proofs.SimpleToken.Correctness.transfer_reverts_insufficient_balance
        { state with sender := sender } to (Verity.Core.Uint256.ofNat amount) h_insufficient_u
    simp [ContractResult.isSuccess, hrun]
  · -- Spec side: require fails, so interpreter returns success = false.
    by_cases h_eq : sender = to
    · subst h_eq
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        simpleTokenSpec, requireOwner, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same,
        List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq,
        h, h_insufficient, Nat.mod_eq_of_lt h_amount]
    · have h_addr_ne : addressToNat sender ≠ addressToNat to :=
        addressToNat_ne_of_ne sender to h_eq
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        simpleTokenSpec, requireOwner, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same,
        List.lookup, BEq.beq, beq_iff_eq, decide_eq_true_eq, String.decEq,
        h, h_insufficient, Nat.mod_eq_of_lt h_amount, h_addr_ne]

/-- The `balanceOf` function correctly retrieves balance -/
theorem token_balanceOf_correct (state : ContractState) (addr : Address) (sender : Address) :
    let edslValue := (balanceOf addr).runValue { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "balanceOf"
      args := [addressToNat addr]
    }
    let specResult := interpretSpec simpleTokenSpec (tokenEdslToSpecStorageWithAddrs state [addr]) specTx
    specResult.success = true ∧
    specResult.returnValue = some edslValue.val := by
  unfold balanceOf Contract.runValue simpleTokenSpec interpretSpec tokenEdslToSpecStorageWithAddrs
  simp [getMapping, execFunction, execStmts, execStmt, evalExpr, SpecStorage.getMapping,
    balances]

/-- The `getTotalSupply` function correctly retrieves total supply -/
theorem token_getTotalSupply_correct (state : ContractState) (sender : Address) :
    let edslValue := (getTotalSupply.runValue { state with sender := sender }).val
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "totalSupply"
      args := []
    }
    let specResult := interpretSpec simpleTokenSpec (tokenEdslToSpecStorageWithAddrs state []) specTx
    specResult.success = true ∧
    specResult.returnValue = some edslValue := by
  unfold getTotalSupply Contract.runValue simpleTokenSpec interpretSpec tokenEdslToSpecStorageWithAddrs
  have h_slot : (List.lookup 2 [(0, addressToNat (state.storageAddr 0)), (2, (state.storage 2).val)]).getD 0
      = (state.storage 2).val := by
    simp [(by decide : (0:Nat) ≠ 2)]
  simp [getStorage, execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot,
    totalSupply, h_slot]

/-- The `getOwner` function correctly retrieves owner -/
theorem token_getOwner_correct (state : ContractState) (sender : Address) :
    let edslAddr := getOwner.runValue { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "owner"
      args := []
    }
    let specResult := interpretSpec simpleTokenSpec (tokenEdslToSpecStorageWithAddrs state []) specTx
    specResult.success = true ∧
    specResult.returnValue = some (addressToNat edslAddr) := by
  unfold getOwner Contract.runValue simpleTokenSpec interpretSpec tokenEdslToSpecStorageWithAddrs
  simp [getStorageAddr, execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot,
    owner]

/- Helper Properties -/

/-- Getters preserve state -/
theorem token_getters_preserve_state (state : ContractState) (addr : Address) (sender : Address) :
    let balState := (balanceOf addr).runState { state with sender := sender }
    let supplyState := getTotalSupply.runState { state with sender := sender }
    let ownerState := getOwner.runState { state with sender := sender }
    balState.storageMap 1 addr = state.storageMap 1 addr ∧
    supplyState.storage 2 = state.storage 2 ∧
    ownerState.storageAddr 0 = state.storageAddr 0 := by
  have h_bal := balanceOf_preserves_state { state with sender := sender } addr
  have h_supply := getTotalSupply_preserves_state { state with sender := sender }
  have h_owner := getOwner_preserves_state { state with sender := sender }
  constructor
  · -- balance mapping preserved
    simpa [Contract.runState] using congrArg (fun s : ContractState => s.storageMap 1 addr) h_bal
  constructor
  · -- totalSupply preserved
    simpa [Contract.runState] using congrArg (fun s : ContractState => s.storage 2) h_supply
  · -- owner preserved
    simpa [Contract.runState] using congrArg (fun s : ContractState => s.storageAddr 0) h_owner

/-- Mint increases totalSupply by amount -/
theorem token_mint_increases_supply (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : state.storageAddr 0 = sender)
    (h2 : (state.storage 2).val + amount < Verity.Core.Uint256.modulus)
    (h_no_bal_overflow : (state.storageMap 1 to : Nat) + amount ≤ MAX_UINT256) :
    let finalState := (mint to (Verity.Core.Uint256.ofNat amount)).runState { state with sender := sender }
    (finalState.storage 2).val = (state.storage 2).val + amount := by
  have h_bal_of : (({ state with sender := sender } : ContractState).storageMap 1 to : Nat) + ((Verity.Core.Uint256.ofNat amount : Uint256) : Nat) ≤ MAX_UINT256 := by
    simp [Verity.Core.Uint256.coe_ofNat]
    rw [Nat.mod_eq_of_lt (lt_modulus_of_le_max_uint256 _ (Nat.le_trans (Nat.le_add_left ..) h_no_bal_overflow))]
    exact h_no_bal_overflow
  have h_sup_of : (({ state with sender := sender } : ContractState).storage 2 : Nat) + ((Verity.Core.Uint256.ofNat amount : Uint256) : Nat) ≤ MAX_UINT256 := by
    simp [Verity.Core.Uint256.coe_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left amount (state.storage 2).val) h2)]
    have : (state.storage 2).val + amount ≤ MAX_UINT256 := by
      have := modulus_eq_max_uint256_succ; omega
    exact this
  have h_edsl :
      (ContractResult.getState
        ((mint to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
      ).storage 2 =
      Verity.EVM.Uint256.add (state.storage 2)
        (Verity.Core.Uint256.ofNat amount) := by
    simpa [Contract.run, ContractResult.getState, ContractResult.snd, h] using
      (mint_increases_supply { state with sender := sender } to
        (Verity.Core.Uint256.ofNat amount) h.symm h_bal_of h_sup_of)
  have h_val :
      ((ContractResult.getState
        ((mint to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
      ).storage 2).val =
      ((state.storage 2).val + amount) % Verity.Core.Uint256.modulus := by
    have h_edsl_val := congrArg (fun v : Verity.Core.Uint256 => v.val) h_edsl
    calc
      ((ContractResult.getState
        ((mint to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
      ).storage 2).val
          = (Verity.EVM.Uint256.add (state.storage 2)
            (Verity.Core.Uint256.ofNat amount)).val := by
              simpa using h_edsl_val
      _ = ((state.storage 2).val + amount) % Verity.Core.Uint256.modulus := by
              exact uint256_add_val (state.storage 2) amount
  -- Since sum < modulus, the mod is identity
  have h_mod : ((state.storage 2).val + amount) % Verity.Core.Uint256.modulus =
      (state.storage 2).val + amount := by
    exact Nat.mod_eq_of_lt h2
  simpa [Contract.runState, h_mod] using h_val

/-- Transfer preserves totalSupply -/
theorem token_transfer_preserves_supply (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : (state.storageMap 1 sender).val ≥ amount) :
    let finalState := (transfer to (Verity.Core.Uint256.ofNat amount)).runState { state with sender := sender }
    finalState.storage 2 = state.storage 2 := by
  have h_amount_lt := amount_lt_modulus_of_val_ge (state.storageMap 1 sender) amount h
  have h_balance_u := uint256_ofNat_le_of_val_ge (state.storageMap 1 sender) amount h
  by_cases h_eq : sender = to
  · subst h_eq
    simp [transfer, msgSender, getMapping, setMapping, balances,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.runState, h_balance_u, beq_iff_eq]
  · cases h_cases : safeAdd (state.storageMap 1 to) (Verity.Core.Uint256.ofNat amount) with
    | none =>
      simp [transfer, msgSender, getMapping, setMapping, balances, requireSomeUint, h_cases,
        Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Contract.run, Contract.runState, ContractResult.snd, ContractResult.fst,
        h_balance_u, h_eq, beq_iff_eq]
    | some val =>
      simp [transfer, msgSender, getMapping, setMapping, balances, requireSomeUint, h_cases,
        Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Contract.run, Contract.runState, ContractResult.snd, ContractResult.fst,
        h_balance_u, h_eq, beq_iff_eq]

/-- Only owner can mint -/
theorem token_only_owner_mints (state : ContractState) (to : Address) (amount : Nat) (sender : Address) :
    ((mint to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender }).isSuccess = true →
    state.storageAddr 0 = sender := by
  intro h_success
  by_cases h_owner : state.storageAddr 0 = sender
  · exact h_owner
  · have h_owner' : sender ≠ state.storageAddr 0 := by
      intro h_eq
      exact h_owner h_eq.symm
    obtain ⟨msg, hrun⟩ :=
      Verity.Proofs.SimpleToken.Correctness.mint_reverts_when_not_owner
        { state with sender := sender } to (Verity.Core.Uint256.ofNat amount) h_owner'
    have h_fail :
        ((mint to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender }).isSuccess = false := by
      simp [ContractResult.isSuccess, hrun]
    have h_contra : (true : Bool) = false := by
      simpa using (h_success.symm.trans h_fail)
    cases h_contra

/-- Transfer preserves total balance (sender + recipient) -/
theorem token_transfer_preserves_total_balance (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : sender ≠ to)
    (h2 : (state.storageMap 1 sender).val ≥ amount)
    (h3 : (state.storageMap 1 to).val + amount < Verity.Core.Uint256.modulus) :
    let finalState := (transfer to (Verity.Core.Uint256.ofNat amount)).runState { state with sender := sender }
    (finalState.storageMap 1 sender).val + (finalState.storageMap 1 to).val =
    (state.storageMap 1 sender).val + (state.storageMap 1 to).val := by
  have h_amount_lt := amount_lt_modulus_of_val_ge (state.storageMap 1 sender) amount h2
  have h_balance_u := uint256_ofNat_le_of_val_ge (state.storageMap 1 sender) amount h2
  have h_no_overflow_nat : (state.storageMap 1 to).val + amount ≤ MAX_UINT256 := by
    have := modulus_eq_max_uint256_succ; omega
  have h_safe : safeAdd (state.storageMap 1 to) (Verity.Core.Uint256.ofNat amount) = some (state.storageMap 1 to + Verity.Core.Uint256.ofNat amount) := by
    simp only [safeAdd, Verity.Core.Uint256.coe_ofNat, Nat.mod_eq_of_lt h_amount_lt]
    simp [Nat.not_lt.mpr h_no_overflow_nat]
  have h_sender_state :
      (ContractResult.getState
        ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
      ).storageMap 1 sender =
      Verity.EVM.Uint256.sub (state.storageMap 1 sender)
        (Verity.Core.Uint256.ofNat amount) := by
    simp [transfer, msgSender, getMapping, setMapping, balances,
      requireSomeUint, h_safe,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.getState, ContractResult.snd, ContractResult.fst,
      h_balance_u, h]
  have h_recipient_state :
      (ContractResult.getState
        ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
      ).storageMap 1 to =
      Verity.EVM.Uint256.add (state.storageMap 1 to)
        (Verity.Core.Uint256.ofNat amount) := by
    show _ = state.storageMap 1 to + Verity.Core.Uint256.ofNat amount
    simp [transfer, msgSender, getMapping, setMapping, balances,
      requireSomeUint, h_safe,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.getState, ContractResult.snd, ContractResult.fst,
      h_balance_u, h]
  have h_sender_val :
      ((ContractResult.getState
        ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
      ).storageMap 1 sender).val =
      (state.storageMap 1 sender).val - amount :=
    h_sender_state ▸ uint256_sub_val_of_le _ _ h2
  have h_recipient_val :
      ((ContractResult.getState
        ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
      ).storageMap 1 to).val =
      (state.storageMap 1 to).val + amount := by
    have h_val := congrArg (fun v : Verity.Core.Uint256 => v.val) h_recipient_state
    have h_val' :
        (Verity.EVM.Uint256.add (state.storageMap 1 to)
          (Verity.Core.Uint256.ofNat amount)).val =
        ((state.storageMap 1 to).val + amount) % Verity.Core.Uint256.modulus := by
      exact uint256_add_val (state.storageMap 1 to) amount
    have h_mod : ((state.storageMap 1 to).val + amount) % Verity.Core.Uint256.modulus =
        (state.storageMap 1 to).val + amount := by
      exact Nat.mod_eq_of_lt h3
    simpa [h_val', h_mod] using h_val
  calc
    ((ContractResult.getState
      ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
    ).storageMap 1 sender).val +
    ((ContractResult.getState
      ((transfer to (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender })
    ).storageMap 1 to).val
        = (state.storageMap 1 sender).val - amount + ((state.storageMap 1 to).val + amount) := by
            simp [h_sender_val, h_recipient_val]
    _ = ((state.storageMap 1 sender).val - amount + amount) + (state.storageMap 1 to).val := by
            ac_rfl
    _ = (state.storageMap 1 sender).val + (state.storageMap 1 to).val := by
            simp [Nat.sub_add_cancel h2, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end Compiler.Proofs.SpecCorrectness
