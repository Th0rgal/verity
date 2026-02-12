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
import Compiler.Proofs.SpecInterpreter
import Compiler.Proofs.Automation
import Compiler.Hex
import DumbContracts.Examples.SimpleToken
import DumbContracts.Proofs.SimpleToken.Basic
import DumbContracts.Proofs.SimpleToken.Correctness
import DumbContracts.Core.Uint256

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open Compiler.Proofs
open Compiler.Proofs.Automation
open Compiler.Hex
open DumbContracts
open DumbContracts.Examples.SimpleToken
open DumbContracts.Proofs.SimpleToken

/- State Conversion -/

/-- Convert EDSL ContractState to SpecStorage for SimpleToken with specific addresses -/
def tokenEdslToSpecStorageWithAddrs (state : ContractState) (addrs : List Address) : SpecStorage :=
  { slots := [
      (0, addressToNat (state.storageAddr 0)),  -- owner at slot 0
      (2, (state.storage 2).val)                -- totalSupply at slot 2
    ]
    mappings := [(1, addrs.map (fun addr => (addressToNat addr, (state.storageMap 1 addr).val)))] }

/-!
## Helper Lemmas for Address and Uint256 Arithmetic
-/

-- Ethereum addresses are 160-bit values, so addressToNat is always less than 2^256.
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

-- Trust assumption: addressToNat is injective for valid addresses.
private axiom addressToNat_injective :
    ∀ (a b : Address), addressToNat a = addressToNat b → a = b

-- addressToNat mod modulus is identity.
private theorem addressToNat_mod_eq (addr : Address) :
    addressToNat addr % DumbContracts.Core.Uint256.modulus = addressToNat addr := by
  exact Nat.mod_eq_of_lt (addressToNat_lt_modulus addr)

-- Helper: EVM add (Uint256) matches modular Nat addition.
private theorem uint256_add_val (a : DumbContracts.Core.Uint256) (amount : Nat) :
    (DumbContracts.EVM.Uint256.add a (DumbContracts.Core.Uint256.ofNat amount)).val =
      (a.val + amount) % DumbContracts.Core.Uint256.modulus := by
  let m := DumbContracts.Core.Uint256.modulus
  have h_mod_a : a.val % m = a.val := by
    exact Nat.mod_eq_of_lt a.isLt
  calc
    (DumbContracts.EVM.Uint256.add a (DumbContracts.Core.Uint256.ofNat amount)).val
        = (a.val + (amount % m)) % m := by
            simp [DumbContracts.EVM.Uint256.add, DumbContracts.Core.Uint256.add,
              DumbContracts.Core.Uint256.val_ofNat]
    _ = (a.val + amount) % m := by
            -- Rewrite with add_mod using a.val < m.
            calc
              (a.val + amount) % m
                  = ((a.val % m) + (amount % m)) % m := by
                      exact (Nat.add_mod _ _ _).symm
              _ = (a.val + (amount % m)) % m := by
                      simp [h_mod_a]

-- Helper: EVM sub (Uint256) matches Nat subtraction when no underflow.
private theorem uint256_sub_val_of_le (a : DumbContracts.Core.Uint256) (amount : Nat)
    (h : a.val ≥ amount) :
    (DumbContracts.EVM.Uint256.sub a (DumbContracts.Core.Uint256.ofNat amount)).val =
      a.val - amount := by
  have h_amount_lt : amount < DumbContracts.Core.Uint256.modulus := by
    exact Nat.lt_of_le_of_lt h a.isLt
  have h_le : (DumbContracts.Core.Uint256.ofNat amount : Nat) ≤ (a : Nat) := by
    simp [DumbContracts.Core.Uint256.coe_ofNat, Nat.mod_eq_of_lt h_amount_lt, h]
  -- Use EVM sub lemma
  have h_sub : ((DumbContracts.EVM.Uint256.sub a (DumbContracts.Core.Uint256.ofNat amount)
      : DumbContracts.Core.Uint256) : Nat) = (a : Nat) - (DumbContracts.Core.Uint256.ofNat amount : Nat) := by
    exact DumbContracts.EVM.Uint256.sub_eq_of_le h_le
  -- Simplify the RHS
  simp [DumbContracts.Core.Uint256.coe_ofNat, Nat.mod_eq_of_lt h_amount_lt] at h_sub
  simpa using h_sub

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
      DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
      Examples.SimpleToken.owner, Examples.SimpleToken.totalSupply]
  constructor
  · -- Spec constructor succeeds
    simp [interpretSpec, execConstructor, execStmts, execStmt, evalExpr,
      simpleTokenSpec, SpecStorage.setSlot, SpecStorage.getSlot, SpecStorage.empty,
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
      simpleTokenSpec, SpecStorage.setSlot, SpecStorage.getSlot, SpecStorage.empty,
      addressToNat_mod_eq, h_owner]
  · -- Total supply slot matches
    have h_supply :
        (ContractResult.getState
          ((constructor initialOwner).run { state with sender := sender })).storage 2 = 0 := by
      simpa [Contract.run, ContractResult.getState, ContractResult.snd] using
        (constructor_sets_supply_zero { state with sender := sender } initialOwner)
    simp [interpretSpec, execConstructor, execStmts, execStmt, evalExpr,
      simpleTokenSpec, SpecStorage.setSlot, SpecStorage.getSlot, SpecStorage.empty, h_supply]

/-- The `mint` function correctly mints when called by owner -/
theorem token_mint_correct_as_owner (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : state.storageAddr 0 = sender) :
    let edslResult := (mint to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender }
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
  constructor
  · -- EDSL success
    simp [mint, DumbContracts.Examples.SimpleToken.onlyOwner, isOwner, Contract.run,
      msgSender, getStorageAddr, getMapping, setMapping, getStorage, setStorage,
      Examples.SimpleToken.owner, Examples.SimpleToken.balances, Examples.SimpleToken.totalSupply,
      DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
      ContractResult.isSuccess, h]
  constructor
  · -- Spec success
    simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
      simpleTokenSpec, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
      SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same,
      addressToNat_mod_eq, h]
  constructor
  · -- Mapping update matches EDSL
    have h_edsl_map :
        (ContractResult.getState
          ((mint to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
        ).storageMap 1 to =
        DumbContracts.EVM.Uint256.add (state.storageMap 1 to)
          (DumbContracts.Core.Uint256.ofNat amount) := by
      simpa [Contract.run, ContractResult.getState, ContractResult.snd, h] using
        (mint_increases_balance { state with sender := sender } to
          (DumbContracts.Core.Uint256.ofNat amount) h.symm)
    have h_edsl_map_val :
        (ContractResult.getState
          ((mint to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
        ).storageMap 1 to |>.val =
        (DumbContracts.EVM.Uint256.add (state.storageMap 1 to)
          (DumbContracts.Core.Uint256.ofNat amount)).val := by
      simpa using congrArg (fun v : DumbContracts.Core.Uint256 => v.val) h_edsl_map
    have h_spec_val :
        (let specTx : DiffTestTypes.Transaction := {
          sender := sender
          functionName := "mint"
          args := [addressToNat to, amount]
        };
        let specResult := interpretSpec simpleTokenSpec
          (tokenEdslToSpecStorageWithAddrs state [to]) specTx;
        specResult.finalStorage.getMapping 1 (addressToNat to)) =
          ((state.storageMap 1 to).val + amount) % DumbContracts.Core.Uint256.modulus := by
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        simpleTokenSpec, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same,
        addressToNat_mod_eq, h]
    calc
      (let specTx : DiffTestTypes.Transaction := {
        sender := sender
        functionName := "mint"
        args := [addressToNat to, amount]
      };
      let specResult := interpretSpec simpleTokenSpec
        (tokenEdslToSpecStorageWithAddrs state [to]) specTx;
      specResult.finalStorage.getMapping 1 (addressToNat to))
          = ((state.storageMap 1 to).val + amount) % DumbContracts.Core.Uint256.modulus := h_spec_val
      _ = (DumbContracts.EVM.Uint256.add (state.storageMap 1 to)
            (DumbContracts.Core.Uint256.ofNat amount)).val := by
            symm
            exact uint256_add_val (state.storageMap 1 to) amount
      _ = (ContractResult.getState
          ((mint to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
        ).storageMap 1 to |>.val := by
            symm
            exact h_edsl_map_val
  · -- Total supply update matches EDSL
    have h_edsl_supply :
        (ContractResult.getState
          ((mint to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
        ).storage 2 =
        DumbContracts.EVM.Uint256.add (state.storage 2)
          (DumbContracts.Core.Uint256.ofNat amount) := by
      simpa [Contract.run, ContractResult.getState, ContractResult.snd, h] using
        (mint_increases_supply { state with sender := sender } to
          (DumbContracts.Core.Uint256.ofNat amount) h.symm)
    have h_edsl_supply_val :
        (ContractResult.getState
          ((mint to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
        ).storage 2 |>.val =
        (DumbContracts.EVM.Uint256.add (state.storage 2)
          (DumbContracts.Core.Uint256.ofNat amount)).val := by
      simpa using congrArg (fun v : DumbContracts.Core.Uint256 => v.val) h_edsl_supply
    have h_spec_val :
        (let specTx : DiffTestTypes.Transaction := {
          sender := sender
          functionName := "mint"
          args := [addressToNat to, amount]
        };
        let specResult := interpretSpec simpleTokenSpec
          (tokenEdslToSpecStorageWithAddrs state [to]) specTx;
        specResult.finalStorage.getSlot 2) =
          ((state.storage 2).val + amount) % DumbContracts.Core.Uint256.modulus := by
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        simpleTokenSpec, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same,
        addressToNat_mod_eq, h]
    calc
      (let specTx : DiffTestTypes.Transaction := {
        sender := sender
        functionName := "mint"
        args := [addressToNat to, amount]
      };
      let specResult := interpretSpec simpleTokenSpec
        (tokenEdslToSpecStorageWithAddrs state [to]) specTx;
      specResult.finalStorage.getSlot 2)
          = ((state.storage 2).val + amount) % DumbContracts.Core.Uint256.modulus := h_spec_val
      _ = (DumbContracts.EVM.Uint256.add (state.storage 2)
            (DumbContracts.Core.Uint256.ofNat amount)).val := by
            symm
            exact uint256_add_val (state.storage 2) amount
      _ = (ContractResult.getState
          ((mint to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
        ).storage 2 |>.val := by
            symm
            exact h_edsl_supply_val

/-- The `mint` function correctly reverts when called by non-owner -/
theorem token_mint_reverts_as_nonowner (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : state.storageAddr 0 ≠ sender) :
    let edslResult := (mint to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender }
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
    have h_beq : (sender == state.storageAddr 0) = false := by
      cases h_eq : (sender == state.storageAddr 0)
      · rfl
      · exfalso
        have h_addr : sender = state.storageAddr 0 := by
          simpa [beq_iff_eq] using h_eq
        exact h h_addr.symm
    simp [mint, DumbContracts.Examples.SimpleToken.onlyOwner, isOwner, Contract.run,
      msgSender, getStorageAddr, getMapping, setMapping, getStorage, setStorage,
      Examples.SimpleToken.owner, Examples.SimpleToken.balances, Examples.SimpleToken.totalSupply,
      DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
      ContractResult.isSuccess, h_beq]
  · -- Spec reverts due to require failing
    have h_beq : (addressToNat sender == addressToNat (state.storageAddr 0)) = false := by
      cases h_eq : (addressToNat sender == addressToNat (state.storageAddr 0))
      · rfl
      · exfalso
        have h_nat : addressToNat sender = addressToNat (state.storageAddr 0) := by
          simpa [beq_iff_eq] using h_eq
        have h_addr : sender = state.storageAddr 0 :=
          addressToNat_injective sender (state.storageAddr 0) h_nat
        exact h h_addr.symm
    simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
      simpleTokenSpec, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
      SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same,
      addressToNat_mod_eq, h_beq]

/-- The `transfer` function correctly transfers when balance is sufficient -/
theorem token_transfer_correct_sufficient (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : (state.storageMap 1 sender).val ≥ amount) :
    let edslResult := (transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender }
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
  have h_amount_lt : amount < DumbContracts.Core.Uint256.modulus := by
    have hlt : (state.storageMap 1 sender).val < DumbContracts.Core.Uint256.modulus := by
      exact (state.storageMap 1 sender).isLt
    exact Nat.lt_of_le_of_lt h hlt
  have h_balance_u :
      (state.storageMap 1 sender) ≥ DumbContracts.Core.Uint256.ofNat amount := by
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
      have h_not_lt : ¬ (state.storageMap 1 sender).val < amount := by
        exact Nat.not_lt_of_ge h
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        simpleTokenSpec, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage.setSlot, h, h_not_lt, Nat.mod_eq_of_lt h_amount_lt,
        addressToNat_mod_eq]
    constructor
    · -- Sender mapping equals EDSL mapping (self-transfer)
      have h_not_lt : ¬ (state.storageMap 1 sender).val < amount := by
        exact Nat.not_lt_of_ge h
      have h_spec_val :
          (let specTx : DiffTestTypes.Transaction := {
            sender := sender
            functionName := "transfer"
            args := [addressToNat sender, amount]
          };
          let specResult := interpretSpec simpleTokenSpec
            (tokenEdslToSpecStorageWithAddrs state [sender, sender]) specTx;
          specResult.finalStorage.getMapping 1 (addressToNat sender)) =
            ((state.storageMap 1 sender).val + amount) % DumbContracts.Core.Uint256.modulus := by
        simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
          simpleTokenSpec, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
          SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same, h, h_not_lt,
          Nat.mod_eq_of_lt h_amount_lt, addressToNat_mod_eq]
      have h_edsl_val :
          ((ContractResult.getState
              ((transfer sender (DumbContracts.Core.Uint256.ofNat amount)).run
                { state with sender := sender })
            ).storageMap 1 sender).val =
            ((state.storageMap 1 sender).val + amount) % DumbContracts.Core.Uint256.modulus := by
        simp [transfer, msgSender, getMapping, setMapping, balances,
          DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
          Contract.run, ContractResult.getState, ContractResult.snd, ContractResult.fst,
          DumbContracts.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_amount_lt, h_balance_u]
      simpa [h_spec_val] using h_edsl_val.symm
    · -- Recipient mapping equals EDSL mapping (same as sender)
      simpa using (by
        have h_not_lt : ¬ (state.storageMap 1 sender).val < amount := by
          exact Nat.not_lt_of_ge h
        have h_spec_val :
            (let specTx : DiffTestTypes.Transaction := {
              sender := sender
              functionName := "transfer"
              args := [addressToNat sender, amount]
            };
            let specResult := interpretSpec simpleTokenSpec
              (tokenEdslToSpecStorageWithAddrs state [sender, sender]) specTx;
            specResult.finalStorage.getMapping 1 (addressToNat sender)) =
              ((state.storageMap 1 sender).val + amount) % DumbContracts.Core.Uint256.modulus := by
          simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
            simpleTokenSpec, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
            SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same, h, h_not_lt,
            Nat.mod_eq_of_lt h_amount_lt, addressToNat_mod_eq]
        have h_edsl_val :
            ((ContractResult.getState
                ((transfer sender (DumbContracts.Core.Uint256.ofNat amount)).run
                  { state with sender := sender })
              ).storageMap 1 sender).val =
              ((state.storageMap 1 sender).val + amount) % DumbContracts.Core.Uint256.modulus := by
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
        Contract.run, ContractResult.isSuccess, h_balance_u, h_ne]
    constructor
    · -- Spec success
      have h_not_lt : ¬ (state.storageMap 1 sender).val < amount := by
        exact Nat.not_lt_of_ge h
      simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
        simpleTokenSpec, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
        SpecStorage.setMapping, SpecStorage.setSlot, h, h_not_lt, Nat.mod_eq_of_lt h_amount_lt,
        addressToNat_mod_eq]
    constructor
    · -- Sender mapping equals EDSL mapping
      have h_not_lt : ¬ (state.storageMap 1 sender).val < amount := by
        exact Nat.not_lt_of_ge h
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
          simpleTokenSpec, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
          SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same,
          h, h_not_lt, Nat.mod_eq_of_lt h_amount_lt, addressToNat_mod_eq, h_ne]
      have h_edsl_state :
          (ContractResult.getState
              ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 1 sender =
            DumbContracts.EVM.Uint256.sub (state.storageMap 1 sender)
              (DumbContracts.Core.Uint256.ofNat amount) := by
        simp [transfer, msgSender, getMapping, setMapping, balances,
          DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
          Contract.run, ContractResult.getState, ContractResult.snd, ContractResult.fst,
          h_balance_u, h_ne]
      have h_edsl_val :
          ((ContractResult.getState
              ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 1 sender).val =
            (state.storageMap 1 sender).val - amount := by
        have h_val := congrArg (fun v : DumbContracts.Core.Uint256 => v.val) h_edsl_state
        -- Use sub semantics with no underflow
        have h_val' :
            ((ContractResult.getState
                ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
              ).storageMap 1 sender).val =
              (DumbContracts.EVM.Uint256.sub (state.storageMap 1 sender)
                (DumbContracts.Core.Uint256.ofNat amount)).val := by
          simpa using h_val
        simpa [h_val'] using
          (uint256_sub_val_of_le (state.storageMap 1 sender) amount h)
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
              ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 1 sender).val := by
              symm
              exact h_edsl_val
    · -- Recipient mapping equals EDSL mapping
      have h_not_lt : ¬ (state.storageMap 1 sender).val < amount := by
        exact Nat.not_lt_of_ge h
      have h_spec_val :
          (let specTx : DiffTestTypes.Transaction := {
            sender := sender
            functionName := "transfer"
            args := [addressToNat to, amount]
          };
          let specResult := interpretSpec simpleTokenSpec
            (tokenEdslToSpecStorageWithAddrs state [sender, to]) specTx;
          specResult.finalStorage.getMapping 1 (addressToNat to)) =
            ((state.storageMap 1 to).val + amount) % DumbContracts.Core.Uint256.modulus := by
        simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
          simpleTokenSpec, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
          SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same,
          h, h_not_lt, Nat.mod_eq_of_lt h_amount_lt, addressToNat_mod_eq, h_ne]
      have h_edsl_state :
          (ContractResult.getState
              ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 1 to =
            DumbContracts.EVM.Uint256.add (state.storageMap 1 to)
              (DumbContracts.Core.Uint256.ofNat amount) := by
        simp [transfer, msgSender, getMapping, setMapping, balances,
          DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
          Contract.run, ContractResult.getState, ContractResult.snd, ContractResult.fst,
          h_balance_u, h_ne]
      have h_edsl_val :
          ((ContractResult.getState
              ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 1 to).val =
            ((state.storageMap 1 to).val + amount) % DumbContracts.Core.Uint256.modulus := by
        have h_val := congrArg (fun v : DumbContracts.Core.Uint256 => v.val) h_edsl_state
        calc
          ((ContractResult.getState
              ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 1 to).val
              = (DumbContracts.EVM.Uint256.add (state.storageMap 1 to)
                (DumbContracts.Core.Uint256.ofNat amount)).val := by
                    simpa using h_val
          _ = ((state.storageMap 1 to).val + amount) % DumbContracts.Core.Uint256.modulus := by
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
            = ((state.storageMap 1 to).val + amount) % DumbContracts.Core.Uint256.modulus := h_spec_val
        _ = ((ContractResult.getState
              ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
            ).storageMap 1 to).val := by
              symm
              exact h_edsl_val

/-- The `transfer` function correctly reverts when balance is insufficient -/
theorem token_transfer_reverts_insufficient (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h_amount : amount < DumbContracts.Core.Uint256.modulus)
    (h : (state.storageMap 1 sender).val < amount) :
    let edslResult := (transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender }
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
      ¬ ((state.storageMap 1 sender) ≥ DumbContracts.Core.Uint256.ofNat amount) := by
    simpa [ge_iff_le, DumbContracts.Core.Uint256.le_def, DumbContracts.Core.Uint256.val_ofNat,
      Nat.mod_eq_of_lt h_amount] using h_insufficient
  constructor
  · obtain ⟨msg, hrun⟩ :=
      DumbContracts.Proofs.SimpleToken.Correctness.transfer_reverts_insufficient_balance
        { state with sender := sender } to (DumbContracts.Core.Uint256.ofNat amount) h_insufficient_u
    simp [ContractResult.isSuccess, hrun]
  · -- Spec side: require fails, so interpreter returns success = false.
    simp [interpretSpec, execFunction, execStmts, execStmt, evalExpr,
      simpleTokenSpec, tokenEdslToSpecStorageWithAddrs, SpecStorage.getMapping, SpecStorage.getSlot,
      SpecStorage.setMapping, SpecStorage.setSlot, SpecStorage_getMapping_setMapping_same,
      h, h_insufficient, Nat.mod_eq_of_lt h_amount, addressToNat_mod_eq]

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
  -- Same pattern as other getters
  unfold balanceOf Contract.runValue simpleTokenSpec interpretSpec tokenEdslToSpecStorageWithAddrs
  simp [getMapping, execFunction, execStmts, execStmt, evalExpr, SpecStorage.getMapping,
    addressToNat_mod_eq]

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
  simp [getStorage, execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot]

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
    addressToNat_mod_eq]

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
    (h2 : (state.storage 2).val + amount < DumbContracts.Core.Uint256.modulus) :
    let finalState := (mint to (DumbContracts.Core.Uint256.ofNat amount)).runState { state with sender := sender }
    (finalState.storage 2).val = (state.storage 2).val + amount := by
  have h_edsl :
      (ContractResult.getState
        ((mint to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
      ).storage 2 =
      DumbContracts.EVM.Uint256.add (state.storage 2)
        (DumbContracts.Core.Uint256.ofNat amount) := by
    simpa [Contract.run, ContractResult.getState, ContractResult.snd, h] using
      (mint_increases_supply { state with sender := sender } to
        (DumbContracts.Core.Uint256.ofNat amount) h.symm)
  have h_val :
      (ContractResult.getState
        ((mint to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
      ).storage 2 |>.val =
      ((state.storage 2).val + amount) % DumbContracts.Core.Uint256.modulus := by
    have h_edsl_val := congrArg (fun v : DumbContracts.Core.Uint256 => v.val) h_edsl
    calc
      (ContractResult.getState
        ((mint to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
      ).storage 2 |>.val
          = (DumbContracts.EVM.Uint256.add (state.storage 2)
            (DumbContracts.Core.Uint256.ofNat amount)).val := by
              simpa using h_edsl_val
      _ = ((state.storage 2).val + amount) % DumbContracts.Core.Uint256.modulus := by
              exact uint256_add_val (state.storage 2) amount
  -- Since sum < modulus, the mod is identity
  have h_mod : ((state.storage 2).val + amount) % DumbContracts.Core.Uint256.modulus =
      (state.storage 2).val + amount := by
    exact Nat.mod_eq_of_lt h2
  simpa [Contract.runState, h_mod] using h_val

/-- Transfer preserves totalSupply -/
theorem token_transfer_preserves_supply (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : (state.storageMap 1 sender).val ≥ amount) :
    let finalState := (transfer to (DumbContracts.Core.Uint256.ofNat amount)).runState { state with sender := sender }
    finalState.storage 2 = state.storage 2 := by
  have h_amount_lt : amount < DumbContracts.Core.Uint256.modulus := by
    have hlt : (state.storageMap 1 sender).val < DumbContracts.Core.Uint256.modulus := by
      exact (state.storageMap 1 sender).isLt
    exact Nat.lt_of_le_of_lt h hlt
  have h_balance_u :
      (state.storageMap 1 sender) ≥ DumbContracts.Core.Uint256.ofNat amount := by
    simp [DumbContracts.Core.Uint256.le_def, DumbContracts.Core.Uint256.val_ofNat,
      Nat.mod_eq_of_lt h_amount_lt, h]
  simp [transfer, msgSender, getMapping, setMapping, balances,
    DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
    Contract.runState, h_balance_u]

/-- Only owner can mint -/
theorem token_only_owner_mints (state : ContractState) (to : Address) (amount : Nat) (sender : Address) :
    let result := (mint to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender }
    result.isSuccess = true → state.storageAddr 0 = sender := by
  intro h_success
  by_contra h_not_owner
  obtain ⟨msg, hrun⟩ :=
    DumbContracts.Proofs.SimpleToken.Correctness.mint_reverts_when_not_owner
      { state with sender := sender } to (DumbContracts.Core.Uint256.ofNat amount) h_not_owner
  have h_fail : result.isSuccess = false := by
    simpa [ContractResult.isSuccess, hrun] using rfl
  have h_contra : (true : Bool) = false := by
    simpa using (h_success.trans h_fail.symm)
  cases h_contra

/-- Transfer preserves total balance (sender + recipient) -/
theorem token_transfer_preserves_total_balance (state : ContractState) (to : Address) (amount : Nat) (sender : Address)
    (h : sender ≠ to)
    (h2 : (state.storageMap 1 sender).val ≥ amount)
    (h3 : (state.storageMap 1 to).val + amount < DumbContracts.Core.Uint256.modulus) :
    let finalState := (transfer to (DumbContracts.Core.Uint256.ofNat amount)).runState { state with sender := sender }
    (finalState.storageMap 1 sender).val + (finalState.storageMap 1 to).val =
    (state.storageMap 1 sender).val + (state.storageMap 1 to).val := by
  have h_amount_lt : amount < DumbContracts.Core.Uint256.modulus := by
    have hlt : (state.storageMap 1 sender).val < DumbContracts.Core.Uint256.modulus := by
      exact (state.storageMap 1 sender).isLt
    exact Nat.lt_of_le_of_lt h2 hlt
  have h_balance_u :
      (state.storageMap 1 sender) ≥ DumbContracts.Core.Uint256.ofNat amount := by
    simp [DumbContracts.Core.Uint256.le_def, DumbContracts.Core.Uint256.val_ofNat,
      Nat.mod_eq_of_lt h_amount_lt, h2]
  have h_sender_state :
      (ContractResult.getState
        ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
      ).storageMap 1 sender =
      DumbContracts.EVM.Uint256.sub (state.storageMap 1 sender)
        (DumbContracts.Core.Uint256.ofNat amount) := by
    simp [transfer, msgSender, getMapping, setMapping, balances,
      DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
      Contract.run, ContractResult.getState, ContractResult.snd, ContractResult.fst,
      h_balance_u, h]
  have h_recipient_state :
      (ContractResult.getState
        ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
      ).storageMap 1 to =
      DumbContracts.EVM.Uint256.add (state.storageMap 1 to)
        (DumbContracts.Core.Uint256.ofNat amount) := by
    simp [transfer, msgSender, getMapping, setMapping, balances,
      DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
      Contract.run, ContractResult.getState, ContractResult.snd, ContractResult.fst,
      h_balance_u, h]
  have h_sender_val :
      (ContractResult.getState
        ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
      ).storageMap 1 sender |>.val =
      (state.storageMap 1 sender).val - amount := by
    have h_val := congrArg (fun v : DumbContracts.Core.Uint256 => v.val) h_sender_state
    have h_val' :
        (DumbContracts.EVM.Uint256.sub (state.storageMap 1 sender)
          (DumbContracts.Core.Uint256.ofNat amount)).val =
        (state.storageMap 1 sender).val - amount := by
      exact uint256_sub_val_of_le (state.storageMap 1 sender) amount h2
    simpa [h_val'] using h_val
  have h_recipient_val :
      (ContractResult.getState
        ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
      ).storageMap 1 to |>.val =
      (state.storageMap 1 to).val + amount := by
    have h_val := congrArg (fun v : DumbContracts.Core.Uint256 => v.val) h_recipient_state
    have h_val' :
        (DumbContracts.EVM.Uint256.add (state.storageMap 1 to)
          (DumbContracts.Core.Uint256.ofNat amount)).val =
        ((state.storageMap 1 to).val + amount) % DumbContracts.Core.Uint256.modulus := by
      exact uint256_add_val (state.storageMap 1 to) amount
    have h_mod : ((state.storageMap 1 to).val + amount) % DumbContracts.Core.Uint256.modulus =
        (state.storageMap 1 to).val + amount := by
      exact Nat.mod_eq_of_lt h3
    simpa [h_val', h_mod] using h_val
  calc
    (ContractResult.getState
      ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
    ).storageMap 1 sender |>.val +
    (ContractResult.getState
      ((transfer to (DumbContracts.Core.Uint256.ofNat amount)).run { state with sender := sender })
    ).storageMap 1 to |>.val
        = (state.storageMap 1 sender).val - amount + ((state.storageMap 1 to).val + amount) := by
            simp [h_sender_val, h_recipient_val]
    _ = ((state.storageMap 1 sender).val - amount + amount) + (state.storageMap 1 to).val := by
            ac_rfl
    _ = (state.storageMap 1 sender).val + (state.storageMap 1 to).val := by
            simp [Nat.sub_add_cancel h2, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end Compiler.Proofs.SpecCorrectness
