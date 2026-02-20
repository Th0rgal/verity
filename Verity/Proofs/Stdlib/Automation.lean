/-
  Verity.Proofs.Stdlib.Automation

  Helper lemmas and automation for proving specification correctness.

  This module provides proven lemmas for Contract monad operations,
  storage operations, and common proof patterns.

  ## Sections

  - Contract Result Lemmas: `isSuccess`, `getState` for success/revert
  - Basic Storage Operation Lemmas: `getStorage`/`setStorage` runState/runValue
  - Address Storage Lemmas: `getStorageAddr`/`setStorageAddr` runState/runValue
  - Mapping Storage Lemmas: `getMapping`/`setMapping` runState/runValue
  - Require Lemmas: `require_true/false_isSuccess`, `require_state`
  - Address Equality: `address_beq` lemmas
  - Spec Storage Helpers: slot/mapping field access
  - Uint256 Arithmetic: `add`/`sub` value lemmas, `safeSub`/`safeAdd`
  - Well-Formedness Preservation: `wf_of_state_eq` for read-only ops
  - Generic Storage Preservation: cross-type preservation for setStorage/setStorageAddr/setMapping

  Status: All lemmas fully proven with zero sorry, zero axioms.
  Note: addressToNat_injective is now a provable theorem (was an axiom when Address = String).
-/

import Verity.Core
import Verity.Stdlib.Math
import Verity.EVM.Uint256
import Verity.Proofs.Stdlib.SpecInterpreter

namespace Verity.Proofs.Stdlib.Automation

open Verity
open Verity.Proofs.Stdlib.SpecInterpreter
open Compiler.ContractSpec

/-!
## Index Normalization Helpers

Lean 4.22 is less eager to reduce `List.findIdx?` inside large interpreter terms.
These simp lemmas keep field/parameter lookup deterministic in spec-correctness proofs.
-/

@[simp] theorem findIdx_owner_ownedCounter :
    List.findIdx? (fun x : Field => x.name == "owner")
      ([{ name := "owner", ty := FieldType.address },
        { name := "count", ty := FieldType.uint256 }] : List Field) = some 0 := by
  decide

@[simp] theorem findIdx_owner_ownedCounter_decide :
    List.findIdx? (fun x : Field => decide (x.name = "owner"))
      ([{ name := "owner", ty := FieldType.address },
        { name := "count", ty := FieldType.uint256 }] : List Field) = some 0 := by
  decide

@[simp] theorem findIdx_count_ownedCounter :
    List.findIdx? (fun x : Field => x.name == "count")
      ([{ name := "owner", ty := FieldType.address },
        { name := "count", ty := FieldType.uint256 }] : List Field) = some 1 := by
  decide

@[simp] theorem findIdx_count_ownedCounter_decide :
    List.findIdx? (fun x : Field => decide (x.name = "count"))
      ([{ name := "owner", ty := FieldType.address },
        { name := "count", ty := FieldType.uint256 }] : List Field) = some 1 := by
  decide

@[simp] theorem findIdx_count_safeCounter :
    List.findIdx? (fun x : Field => x.name == "count")
      ([{ name := "count", ty := FieldType.uint256 }] : List Field) = some 0 := by
  decide

@[simp] theorem findIdx_count_safeCounter_decide :
    List.findIdx? (fun x : Field => decide (x.name = "count"))
      ([{ name := "count", ty := FieldType.uint256 }] : List Field) = some 0 := by
  decide

@[simp] theorem findIdx_balances_simpleToken :
    List.findIdx? (fun x : Field => x.name == "balances")
      ([{ name := "owner", ty := FieldType.address },
        { name := "balances", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address) },
        { name := "totalSupply", ty := FieldType.uint256 }] : List Field) = some 1 := by
  decide

@[simp] theorem findIdx_balances_simpleToken_decide :
    List.findIdx? (fun x : Field => decide (x.name = "balances"))
      ([{ name := "owner", ty := FieldType.address },
        { name := "balances", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address) },
        { name := "totalSupply", ty := FieldType.uint256 }] : List Field) = some 1 := by
  decide

@[simp] theorem findIdx_owner_simpleToken :
    List.findIdx? (fun x : Field => x.name == "owner")
      ([{ name := "owner", ty := FieldType.address },
        { name := "balances", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address) },
        { name := "totalSupply", ty := FieldType.uint256 }] : List Field) = some 0 := by
  decide

@[simp] theorem findIdx_owner_simpleToken_decide :
    List.findIdx? (fun x : Field => decide (x.name = "owner"))
      ([{ name := "owner", ty := FieldType.address },
        { name := "balances", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address) },
        { name := "totalSupply", ty := FieldType.uint256 }] : List Field) = some 0 := by
  decide

@[simp] theorem findIdx_totalSupply_simpleToken :
    List.findIdx? (fun x : Field => x.name == "totalSupply")
      ([{ name := "owner", ty := FieldType.address },
        { name := "balances", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address) },
        { name := "totalSupply", ty := FieldType.uint256 }] : List Field) = some 2 := by
  decide

@[simp] theorem findIdx_totalSupply_simpleToken_decide :
    List.findIdx? (fun x : Field => decide (x.name = "totalSupply"))
      ([{ name := "owner", ty := FieldType.address },
        { name := "balances", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address) },
        { name := "totalSupply", ty := FieldType.uint256 }] : List Field) = some 2 := by
  decide

@[simp] theorem findIdx_balances_ledger :
    List.findIdx? (fun x : Field => x.name == "balances")
      ([{ name := "balances", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address) }] : List Field) = some 0 := by
  decide

@[simp] theorem findIdx_balances_ledger_decide :
    List.findIdx? (fun x : Field => decide (x.name = "balances"))
      ([{ name := "balances", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address) }] : List Field) = some 0 := by
  decide

@[simp] theorem findIdx_param_newOwner :
    List.findIdx? (fun x => x == "newOwner") ["newOwner"] = some 0 := by
  decide

@[simp] theorem findIdx_param_newOwner_decide :
    List.findIdx? (fun x => decide (x = "newOwner")) ["newOwner"] = some 0 := by
  decide

@[simp] theorem findIdx_param_initialOwner :
    List.findIdx? (fun x => x == "initialOwner") ["initialOwner"] = some 0 := by
  decide

@[simp] theorem findIdx_param_initialOwner_decide :
    List.findIdx? (fun x => decide (x = "initialOwner")) ["initialOwner"] = some 0 := by
  decide

@[simp] theorem findIdx_param_to_to_amount :
    List.findIdx? (fun x => x == "to") ["to", "amount"] = some 0 := by
  decide

@[simp] theorem findIdx_param_to_to_amount_decide :
    List.findIdx? (fun x => decide (x = "to")) ["to", "amount"] = some 0 := by
  decide

@[simp] theorem findIdx_param_amount_to_amount :
    List.findIdx? (fun x => x == "amount") ["to", "amount"] = some 1 := by
  decide

@[simp] theorem findIdx_param_amount_to_amount_decide :
    List.findIdx? (fun x => decide (x = "amount")) ["to", "amount"] = some 1 := by
  decide

@[simp] theorem findIdx_param_addr :
    List.findIdx? (fun x => x == "addr") ["addr"] = some 0 := by
  decide

@[simp] theorem findIdx_param_addr_decide :
    List.findIdx? (fun x => decide (x = "addr")) ["addr"] = some 0 := by
  decide

@[simp] theorem findIdx_param_amount_single :
    List.findIdx? (fun x => x == "amount") ["amount"] = some 0 := by
  decide

@[simp] theorem findIdx_param_amount_single_decide :
    List.findIdx? (fun x => decide (x = "amount")) ["amount"] = some 0 := by
  decide

/-!
## Contract Result Lemmas
-/

-- Lemmas for isSuccess
@[simp]
theorem isSuccess_success {α : Type} (a : α) (s : ContractState) :
    (ContractResult.success a s).isSuccess = true := rfl

@[simp]
theorem isSuccess_revert {α : Type} (msg : String) (s : ContractState) :
    (ContractResult.revert msg s : ContractResult α).isSuccess = false := rfl

-- Lemmas for getState
@[simp]
theorem getState_success {α : Type} (a : α) (s : ContractState) :
    (ContractResult.success a s).getState = s := rfl

@[simp]
theorem getState_revert {α : Type} (msg : String) (s : ContractState) :
    (ContractResult.revert msg s : ContractResult α).getState = s := rfl

/-!
## Basic Storage Operation Lemmas
-/

-- getStorage preserves state
theorem getStorage_runState (slot : StorageSlot Uint256) (state : ContractState) :
    (getStorage slot).runState state = state := by
  simp [getStorage, Contract.runState]

-- setStorage updates the state
theorem setStorage_runState (slot : StorageSlot Uint256) (value : Uint256) (state : ContractState) :
    (setStorage slot value).runState state =
      { state with storage := fun s => if s == slot.slot then value else state.storage s } := by
  simp [setStorage, Contract.runState]

-- getStorage returns correct value
theorem getStorage_runValue (slot : StorageSlot Uint256) (state : ContractState) :
    (getStorage slot).runValue state = state.storage slot.slot := by
  simp [getStorage, Contract.runValue]

-- After setStorage, getStorage returns the value
theorem setStorage_getStorage (slot : StorageSlot Uint256) (value : Uint256) (state : ContractState) :
    (getStorage slot).runValue ((setStorage slot value).runState state) = value := by
  simp [setStorage, getStorage, Contract.runState, Contract.runValue]

-- getStorage for different slot is unchanged after setStorage
theorem setStorage_getStorage_diff (slot1 slot2 : StorageSlot Uint256) (value : Uint256) (state : ContractState)
    (h : slot1.slot ≠ slot2.slot) :
    (getStorage slot2).runValue ((setStorage slot1 value).runState state) =
    state.storage slot2.slot := by
  unfold setStorage getStorage Contract.runState Contract.runValue
  by_cases h_eq : slot2.slot = slot1.slot
  · exact (h h_eq.symm).elim
  · simp [h_eq]

/-!
## Monadic Composition Lemmas

These lemmas help with proving correctness of functions that use bind (>>=).
-/

-- Left identity: binding a pure value is just function application.
@[simp]
theorem bind_pure_left {α β : Type} (a : α) (f : α → Contract β) :
    Verity.bind (Verity.pure a) f = f a := by
  funext state
  simp [Verity.bind, Verity.pure]

-- Right identity: binding to pure preserves the original computation.
@[simp]
theorem bind_pure_right {α : Type} (m : Contract α) :
    Verity.bind m Verity.pure = m := by
  funext state
  unfold Verity.bind Verity.pure
  cases h : m state <;> simp [h]

-- Associativity: nested binds can be reassociated.
@[simp]
theorem bind_assoc {α β γ : Type} (m : Contract α) (f : α → Contract β) (g : β → Contract γ) :
    Verity.bind (Verity.bind m f) g = Verity.bind m (fun a => Verity.bind (f a) g) := by
  funext state
  unfold Verity.bind
  cases h : m state <;> simp [h]

-- Lemma for getStorage >> setStorage pattern (the most common pattern)
@[simp]
theorem bind_getStorage_setStorage_runState (slot : StorageSlot Uint256) (f : Uint256 → Uint256) (state : ContractState) :
    (Verity.bind (getStorage slot) (fun val => setStorage slot (f val))).runState state =
      { state with storage := fun s => if s == slot.slot then f (state.storage slot.slot) else state.storage s } := by
  simp [Verity.bind, getStorage, setStorage, Contract.runState]

-- Bind success propagation: if bind succeeds, first action succeeded
theorem bind_isSuccess_left {α β : Type} (m1 : Contract α) (m2 : α → Contract β) (state : ContractState) :
    ((Verity.bind m1 m2).run state).isSuccess = true →
    (m1.run state).isSuccess = true := by
  intro h_success
  -- Strategy: case analysis on m1 state
  -- Note: Contract.run is just function application, so m1.run state = m1 state
  cases h_result : m1 state
  case success val s' =>
    -- When m1 succeeds, isSuccess is trivially true
    simp [Contract.run, h_result, ContractResult.isSuccess]
  case revert msg s' =>
    -- When m1 reverts, bind also reverts, so isSuccess = false
    -- This contradicts h_success
    unfold Verity.bind Contract.run at h_success
    simp [h_result, ContractResult.isSuccess] at h_success

/-!
## Address Storage Lemmas
-/

-- getStorageAddr preserves state
theorem getStorageAddr_runState (slot : StorageSlot Address) (state : ContractState) :
    (getStorageAddr slot).runState state = state := by
  simp [getStorageAddr, Contract.runState]

-- setStorageAddr updates the state
theorem setStorageAddr_runState (slot : StorageSlot Address) (value : Address) (state : ContractState) :
    (setStorageAddr slot value).runState state =
      { state with storageAddr := fun s => if s == slot.slot then value else state.storageAddr s } := by
  simp [setStorageAddr, Contract.runState]

-- getStorageAddr returns correct value
theorem getStorageAddr_runValue (slot : StorageSlot Address) (state : ContractState) :
    (getStorageAddr slot).runValue state = state.storageAddr slot.slot := by
  simp [getStorageAddr, Contract.runValue]

/-!
## Address Encoding Lemmas
-/

-- Address values are always less than 2^160 (the address modulus).
theorem addressToNat_lt_modulus (addr : Address) :
    addr.val < addressModulus := addr.isLt

@[simp] theorem addressToNat_mod_eq (addr : Address) :
    addr.val % addressModulus = addr.val := by
  exact Nat.mod_eq_of_lt (addressToNat_lt_modulus addr)

@[simp] theorem addressToNat_beq_self (addr : Address) :
    (addr.val == addr.val) = true := by
  simp

-- Injectivity is now provable from the structure definition (was an axiom!).
theorem addressToNat_injective :
    ∀ (a b : Address), a.val = b.val → a = b :=
  fun _ _ h => Verity.Core.Address.ext h

/-!
## Mapping Operation Lemmas
-/

-- getMapping preserves state
theorem getMapping_runState (slot : StorageSlot (Address → Uint256)) (key : Address) (state : ContractState) :
    (getMapping slot key).runState state = state := by
  simp [getMapping, Contract.runState]

-- getMapping returns correct value
theorem getMapping_runValue (slot : StorageSlot (Address → Uint256)) (key : Address) (state : ContractState) :
    (getMapping slot key).runValue state = state.storageMap slot.slot key := by
  simp [getMapping, Contract.runValue]

/-!
## List Lookup Lemmas
-/

-- Local variable lookups in the spec interpreter.
@[simp] theorem lookup_senderBal (recipientBal senderBal : Nat) :
    (List.lookup "senderBal" [("recipientBal", recipientBal), ("senderBal", senderBal)]).getD 0 =
      senderBal := by
  simp [List.lookup, List.lookup_cons]

@[simp] theorem lookup_recipientBal (recipientBal senderBal : Nat) :
    (List.lookup "recipientBal" [("recipientBal", recipientBal), ("senderBal", senderBal)]).getD 0 =
      recipientBal := by
  simp [List.lookup, List.lookup_cons]

-- Local variable lookups when transfer introduces sameAddr/delta/amountDelta.
@[simp] theorem lookup_senderBal_with_delta (amountDelta delta sameAddr recipientBal senderBal : Nat) :
    (List.lookup "senderBal"
        [("amountDelta", amountDelta), ("delta", delta), ("sameAddr", sameAddr),
          ("recipientBal", recipientBal), ("senderBal", senderBal)]).getD 0 =
      senderBal := by
  simp [List.lookup, List.lookup_cons]

@[simp] theorem lookup_recipientBal_with_delta (amountDelta delta sameAddr recipientBal senderBal : Nat) :
    (List.lookup "recipientBal"
        [("amountDelta", amountDelta), ("delta", delta), ("sameAddr", sameAddr),
          ("recipientBal", recipientBal), ("senderBal", senderBal)]).getD 0 =
      recipientBal := by
  simp [List.lookup, List.lookup_cons]

@[simp] theorem lookup_sameAddr_with_delta (amountDelta delta sameAddr recipientBal senderBal : Nat) :
    (List.lookup "sameAddr"
        [("amountDelta", amountDelta), ("delta", delta), ("sameAddr", sameAddr),
          ("recipientBal", recipientBal), ("senderBal", senderBal)]).getD 0 =
      sameAddr := by
  simp [List.lookup, List.lookup_cons]

@[simp] theorem lookup_delta_with_delta (amountDelta delta sameAddr recipientBal senderBal : Nat) :
    (List.lookup "delta"
        [("amountDelta", amountDelta), ("delta", delta), ("sameAddr", sameAddr),
          ("recipientBal", recipientBal), ("senderBal", senderBal)]).getD 0 =
      delta := by
  simp [List.lookup, List.lookup_cons]

@[simp] theorem lookup_amountDelta_with_delta (amountDelta delta sameAddr recipientBal senderBal : Nat) :
    (List.lookup "amountDelta"
        [("amountDelta", amountDelta), ("delta", delta), ("sameAddr", sameAddr),
          ("recipientBal", recipientBal), ("senderBal", senderBal)]).getD 0 =
      amountDelta := by
  simp [List.lookup, List.lookup_cons]

-- Mapping lookups for two-address lists.
@[simp] theorem lookup_addr_first (k1 k2 v1 v2 : Nat) :
    (List.lookup k1 [(k1, v1), (k2, v2)]).getD 0 = v1 := by
  simp [List.lookup, List.lookup_cons]

@[simp] theorem lookup_addr_second (k1 k2 v1 v2 : Nat) (h : k1 ≠ k2) :
    (List.lookup k2 [(k1, v1), (k2, v2)]).getD 0 = v2 := by
  cases h_eq : (k2 == k1) with
  | false =>
      simp [List.lookup, h_eq]
  | true =>
      have : k2 = k1 := by
        exact (beq_iff_eq).1 h_eq
      exact (False.elim (h this.symm))

-- Slot lookups for the common two-slot layout.
@[simp] theorem lookup_slot_first (v0 v1 : Nat) :
    (List.lookup 0 [(0, v0), (1, v1)]).getD 0 = v0 := by
  simp [List.lookup, List.lookup_cons]

@[simp] theorem lookup_slot_second (v0 v1 : Nat) :
    (List.lookup 1 [(0, v0), (1, v1)]).getD 0 = v1 := by
  simp [List.lookup, List.lookup_cons]

/-!
## msgSender Lemmas
-/

-- msgSender preserves state
theorem msgSender_runState (state : ContractState) :
    msgSender.runState state = state := by
  simp [msgSender, Contract.runState]

-- msgSender returns sender
theorem msgSender_runValue (state : ContractState) :
    msgSender.runValue state = state.sender := by
  simp [msgSender, Contract.runValue]

/-!
## require Lemmas
-/

-- require with true condition is success
theorem require_true_isSuccess (cond : Bool) (msg : String) (state : ContractState)
    (h : cond = true) :
    ((require cond msg).run state).isSuccess = true := by
  simp [require, h]

-- require with false condition is not success
theorem require_false_isSuccess (cond : Bool) (msg : String) (state : ContractState)
    (h : cond = false) :
    ((require cond msg).run state).isSuccess = false := by
  simp [require, h]

-- If require succeeds, the condition must have been true (reverse direction)
theorem require_success_implies_cond (cond : Bool) (msg : String) (state : ContractState) :
    ((require cond msg).run state).isSuccess = true →
    cond = true := by
  intro h_success
  -- Strategy: case analysis on cond
  cases cond
  case false =>
    -- When cond = false, require returns revert, which has isSuccess = false
    -- This contradicts h_success
    unfold require Contract.run at h_success
    simp [ContractResult.isSuccess] at h_success
  case true =>
    -- When cond = true, we're done
    rfl

-- require preserves state regardless of branch
@[simp] theorem require_state (cond : Bool) (msg : String) (state : ContractState) :
    (require cond msg).runState state = state := by
  by_cases h : cond
  · simp [require, Contract.runState, h]
  · simp [require, Contract.runState, h]

-- If the guard is true, binding after require is exactly the continuation.
@[simp] theorem require_bind_true_run (cond : Bool) (msg : String) (k : Unit → Contract α)
    (state : ContractState) (h : cond = true) :
    (Verity.bind (require cond msg) k).run state = (k ()) state := by
  subst h
  simp [Verity.bind, require, Contract.run]

-- If the guard is false, bind short-circuits to revert and never runs continuation.
@[simp] theorem require_bind_false_run (cond : Bool) (msg : String) (k : Unit → Contract α)
    (state : ContractState) (h : cond = false) :
    (Verity.bind (require cond msg) k).run state = ContractResult.revert msg state := by
  subst h
  simp [Verity.bind, require, Contract.run]

/-!
## Address Equality Lemmas
-/

-- Address beq reflects equality.
theorem address_beq_eq_true_iff_eq (a b : Address) :
    (a == b) = true ↔ a = b := by
  simp only [beq_iff_eq]

/-- Address beq is false when addresses are not equal. -/
theorem address_beq_false_of_ne (a b : Address) (h : a ≠ b) :
    (a == b) = false :=
  beq_eq_false_iff_ne.mpr h

/-- Distinct addresses have distinct Nat values. -/
theorem addressToNat_ne_of_ne (a b : Address) (h : a ≠ b) :
    a.val ≠ b.val := by
  intro h_nat
  exact h (addressToNat_injective a b h_nat)

/-- Address val beq is false when addresses are not equal. -/
theorem addressToNat_beq_false_of_ne (a b : Address) (h : a ≠ b) :
    (a.val == b.val) = false :=
  beq_eq_false_iff_ne.mpr (addressToNat_ne_of_ne a b h)

/-!
## Uint256 Arithmetic Lemmas
-/

/-- 1 mod modulus is 1 (used pervasively in spec interpreter proofs). -/
@[simp] theorem one_mod_modulus : (1 % Verity.Core.Uint256.modulus) = 1 :=
  Nat.mod_eq_of_lt (by decide : (1 : Nat) < Verity.Core.Uint256.modulus)

/-- EVM.Uint256.add is definitionally equal to HAdd (+). -/
theorem evm_add_eq_hadd (a b : Verity.Core.Uint256) :
    Verity.EVM.Uint256.add a b = a + b := rfl

-- Helper: EVM add (Uint256) matches modular Nat addition.
theorem uint256_add_val (a : Verity.Core.Uint256) (amount : Nat) :
    (Verity.EVM.Uint256.add a (Verity.Core.Uint256.ofNat amount)).val =
      (a.val + amount) % Verity.Core.Uint256.modulus := by
  cases a with
  | mk aval hlt =>
      have haval : aval % Verity.Core.Uint256.modulus = aval := Nat.mod_eq_of_lt hlt
      calc
        (Verity.EVM.Uint256.add (Verity.Core.Uint256.mk aval hlt)
              (Verity.Core.Uint256.ofNat amount)).val
            = (aval + amount % Verity.Core.Uint256.modulus) % Verity.Core.Uint256.modulus := by
                simp [Verity.EVM.Uint256.add, Verity.Core.Uint256.add,
                  Verity.Core.Uint256.val_ofNat, -Verity.Core.Uint256.ofNat_add]
        _ = ((aval % Verity.Core.Uint256.modulus) + (amount % Verity.Core.Uint256.modulus))
              % Verity.Core.Uint256.modulus := by
                simp [haval]
        _ = (aval + amount) % Verity.Core.Uint256.modulus := by
                exact (Nat.add_mod _ _ _).symm

-- Helper: EVM sub (Uint256) matches the EDSL modular subtraction formula.
theorem uint256_sub_val (a : Verity.Core.Uint256) (amount : Nat) :
    (Verity.EVM.Uint256.sub a (Verity.Core.Uint256.ofNat amount)).val =
      (if amount % Verity.Core.Uint256.modulus ≤ a.val then
        a.val - amount % Verity.Core.Uint256.modulus
      else
        Verity.Core.Uint256.modulus -
          (amount % Verity.Core.Uint256.modulus - a.val)) := by
  have h_amount_lt : amount % Verity.Core.Uint256.modulus < Verity.Core.Uint256.modulus := by
    exact Nat.mod_lt _ Verity.Core.Uint256.modulus_pos
  by_cases h_le : amount % Verity.Core.Uint256.modulus ≤ a.val
  · have h_lt : a.val - amount % Verity.Core.Uint256.modulus < Verity.Core.Uint256.modulus := by
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
    simp [Verity.EVM.Uint256.sub, Verity.Core.Uint256.sub, h_le,
      Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_lt]
  · have h_not_le : ¬ amount % Verity.Core.Uint256.modulus ≤ a.val := h_le
    have h_pos : 0 < amount % Verity.Core.Uint256.modulus - a.val := by
      exact Nat.sub_pos_of_lt (Nat.lt_of_not_ge h_not_le)
    have h_le_x : amount % Verity.Core.Uint256.modulus - a.val ≤ Verity.Core.Uint256.modulus := by
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_amount_lt)
    have h_lt_add :
        Verity.Core.Uint256.modulus <
          (amount % Verity.Core.Uint256.modulus - a.val) + Verity.Core.Uint256.modulus := by
      exact Nat.lt_add_of_pos_left h_pos
    have h_lt :
        Verity.Core.Uint256.modulus - (amount % Verity.Core.Uint256.modulus - a.val) <
          Verity.Core.Uint256.modulus := by
      exact Nat.sub_lt_left_of_lt_add h_le_x h_lt_add
    simp [Verity.EVM.Uint256.sub, Verity.Core.Uint256.sub, h_not_le,
      Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt h_lt]

-- Helper: EVM sub (Uint256) matches Nat subtraction when no underflow.
theorem uint256_sub_val_of_le (a : Verity.Core.Uint256) (amount : Nat)
    (h : a.val ≥ amount) :
    (Verity.EVM.Uint256.sub a (Verity.Core.Uint256.ofNat amount)).val =
      a.val - amount := by
  have h_amount_lt : amount < Verity.Core.Uint256.modulus := by
    exact Nat.lt_of_le_of_lt h a.isLt
  have h_le : (Verity.Core.Uint256.ofNat amount : Nat) ≤ (a : Nat) := by
    simp [Verity.Core.Uint256.coe_ofNat, Nat.mod_eq_of_lt h_amount_lt, h]
  have h_sub : ((Verity.EVM.Uint256.sub a (Verity.Core.Uint256.ofNat amount)
      : Verity.Core.Uint256) : Nat) = (a : Nat) - (Verity.Core.Uint256.ofNat amount : Nat) := by
    exact Verity.EVM.Uint256.sub_eq_of_le h_le
  simp [Verity.Core.Uint256.coe_ofNat, Nat.mod_eq_of_lt h_amount_lt] at h_sub
  simpa using h_sub

-- getSlot from setSlot (same slot)
theorem SpecStorage_getSlot_setSlot_same (storage : SpecStorage) (slot : Nat) (value : Nat) :
    (storage.setSlot slot value).getSlot slot = value := by
  simp [SpecStorage.getSlot, SpecStorage.setSlot, List.lookup]

theorem lookup_filter_ne {β : Type} (k k' : Nat) (h : k ≠ k') (xs : List (Nat × β)) :
    (xs.filter (fun kv => kv.1 ≠ k')).lookup k = xs.lookup k := by
  induction xs with
  | nil =>
      simp
  | cons kv xs ih =>
      cases kv with
      | mk k0 v0 =>
          by_cases hk0 : k0 = k'
          · -- Filter drops this head.
            have hk0ne : k ≠ k0 := by
              intro hkk
              exact h (hkk.trans hk0)
            calc
              (List.filter (fun kv => kv.1 ≠ k') ((k0, v0) :: xs)).lookup k
                  = (List.filter (fun kv => kv.1 ≠ k') xs).lookup k := by
                      simp [List.filter, hk0]
              _ = xs.lookup k := ih
              _ = ((k0, v0) :: xs).lookup k := by
                      have hk0false : (k == k0) = false := by
                        exact (beq_eq_false_iff_ne.mpr hk0ne)
                      simp [List.lookup, hk0false]
          · -- Filter keeps this head.
            by_cases hk : k = k0
            · simp [List.filter, List.lookup, hk0, beq_iff_eq, hk]
            · calc
                (List.filter (fun kv => kv.1 ≠ k') ((k0, v0) :: xs)).lookup k
                    = (List.filter (fun kv => kv.1 ≠ k') xs).lookup k := by
                        have hkfalse : (k == k0) = false := by
                          exact (beq_eq_false_iff_ne.mpr hk)
                        simp [List.filter, List.lookup, hk0, hkfalse]
                _ = xs.lookup k := ih
                _ = ((k0, v0) :: xs).lookup k := by
                        have hkfalse : (k == k0) = false := by
                          exact (beq_eq_false_iff_ne.mpr hk)
                        simp [List.lookup, hkfalse]

-- lookup skips head when key is different
theorem lookup_cons_ne {α β : Type} [BEq α] [LawfulBEq α]
    (k k' : α) (v : β) (xs : List (α × β)) (h : k ≠ k') :
    (List.lookup k ((k', v) :: xs)) = List.lookup k xs := by
  have hfalse : (k == k') = false := by
    exact (beq_eq_false_iff_ne.mpr h)
  simp [List.lookup, hfalse]

-- getSlot from setSlot (different slot)
theorem SpecStorage_getSlot_setSlot_diff (storage : SpecStorage) (slot1 slot2 : Nat) (value : Nat)
    (h : slot1 ≠ slot2) :
    (storage.setSlot slot1 value).getSlot slot2 = storage.getSlot slot2 := by
  -- After unfolding: List.lookup slot2 ((slot1, value) :: filtered)
  -- Since slot2 ≠ slot1, lookup skips head and searches in filtered list
  -- Key lemma needed: List.lookup k (List.filter (·.1 ≠ k') xs) = List.lookup k xs when k ≠ k'
  unfold SpecStorage.getSlot SpecStorage.setSlot
  have h' : slot2 ≠ slot1 := by
    intro h2
    exact h h2.symm
  have hfalse : (slot2 == slot1) = false := by
    exact (beq_eq_false_iff_ne.mpr h')
  have hpred : (fun x : Nat × Nat => !decide (x.1 = slot1)) = (fun x : Nat × Nat => decide (x.1 ≠ slot1)) := by
    funext x
    simp [decide_not]
  simp [List.lookup, hfalse, hpred, lookup_filter_ne slot2 slot1 h']

-- getMapping from setMapping (same slot and key) - requires proof
theorem SpecStorage_getMapping_setMapping_same (storage : SpecStorage) (slot : Nat) (key : Nat) (value : Nat) :
    (storage.setMapping slot key value).getMapping slot key = value := by
  simp [SpecStorage.getMapping, SpecStorage.setMapping, List.lookup, beq_iff_eq, lookup_filter_ne]

-- getMapping preserves other slots - requires proof
theorem SpecStorage_getMapping_setMapping_diff_slot (storage : SpecStorage) (slot1 slot2 : Nat) (key : Nat) (value : Nat)
    (h : slot1 ≠ slot2) :
    (storage.setMapping slot1 key value).getMapping slot2 key = storage.getMapping slot2 key := by
  unfold SpecStorage.getMapping SpecStorage.setMapping
  have h' : slot2 ≠ slot1 := by
    intro h2
    exact h h2.symm
  have hfalse : (slot2 == slot1) = false := by
    exact (beq_eq_false_iff_ne.mpr h')
  have hpred : (fun x : Nat × List (Nat × Nat) => !decide (x.1 = slot1)) =
      (fun x : Nat × List (Nat × Nat) => decide (x.1 ≠ slot1)) := by
    funext x
    simp [decide_not]
  simp [List.lookup, hfalse, hpred, lookup_filter_ne slot2 slot1 h']

/-!
## Safe Arithmetic Lemmas

Helper lemmas for reasoning about safe arithmetic operations (safeAdd, safeSub).
-/

-- safeSub returns Some iff no underflow
theorem safeSub_some_iff_ge (a b : Verity.Core.Uint256) :
    (Verity.Stdlib.Math.safeSub a b).isSome ↔ (a : Nat) ≥ (b : Nat) := by
  unfold Verity.Stdlib.Math.safeSub
  split
  · simp; rename_i h; omega
  · simp; rename_i h; omega

-- safeSub returns None iff underflow
theorem safeSub_none_iff_lt (a b : Verity.Core.Uint256) :
    (Verity.Stdlib.Math.safeSub a b).isNone ↔ (a : Nat) < (b : Nat) := by
  unfold Verity.Stdlib.Math.safeSub
  split
  · simp; rename_i h; omega
  · simp; rename_i h; omega

-- When safeSub succeeds, it returns the correct value
theorem safeSub_some_val (a b : Verity.Core.Uint256) (h : (a : Nat) ≥ (b : Nat)) :
    Verity.Stdlib.Math.safeSub a b = some (a - b) := by
  unfold Verity.Stdlib.Math.safeSub
  have h_not : ¬((b : Nat) > (a : Nat)) := by omega
  simp [h_not]

-- safeAdd returns Some iff no overflow
theorem safeAdd_some_iff_le (a b : Verity.Core.Uint256) :
    (Verity.Stdlib.Math.safeAdd a b).isSome ↔
    (a : Nat) + (b : Nat) ≤ Verity.Stdlib.Math.MAX_UINT256 := by
  unfold Verity.Stdlib.Math.safeAdd
  by_cases h : (a : Nat) + (b : Nat) > Verity.Stdlib.Math.MAX_UINT256
  case pos =>
    constructor
    · intro h_some
      simp [h] at h_some
    · intro h_le
      omega
  case neg =>
    constructor
    · intro _
      omega
    · intro _
      simp [h]

-- safeAdd returns None iff overflow
theorem safeAdd_none_iff_gt (a b : Verity.Core.Uint256) :
    (Verity.Stdlib.Math.safeAdd a b).isNone ↔
    (a : Nat) + (b : Nat) > Verity.Stdlib.Math.MAX_UINT256 := by
  unfold Verity.Stdlib.Math.safeAdd
  by_cases h : (a : Nat) + (b : Nat) > Verity.Stdlib.Math.MAX_UINT256
  case pos =>
    constructor
    · intro _; exact h
    · intro _; simp [h]
  case neg =>
    constructor
    · intro h_none
      simp [h] at h_none
    · intro h_gt
      exact absurd h_gt h

-- When safeAdd succeeds, it returns the correct value
theorem safeAdd_some_val (a b : Verity.Core.Uint256)
    (h : (a : Nat) + (b : Nat) ≤ Verity.Stdlib.Math.MAX_UINT256) :
    Verity.Stdlib.Math.safeAdd a b = some (a + b) := by
  unfold Verity.Stdlib.Math.safeAdd
  have h_not : ¬((a : Nat) + (b : Nat) > Verity.Stdlib.Math.MAX_UINT256) := by omega
  simp [h_not]

/-!
## Modular Arithmetic Wraparound Lemmas

These lemmas handle the case where modular addition causes wraparound at MAX_UINT256.
-/

-- Addition by 1 preserves order iff no overflow occurs
theorem add_one_preserves_order_iff_no_overflow (a : Verity.Core.Uint256) :
    ((Verity.Core.Uint256.add a 1) : Nat) > (a : Nat) ↔
    (a : Nat) < Verity.Core.MAX_UINT256 := by
  -- Strategy: case split on whether a is at max or not
  by_cases h : (a : Nat) = Verity.Core.MAX_UINT256
  case pos =>
    -- When a = MAX_UINT256, overflow occurs
    -- (MAX_UINT256 + 1) mod 2^256 = 0, and 0 ≯ MAX_UINT256
    constructor
    · intro h_gt
      -- Show contradiction: (a + 1).val = 0, so 0 > MAX_UINT256 is false
      unfold Verity.Core.Uint256.add at h_gt
      simp [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.val] at h_gt
      rw [h] at h_gt
      -- Now: (MAX_UINT256 + 1) % modulus > MAX_UINT256
      have h_mod : (Verity.Core.MAX_UINT256 + 1) % Verity.Core.Uint256.modulus = 0 := by
        have h_eq : Verity.Core.MAX_UINT256 + 1 = Verity.Core.Uint256.modulus := by
          exact Verity.Core.Uint256.max_uint256_succ_eq_modulus
        rw [h_eq]
        simp [Nat.mod_self]
      rw [h_mod] at h_gt
      -- Now: 0 > MAX_UINT256, which is false
      have h_max_pos : Verity.Core.MAX_UINT256 > 0 := by
        unfold Verity.Core.MAX_UINT256
        omega
      omega
    · intro h_lt
      -- a.val < MAX_UINT256 contradicts h : a.val = MAX_UINT256
      rw [h] at h_lt
      omega
  case neg =>
    -- When a < MAX_UINT256, no overflow occurs
    -- (a + 1) mod 2^256 = a + 1, so (a + 1) > a
    constructor
    · intro _
      -- From a.val ≤ MAX_UINT256 and a.val ≠ MAX_UINT256, we get a.val < MAX_UINT256
      have h_le : (a : Nat) ≤ Verity.Core.MAX_UINT256 := by
        exact Verity.Core.Uint256.val_le_max a
      omega
    · intro h_lt
      -- Show (a + 1).val > a.val when no overflow
      unfold Verity.Core.Uint256.add
      simp [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.val]
      -- Need to show: (a.val + 1) % modulus > a.val
      -- Since a.val < MAX_UINT256, we have a.val + 1 < modulus
      have h_sum_lt : (a : Nat) + 1 < Verity.Core.Uint256.modulus := by
        have h_max : (a : Nat) < Verity.Core.MAX_UINT256 := h_lt
        calc
          (a : Nat) + 1 < Verity.Core.MAX_UINT256 + 1 := by omega
          _ = Verity.Core.Uint256.modulus := by
            exact Verity.Core.Uint256.max_uint256_succ_eq_modulus
      -- When a.val + 1 < modulus, the mod is identity
      have h_mod : ((a : Nat) + 1) % Verity.Core.Uint256.modulus = (a : Nat) + 1 := by
        exact Nat.mod_eq_of_lt h_sum_lt
      rw [h_mod]
      omega

/-!
## Well-Formedness Preservation
-/

/-- Generic: any state predicate is preserved when the operation does not change state.
    Eliminates the repeated 3-line pattern:
    `have h_pres := op_preserves_state s; rw [h_pres]; exact h`
    found in every read-only `*_preserves_wellformedness` proof. -/
theorem wf_of_state_eq (P : ContractState → Prop)
    (s s' : ContractState) (h_eq : s' = s) (h : P s) : P s' := by
  rw [h_eq]; exact h

/-!
## Generic setStorage Preservation

Facts about `setStorage` that hold for ANY slot — not specific to a named slot
like `count` or `storedData`. These eliminate per-contract duplication of
`setStorage_preserves_addr_storage`, `setStorage_preserves_map_storage`, etc.
-/

/-- setStorage on any uint256 slot preserves the address storage. -/
theorem setStorage_preserves_storageAddr (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.storageAddr = state.storageAddr := by
  simp [setStorage]

/-- setStorage on any uint256 slot preserves the mapping storage. -/
theorem setStorage_preserves_storageMap (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.storageMap = state.storageMap := by
  simp [setStorage]

/-- setStorage on any uint256 slot preserves the sender. -/
theorem setStorage_preserves_sender (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.sender = state.sender := by
  simp [setStorage]

/-- setStorage on any uint256 slot preserves the contract address. -/
theorem setStorage_preserves_thisAddress (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.thisAddress = state.thisAddress := by
  simp [setStorage]

/-- setStorage on any uint256 slot preserves other uint256 slots. -/
theorem setStorage_preserves_other_storage (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) (n : Nat) (h : n ≠ slot.slot) :
    ((setStorage slot value).run state).snd.storage n = state.storage n := by
  simp [setStorage, h]

/-- setStorageAddr on any address slot preserves the uint256 storage. -/
theorem setStorageAddr_preserves_storage (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.storage = state.storage := by
  simp [setStorageAddr]

/-- setStorageAddr on any address slot preserves the mapping storage. -/
theorem setStorageAddr_preserves_storageMap (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.storageMap = state.storageMap := by
  simp [setStorageAddr]

/-- setStorageAddr on any address slot preserves the sender. -/
theorem setStorageAddr_preserves_sender (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.sender = state.sender := by
  simp [setStorageAddr]

/-- setStorageAddr on any address slot preserves the contract address. -/
theorem setStorageAddr_preserves_thisAddress (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.thisAddress = state.thisAddress := by
  simp [setStorageAddr]

/-!
## Generic setMapping Preservation
-/

/-- setMapping preserves the uint256 storage. -/
theorem setMapping_preserves_storage (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.storage = state.storage := by
  simp [setMapping]

/-- setMapping preserves the address storage. -/
theorem setMapping_preserves_storageAddr (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.storageAddr = state.storageAddr := by
  simp [setMapping]

/-- setMapping preserves the sender. -/
theorem setMapping_preserves_sender (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.sender = state.sender := by
  simp [setMapping]

/-- setMapping preserves the contract address. -/
theorem setMapping_preserves_thisAddress (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.thisAddress = state.thisAddress := by
  simp [setMapping]

/-!
## Generic msgValue / blockTimestamp / knownAddresses Preservation

Storage mutations never touch context fields or (for non-mapping ops) knownAddresses.
-/

/-- setStorage preserves msgValue. -/
theorem setStorage_preserves_msgValue (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.msgValue = state.msgValue := by
  simp [setStorage]

/-- setStorageAddr preserves msgValue. -/
theorem setStorageAddr_preserves_msgValue (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.msgValue = state.msgValue := by
  simp [setStorageAddr]

/-- setMapping preserves msgValue. -/
theorem setMapping_preserves_msgValue (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.msgValue = state.msgValue := by
  simp [setMapping]

/-- setStorage preserves blockTimestamp. -/
theorem setStorage_preserves_blockTimestamp (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.blockTimestamp = state.blockTimestamp := by
  simp [setStorage]

/-- setStorageAddr preserves blockTimestamp. -/
theorem setStorageAddr_preserves_blockTimestamp (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.blockTimestamp = state.blockTimestamp := by
  simp [setStorageAddr]

/-- setMapping preserves blockTimestamp. -/
theorem setMapping_preserves_blockTimestamp (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.blockTimestamp = state.blockTimestamp := by
  simp [setMapping]

/-- setStorage preserves knownAddresses. -/
theorem setStorage_preserves_knownAddresses (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.knownAddresses = state.knownAddresses := by
  simp [setStorage]

/-- setStorageAddr preserves knownAddresses. -/
theorem setStorageAddr_preserves_knownAddresses (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.knownAddresses = state.knownAddresses := by
  simp [setStorageAddr]

/-!
## Generic Event Preservation

Storage mutations never touch the `events` append-only log.
-/

/-- setStorage on any uint256 slot preserves the event log. -/
theorem setStorage_preserves_events (slot : StorageSlot Uint256) (value : Uint256)
    (state : ContractState) :
    ((setStorage slot value).run state).snd.events = state.events := by
  simp [setStorage]

/-- setStorageAddr on any address slot preserves the event log. -/
theorem setStorageAddr_preserves_events (slot : StorageSlot Address) (value : Address)
    (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.events = state.events := by
  simp [setStorageAddr]

/-- setMapping preserves the event log. -/
theorem setMapping_preserves_events (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.events = state.events := by
  simp [setMapping]

/-!
## Event Emission Helpers

Direct automation lemmas for `emitEvent`.
-/

/-- Emitting an event always succeeds. -/
@[simp] theorem emitEvent_isSuccess (name : String) (args indexedArgs : List Uint256)
    (state : ContractState) :
    ((emitEvent name args indexedArgs).run state).isSuccess = true := by
  simp [emitEvent]

/-- Emitting an event returns unit. -/
@[simp] theorem emitEvent_runValue (name : String) (args indexedArgs : List Uint256)
    (state : ContractState) :
    (emitEvent name args indexedArgs).runValue state = () := by
  simp [emitEvent, Contract.runValue]

/-- Emitting an event updates only the event log by appending one entry. -/
@[simp] theorem emitEvent_runState (name : String) (args indexedArgs : List Uint256)
    (state : ContractState) :
    (emitEvent name args indexedArgs).runState state =
      { state with events := state.events ++ [{ name := name, args := args, indexedArgs := indexedArgs }] } := by
  simp [emitEvent, Contract.runState]

/-- Event log append view of emitEvent. -/
@[simp] theorem emitEvent_events_append (name : String) (args indexedArgs : List Uint256)
    (state : ContractState) :
    ((emitEvent name args indexedArgs).run state).snd.events =
      state.events ++ [{ name := name, args := args, indexedArgs := indexedArgs }] := by
  simp [emitEvent]

/-- Sequential event emission appends in order. -/
theorem emitEvent_emitEvent_events (name1 : String) (args1 indexedArgs1 : List Uint256)
    (name2 : String) (args2 indexedArgs2 : List Uint256) (state : ContractState) :
    ((Verity.bind (emitEvent name1 args1 indexedArgs1)
        (fun _ => emitEvent name2 args2 indexedArgs2)).run state).snd.events =
      state.events ++
        [{ name := name1, args := args1, indexedArgs := indexedArgs1 },
         { name := name2, args := args2, indexedArgs := indexedArgs2 }] := by
  simp [Contract.run, Verity.bind, emitEvent, List.append_assoc]

/-!
## MAX_UINT256 / modulus Helper Lemmas

Convenience lemmas that eliminate the repeated inline derivation of
`MAX_UINT256 < modulus` and `n ≤ MAX_UINT256 → n < modulus`.
-/

/-- modulus = MAX_UINT256 + 1. Useful for omega-based proofs. -/
theorem modulus_eq_max_uint256_succ :
    Verity.Core.Uint256.modulus = Verity.Stdlib.Math.MAX_UINT256 + 1 :=
  Verity.Core.Uint256.max_uint256_succ_eq_modulus.symm

/-- MAX_UINT256 is strictly less than modulus (= 2^256). -/
theorem max_uint256_lt_modulus :
    Verity.Stdlib.Math.MAX_UINT256 < Verity.Core.Uint256.modulus := by
  rw [modulus_eq_max_uint256_succ]; exact Nat.lt_succ_of_le (Nat.le_refl _)

/-- Any value ≤ MAX_UINT256 is strictly less than modulus. -/
theorem lt_modulus_of_le_max_uint256 (n : Nat)
    (h : n ≤ Verity.Stdlib.Math.MAX_UINT256) :
    n < Verity.Core.Uint256.modulus :=
  Nat.lt_of_le_of_lt h max_uint256_lt_modulus

/-- Convert `a ≥ b` on Uint256 to `b.val ≤ a.val` on Nat.
    Eliminates the repeated 3-4 line pattern found in transfer proofs:
    `have h' : b.val ≤ a.val := by have h'' : b ≤ a := ...; simpa [Uint256.le_def] using h''` -/
theorem uint256_ge_val_le {a b : Verity.Core.Uint256} (h : a ≥ b) : b.val ≤ a.val := by
  simpa [Verity.Core.Uint256.le_def] using h

/-- `amount < modulus` when `bal.val ≥ amount` (amount fits in a Uint256 because balance does).
    Eliminates the repeated 3-line pattern:
    `have hlt := bal.isLt; exact Nat.lt_of_le_of_lt h hlt` -/
theorem amount_lt_modulus_of_val_ge (bal : Verity.Core.Uint256) (amount : Nat)
    (h : bal.val ≥ amount) : amount < Verity.Core.Uint256.modulus :=
  Nat.lt_of_le_of_lt h bal.isLt

/-- `bal ≥ ofNat amount` when `bal.val ≥ amount` (lift Nat comparison to Uint256).
    Eliminates the repeated 3-line `simp [le_def, val_ofNat, mod_eq_of_lt ...]` block. -/
theorem uint256_ofNat_le_of_val_ge (bal : Verity.Core.Uint256) (amount : Nat)
    (h : bal.val ≥ amount) : bal ≥ Verity.Core.Uint256.ofNat amount := by
  have h_lt := amount_lt_modulus_of_val_ge bal amount h
  simp [Verity.Core.Uint256.le_def, Verity.Core.Uint256.val_ofNat,
    Nat.mod_eq_of_lt h_lt, h]

/-- If `require (a == b) msg` succeeds, then `a = b`.
    Composes `require_success_implies_cond` with `address_beq_eq_true_iff_eq`. -/
theorem require_beq_success_implies_eq (a b : Address) (msg : String)
    (s : ContractState)
    (h : ((Verity.require (a == b) msg).run s).isSuccess = true) :
    a = b :=
  (address_beq_eq_true_iff_eq a b).1 (require_success_implies_cond (cond := a == b) (msg := msg) (state := s) h)

/-- `require (a == b) msg` succeeds exactly when `a = b`. -/
theorem require_beq_isSuccess_true_iff_eq (a b : Address) (msg : String) (s : ContractState) :
    ((Verity.require (a == b) msg).run s).isSuccess = true ↔ a = b := by
  constructor
  · intro h
    exact require_beq_success_implies_eq a b msg s h
  · intro h_eq
    subst h_eq
    simp [Verity.require]

/-- `require (a == b) msg` fails exactly when `a ≠ b`. -/
theorem require_beq_isSuccess_false_iff_ne (a b : Address) (msg : String) (s : ContractState) :
    ((Verity.require (a == b) msg).run s).isSuccess = false ↔ a ≠ b := by
  constructor
  · intro h_false h_eq
    subst h_eq
    simp [Verity.require] at h_false
  · intro h_ne
    have h_beq_false : (a == b) = false := address_beq_false_of_ne a b h_ne
    simp [Verity.require, h_beq_false]

/-- Common owner-check pattern:
    if `msgSender >>= getStorageAddr slot >>= require (sender == owner)` succeeds,
    then the storage owner at `slot` equals the caller (`state.sender`). -/
theorem owner_guard_success_implies_storageAddr_eq_sender
    (slot : StorageSlot Address) (msg : String) (state : ContractState)
    (h :
      ((Verity.bind msgSender (fun sender =>
          Verity.bind (getStorageAddr slot) (fun ownerAddr =>
            Verity.require (sender == ownerAddr) msg))).run state).isSuccess = true) :
    state.storageAddr slot.slot = state.sender := by
  have h_req :
      ((Verity.require (state.sender == state.storageAddr slot.slot) msg).run state).isSuccess = true := by
    simpa [msgSender, getStorageAddr, Verity.bind, Contract.run] using h
  exact (require_beq_isSuccess_true_iff_eq state.sender (state.storageAddr slot.slot) msg state).1 h_req |>.symm

-- All lemmas in this file are fully proven with zero sorry, zero axioms.

end Verity.Proofs.Stdlib.Automation
