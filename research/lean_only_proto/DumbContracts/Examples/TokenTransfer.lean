import DumbContracts.Examples.TokenBase
import DumbContracts.Lang
import DumbContracts.Semantics

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts

/-- Simple ERC20-style transfer. -/

def transferFun : Fun :=
  { name := "transfer"
    args := ["from", "to", "amount"]
    body := Stmt.if_
      (Expr.eq (Expr.var "to") (Expr.lit 0))
      Stmt.revert
      (Stmt.if_
        (Expr.lt (Expr.sload (Expr.add (Expr.lit 1000) (Expr.var "from"))) (Expr.var "amount"))
        Stmt.revert
        (Stmt.sstore
            (Expr.add (Expr.lit 1000) (Expr.var "from"))
            (Expr.sub
              (Expr.sload (Expr.add (Expr.lit 1000) (Expr.var "from")))
              (Expr.var "amount"))
          ;;
          Stmt.sstore
            (Expr.add (Expr.lit 1000) (Expr.var "to"))
            (Expr.add
              (Expr.sload (Expr.add (Expr.lit 1000) (Expr.var "to")))
              (Expr.var "amount"))))
    ret := none }

-- Token-style specs (Store-level).

def transferSpecR (from to amount : Nat) : SpecR Store :=
  { requires := fun s => to ≠ 0 ∧ s (balanceSlot from) >= amount
    ensures := fun s s' =>
      s' =
        setBalance
          (setBalance s from (s (balanceSlot from) - amount))
          to (s (balanceSlot to) + amount)
    reverts := fun s => to = 0 ∨ s (balanceSlot from) < amount }

def transferSpecRNoSelf (from to amount : Nat) : SpecR Store :=
  { requires := fun s => to ≠ 0 ∧ from ≠ to ∧ s (balanceSlot from) >= amount
    ensures := (transferSpecR from to amount).ensures
    reverts := fun s => to = 0 ∨ from = to ∨ s (balanceSlot from) < amount }

def transferStoreSeq (s : Store) (from to amount : Nat) : Store :=
  let s1 := setBalance s from (s (balanceSlot from) - amount)
  setBalance s1 to (s1 (balanceSlot to) + amount)

def transferSpecRSeq (from to amount : Nat) : SpecR Store :=
  { requires := fun s => to ≠ 0 ∧ s (balanceSlot from) >= amount
    ensures := fun s s' => s' = transferStoreSeq s from to amount
    reverts := fun s => to = 0 ∨ s (balanceSlot from) < amount }

-- Sequential read equivalence when from != to.

theorem transferStoreSeq_eq_transferSpecR_update (s : Store) (from to amount : Nat)
    (hneq : from ≠ to) :
    transferStoreSeq s from to amount =
      setBalance
        (setBalance s from (s (balanceSlot from) - amount))
        to (s (balanceSlot to) + amount) := by
  have hslot : balanceSlot from ≠ balanceSlot to := by
    exact balanceSlot_ne from to hneq
  have hs1 :
      (setBalance s from (s (balanceSlot from) - amount)) (balanceSlot to) =
        s (balanceSlot to) := by
    simp [setBalance, updateStore, updateNat, hslot]
  simp [transferStoreSeq, setBalance, updateStore, updateNat, hs1]

theorem transferSpecRSeq_ensures_eq_transferSpecR (s s' : Store) (from to amount : Nat)
    (hneq : from ≠ to) :
    (transferSpecRSeq from to amount).ensures s s' ↔
      (transferSpecR from to amount).ensures s s' := by
  constructor
  · intro hens
    have hs : s' = transferStoreSeq s from to amount := by
      simpa [transferSpecRSeq] using hens
    have hs' :
        s' =
          setBalance
            (setBalance s from (s (balanceSlot from) - amount))
            to (s (balanceSlot to) + amount) := by
      simpa [transferStoreSeq_eq_transferSpecR_update s from to amount hneq] using hs
    simpa [transferSpecR] using hs'
  · intro hens
    have hs :
        s' =
          setBalance
            (setBalance s from (s (balanceSlot from) - amount))
            to (s (balanceSlot to) + amount) := by
      simpa [transferSpecR] using hens
    have hs' : s' = transferStoreSeq s from to amount := by
      simpa [transferStoreSeq_eq_transferSpecR_update s from to amount hneq] using hs
    simpa [transferSpecRSeq] using hs'

-- Execution matches specs.

theorem transfer_meets_specR_ok (s : Store) (from to amount : Nat) :
    (transferSpecR from to amount).requires s ->
    (match execFun transferFun [from, to, amount] s [] with
      | ExecResult.ok _ s' => (transferSpecR from to amount).ensures s s'
      | _ => False) := by
  intro hreq
  have hto : to ≠ 0 := hreq.left
  have hbal : s (balanceSlot from) >= amount := hreq.right
  have hnotlt : ¬ s (balanceSlot from) < amount := by
    exact not_lt_of_ge hbal
  simp [transferSpecR, transferFun, execFun, execStmt, evalExpr, bindArgs, emptyEnv,
    updateEnv, updateStore, balanceSlot, setBalance, hto, hnotlt]

theorem transfer_meets_specRNoSelf_ok (s : Store) (from to amount : Nat) :
    (transferSpecRNoSelf from to amount).requires s ->
    (match execFun transferFun [from, to, amount] s [] with
      | ExecResult.ok _ s' => (transferSpecRNoSelf from to amount).ensures s s'
      | _ => False) := by
  intro hreq
  have hreq' : (transferSpecR from to amount).requires s := by
    exact And.intro hreq.left hreq.right.right
  simpa [transferSpecRNoSelf] using (transfer_meets_specR_ok s from to amount hreq')

theorem transfer_meets_specRSeq_ok (s : Store) (from to amount : Nat) :
    (transferSpecRSeq from to amount).requires s ->
    (match execFun transferFun [from, to, amount] s [] with
      | ExecResult.ok _ s' => (transferSpecRSeq from to amount).ensures s s'
      | _ => False) := by
  intro hreq
  have hto : to ≠ 0 := hreq.left
  have hbal : s (balanceSlot from) >= amount := hreq.right
  have hnotlt : ¬ s (balanceSlot from) < amount := by
    exact not_lt_of_ge hbal
  simp [transferSpecRSeq, transferStoreSeq, transferFun, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, balanceSlot, setBalance, hto, hnotlt]

theorem transfer_meets_specR_reverts (s : Store) (from to amount : Nat) :
    (transferSpecR from to amount).reverts s ->
    execFun transferFun [from, to, amount] s [] = ExecResult.reverted := by
  intro hrev
  cases hrev with
  | inl hto =>
      simp [transferFun, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv,
        updateStore, balanceSlot, setBalance, hto]
  | inr hlt =>
      by_cases hto : to = 0
      · simp [transferFun, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv,
          updateStore, balanceSlot, setBalance, hto]
      · simp [transferFun, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv,
          updateStore, balanceSlot, setBalance, hto, hlt]

-- Aliasing boundary facts.

theorem transfer_self_noop (s : Store) (from amount : Nat)
    (hto : from ≠ 0) (hbal : s (balanceSlot from) >= amount) :
    execFun transferFun [from, from, amount] s [] =
      ExecResult.ok (bindArgs emptyEnv ["from", "to", "amount"] [from, from, amount]) s := by
  have hnotlt : ¬ s (balanceSlot from) < amount := by
    exact not_lt_of_ge hbal
  have hs :
      execFun transferFun [from, from, amount] s [] =
        ExecResult.ok
          (bindArgs emptyEnv ["from", "to", "amount"] [from, from, amount])
          (updateStore
            (updateStore s (balanceSlot from) (s (balanceSlot from) - amount))
            (balanceSlot from)
            (s (balanceSlot from) - amount + amount)) := by
    simp [transferFun, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv,
      updateStore, balanceSlot, hto, hnotlt]
  have hshadow :
      updateStore
        (updateStore s (balanceSlot from) (s (balanceSlot from) - amount))
        (balanceSlot from)
        (s (balanceSlot from) - amount + amount)
        =
        updateStore s (balanceSlot from) (s (balanceSlot from) - amount + amount) := by
    exact updateStore_shadow s (balanceSlot from)
      (s (balanceSlot from) - amount) (s (balanceSlot from) - amount + amount)
  have hval : s (balanceSlot from) - amount + amount = s (balanceSlot from) := by
    exact Nat.sub_add_cancel hbal
  have hs' :
      updateStore
        (updateStore s (balanceSlot from) (s (balanceSlot from) - amount))
        (balanceSlot from)
        (s (balanceSlot from) - amount + amount)
        = s := by
    calc
      updateStore
          (updateStore s (balanceSlot from) (s (balanceSlot from) - amount))
          (balanceSlot from)
          (s (balanceSlot from) - amount + amount)
          =
          updateStore s (balanceSlot from) (s (balanceSlot from) - amount + amount) := by
            exact hshadow
      _ = updateStore s (balanceSlot from) (s (balanceSlot from)) := by
            simp [hval]
      _ = s := by
            exact updateStore_same s (balanceSlot from)
  simpa [hs'] using hs

theorem transferSpecRSeq_self_ensures_noop (s s' : Store) (from amount : Nat)
    (hbal : s (balanceSlot from) >= amount)
    (hens : (transferSpecRSeq from from amount).ensures s s') :
    s' = s := by
  have hval : s (balanceSlot from) - amount + amount = s (balanceSlot from) := by
    exact Nat.sub_add_cancel hbal
  have hs :
      s' =
        updateStore
          (updateStore s (balanceSlot from) (s (balanceSlot from) - amount))
          (balanceSlot from)
          (s (balanceSlot from) - amount + amount) := by
    simpa [transferSpecRSeq, transferStoreSeq, setBalance, updateStore, updateNat] using hens
  have hshadow :
      updateStore
        (updateStore s (balanceSlot from) (s (balanceSlot from) - amount))
        (balanceSlot from)
        (s (balanceSlot from) - amount + amount)
        =
        updateStore s (balanceSlot from) (s (balanceSlot from) - amount + amount) := by
    exact updateStore_shadow s (balanceSlot from)
      (s (balanceSlot from) - amount) (s (balanceSlot from) - amount + amount)
  have hs' :
      s' = updateStore s (balanceSlot from) (s (balanceSlot from) - amount + amount) := by
    calc
      s' =
          updateStore
            (updateStore s (balanceSlot from) (s (balanceSlot from) - amount))
            (balanceSlot from)
            (s (balanceSlot from) - amount + amount) := by
              exact hs
      _ = updateStore s (balanceSlot from) (s (balanceSlot from) - amount + amount) := by
              exact hshadow
  calc
    s' = updateStore s (balanceSlot from) (s (balanceSlot from)) := by
          simpa [hval] using hs'
    _ = s := by
          exact updateStore_same s (balanceSlot from)

theorem transferSpecR_self_balance_increases (s s' : Store) (from amount : Nat)
    (hens : (transferSpecR from from amount).ensures s s') :
    s' (balanceSlot from) = s (balanceSlot from) + amount := by
  have hs :
      s' =
        setBalance
          (setBalance s from (s (balanceSlot from) - amount))
          from (s (balanceSlot from) + amount) := by
    simpa [transferSpecR] using hens
  have hshadow :
      setBalance
          (setBalance s from (s (balanceSlot from) - amount))
          from (s (balanceSlot from) + amount)
        =
        setBalance s from (s (balanceSlot from) + amount) := by
    simp [setBalance, updateStore_shadow]
  calc
    s' (balanceSlot from)
        = (setBalance s from (s (balanceSlot from) + amount)) (balanceSlot from) := by
            simpa [hs, hshadow]
    _ = s (balanceSlot from) + amount := by
            simp [setBalance, updateStore, updateNat]

theorem transferSpecR_self_ensures_not_s (s : Store) (from amount : Nat)
    (hpos : amount > 0) :
    ¬ (transferSpecR from from amount).ensures s s := by
  intro hens
  have hbal :
      s (balanceSlot from) = s (balanceSlot from) + amount := by
    simpa using (transferSpecR_self_balance_increases s s from amount hens)
  have h' : s (balanceSlot from) + amount = s (balanceSlot from) + 0 := by
    simpa using hbal.symm
  have hzero : amount = 0 := by
    exact Nat.add_left_cancel h'
  exact (ne_of_gt hpos) hzero

-- Sum preservation properties.

theorem transfer_preserves_sum2 (s s' : Store) (from to amount : Nat)
    (hreq : (transferSpecR from to amount).requires s) (hneq : from ≠ to) :
    (transferSpecR from to amount).ensures s s' ->
    sum2 s from to = sum2 s' from to := by
  intro h
  have hbal : amount <= s (balanceSlot from) := by
    exact hreq.right
  have hslot : balanceSlot from ≠ balanceSlot to := by
    exact balanceSlot_ne from to hneq
  have hs :
      s' =
        setBalance
          (setBalance s from (s (balanceSlot from) - amount))
          to (s (balanceSlot to) + amount) := by
    simpa [transferSpecR] using h
  calc
    sum2 s from to
        = s (balanceSlot from) + s (balanceSlot to) := by
            simp [sum2]
    _ = (s (balanceSlot from) - amount + amount) + s (balanceSlot to) := by
            simp [Nat.sub_add_cancel hbal, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = (s (balanceSlot from) - amount) + (s (balanceSlot to) + amount) := by
            simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = sum2 s' from to := by
            simp [sum2, hs, setBalance, updateStore, updateNat, balanceSlot, hslot, Nat.add_assoc]

theorem transfer_preserves_other_balance (s s' : Store) (from to amount addr : Nat)
    (hfrom : addr ≠ from) (hto : addr ≠ to) :
    (transferSpecR from to amount).ensures s s' ->
    s' (balanceSlot addr) = s (balanceSlot addr) := by
  intro h
  have hs :
      s' =
        setBalance
          (setBalance s from (s (balanceSlot from) - amount))
          to (s (balanceSlot to) + amount) := by
    simpa [transferSpecR] using h
  have hslot_from : balanceSlot addr ≠ balanceSlot from := by
    exact balanceSlot_ne addr from hfrom
  have hslot_to : balanceSlot addr ≠ balanceSlot to := by
    exact balanceSlot_ne addr to hto
  simp [hs, setBalance, updateStore, updateNat, hslot_to, hslot_from]

theorem transfer_preserves_sum_list (s s' : Store) (from to amount : Nat) (addrs : List Nat)
    (hnotfrom : from ∉ addrs) (hnotto : to ∉ addrs)
    (hens : (transferSpecR from to amount).ensures s s') :
    sumBalances s addrs = sumBalances s' addrs := by
  induction addrs with
  | nil =>
      simp [sumBalances]
  | cons a rest ih =>
      have hnotfrom' : a ≠ from := by
        intro h
        apply hnotfrom
        simp [h]
      have hnotto' : a ≠ to := by
        intro h
        apply hnotto
        simp [h]
      have hnotfrom_tail : from ∉ rest := by
        intro hmem
        apply hnotfrom
        simp [hmem]
      have hnotto_tail : to ∉ rest := by
        intro hmem
        apply hnotto
        simp [hmem]
      have hbal :
          s' (balanceSlot a) = s (balanceSlot a) :=
        transfer_preserves_other_balance s s' from to amount hnotfrom' hnotto' hens
      have htail :
          sumBalances s rest = sumBalances s' rest :=
        ih hnotfrom_tail hnotto_tail hens
      simp [sumBalances, hbal, htail]

theorem transfer_preserves_sum_from_to_rest (s s' : Store) (from to amount : Nat) (rest : List Nat)
    (hreq : (transferSpecR from to amount).requires s) (hneq : from ≠ to)
    (hnotfrom : from ∉ rest) (hnotto : to ∉ rest)
    (hens : (transferSpecR from to amount).ensures s s') :
    sumBalances s (from :: to :: rest) = sumBalances s' (from :: to :: rest) := by
  have hsum2 : sum2 s from to = sum2 s' from to :=
    transfer_preserves_sum2 s s' from to amount hreq hneq hens
  have hrest : sumBalances s rest = sumBalances s' rest :=
    transfer_preserves_sum_list s s' from to amount rest hnotfrom hnotto hens
  calc
    sumBalances s (from :: to :: rest)
        = (s (balanceSlot from) + s (balanceSlot to)) + sumBalances s rest := by
            simp [sumBalances, Nat.add_assoc]
    _ = (s' (balanceSlot from) + s' (balanceSlot to)) + sumBalances s rest := by
            simpa [sum2] using hsum2
    _ = (s' (balanceSlot from) + s' (balanceSlot to)) + sumBalances s' rest := by
            simp [hrest]
    _ = sumBalances s' (from :: to :: rest) := by
            simp [sumBalances, Nat.add_assoc]

theorem transfer_preserves_totalSupply (s s' : Store) (from to amount : Nat)
    (hens : (transferSpecR from to amount).ensures s s') :
    totalSupply s' = totalSupply s := by
  have hs :
      s' =
        setBalance
          (setBalance s from (s (balanceSlot from) - amount))
          to (s (balanceSlot to) + amount) := by
    simpa [transferSpecR] using hens
  have hslot_from : balanceSlot from ≠ totalSupplySlot := by
    exact balanceSlot_ne_total from
  have hslot_to : balanceSlot to ≠ totalSupplySlot := by
    exact balanceSlot_ne_total to
  simp [totalSupply, hs, setBalance, updateStore, updateNat, hslot_to, hslot_from, totalSupplySlot]

theorem transfer_preserves_supply_list (s s' : Store) (from to amount : Nat) (rest : List Nat)
    (hreq : (transferSpecR from to amount).requires s) (hneq : from ≠ to)
    (hnotfrom : from ∉ rest) (hnotto : to ∉ rest)
    (hsupply : sumBalances s (from :: to :: rest) = totalSupply s)
    (hens : (transferSpecR from to amount).ensures s s') :
    sumBalances s' (from :: to :: rest) = totalSupply s' := by
  have hsum :
      sumBalances s (from :: to :: rest) = sumBalances s' (from :: to :: rest) :=
    transfer_preserves_sum_from_to_rest s s' from to amount rest hreq hneq hnotfrom hnotto hens
  have htot : totalSupply s' = totalSupply s :=
    transfer_preserves_totalSupply s s' from to amount hens
  calc
    sumBalances s' (from :: to :: rest)
        = sumBalances s (from :: to :: rest) := by
            symm
            exact hsum
    _ = totalSupply s := by
            exact hsupply
    _ = totalSupply s' := by
            symm
            exact htot

end DumbContracts.Examples
