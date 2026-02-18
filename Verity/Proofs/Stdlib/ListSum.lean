/-
  Shared list-sum lemmas for balance conservation proofs.

  Provides countOcc/countOccU occurrence counting and generic theorems
  about how mapping sums change under point updates, point decreases,
  and two-point transfers. Used by Ledger/Conservation and
  SimpleToken/Supply proofs.
-/

import Verity.Core

namespace Verity.Proofs.Stdlib.ListSum

open Verity

/-! ## Occurrence Counting -/

/-- Count occurrences of an element in a list. -/
def countOcc (target : Address) : List Address → Nat
  | [] => 0
  | a :: rest => (if a = target then 1 else 0) + countOcc target rest

/-- Uint256 version of countOcc for arithmetic in sum equations. -/
def countOccU (target : Address) (addrs : List Address) : Uint256 :=
  Core.Uint256.ofNat (countOcc target addrs)

theorem countOcc_cons_eq (target : Address) (rest : List Address) :
  countOcc target (target :: rest) = 1 + countOcc target rest := by
  simp [countOcc]

theorem countOcc_cons_ne (a target : Address) (rest : List Address) (h : a ≠ target) :
  countOcc target (a :: rest) = countOcc target rest := by
  simp [countOcc, h]

theorem countOccU_cons_eq (target : Address) (rest : List Address) :
  countOccU target (target :: rest) = (1 : Uint256) + countOccU target rest := by
  simp [countOccU, countOcc, Verity.Core.Uint256.ofNat_add]

theorem countOccU_cons_ne (a target : Address) (rest : List Address) (h : a ≠ target) :
  countOccU target (a :: rest) = countOccU target rest := by
  simp [countOccU, countOcc, h]

/-! ## Generic List Sum Lemma: Point Update -/

/-- When f' agrees with f except at target where f'(target) = f(target) + delta,
    then for any list: sum(map f') = sum(map f) + countOcc(target, list) * delta. -/
theorem map_sum_point_update
  (f f' : Address → Uint256) (target : Address) (delta : Uint256)
  (h_target : f' target = f target + delta)
  (h_other : ∀ addr, addr ≠ target → f' addr = f addr) :
  ∀ addrs : List Address,
    (addrs.map f').sum = (addrs.map f).sum + countOccU target addrs * delta := by
  intro addrs
  induction addrs with
  | nil => simp [countOcc, countOccU]
  | cons a rest ih =>
    simp only [List.map, List.sum_cons]
    rw [ih]
    by_cases h : a = target
    · simp [h, h_target, countOccU_cons_eq]
      have h_mul : delta * (1 + countOccU target rest) = delta + delta * countOccU target rest := by
        calc
          delta * (1 + countOccU target rest)
              = (1 + countOccU target rest) * delta := by
                  simp [Verity.Core.Uint256.mul_comm]
          _ = delta + countOccU target rest * delta := by
                  have h_add_mul := Verity.Core.Uint256.add_mul
                    (1 : Uint256) (countOccU target rest) delta
                  calc
                    (1 + countOccU target rest) * delta
                        = 1 * delta + countOccU target rest * delta := h_add_mul
                    _ = delta + countOccU target rest * delta := by
                        simp [Verity.Core.Uint256.one_mul]
          _ = delta + delta * countOccU target rest := by
                  simp [Verity.Core.Uint256.mul_comm]
      rw [h_mul]
      rw [← Verity.Core.Uint256.add_assoc delta (f target) _]
      rw [Verity.Core.Uint256.add_comm delta (f target)]
      rw [Verity.Core.Uint256.add_assoc (f target) delta _]
      rw [← Verity.Core.Uint256.add_assoc delta (List.map f rest).sum _]
      rw [Verity.Core.Uint256.add_comm delta (List.map f rest).sum]
      rw [Verity.Core.Uint256.add_assoc (List.map f rest).sum delta _]
    · simp [h, h_other a h, countOccU_cons_ne a target rest h]

/-! ## Generic List Sum Lemma: Point Decrease -/

/-- When f' agrees with f except at target where f'(target) = f(target) - delta,
    then: sum(map f') + countOcc(target, list) * delta = sum(map f). -/
theorem map_sum_point_decrease
  (f f' : Address → Uint256) (target : Address) (delta : Uint256)
  (h_target : f' target = f target - delta)
  (h_other : ∀ addr, addr ≠ target → f' addr = f addr) :
  ∀ addrs : List Address,
    (addrs.map f').sum + countOccU target addrs * delta = (addrs.map f).sum := by
  intro addrs
  induction addrs with
  | nil => simp [countOcc, countOccU]
  | cons a rest ih =>
    simp only [List.map, List.sum_cons]
    by_cases h : a = target
    · simp [h, h_target, countOccU_cons_eq]
      have h_mul : delta * (1 + countOccU target rest) = delta + delta * countOccU target rest := by
        calc
          delta * (1 + countOccU target rest)
              = (1 + countOccU target rest) * delta := by
                  simp [Verity.Core.Uint256.mul_comm]
          _ = delta + countOccU target rest * delta := by
                  have h_add_mul := Verity.Core.Uint256.add_mul
                    (1 : Uint256) (countOccU target rest) delta
                  calc
                    (1 + countOccU target rest) * delta
                        = 1 * delta + countOccU target rest * delta := h_add_mul
                    _ = delta + countOccU target rest * delta := by
                        simp [Verity.Core.Uint256.one_mul]
          _ = delta + delta * countOccU target rest := by
                  simp [Verity.Core.Uint256.mul_comm]
      rw [h_mul]
      have h_cancel : f target - delta + delta = f target := Verity.Core.Uint256.sub_add_cancel_left (f target) delta
      rw [← Verity.Core.Uint256.add_assoc (List.map f' rest).sum delta _]
      rw [Verity.Core.Uint256.add_left_comm (List.map f' rest).sum delta _]
      rw [Verity.Core.Uint256.add_assoc delta (List.map f' rest).sum _]
      rw [← Verity.Core.Uint256.add_assoc (f target - delta) delta _]
      rw [h_cancel]
      have h_congr := congrArg (fun x => f target + x) ih
      have h_congr' := h_congr
      simp [Verity.Core.Uint256.mul_comm,
        Verity.Core.Uint256.add_assoc] at h_congr'
      exact h_congr'
    · simp [h, h_other a h, countOccU_cons_ne a target rest h]
      have h_congr := congrArg (fun x => f a + x) ih
      have h_congr' := h_congr
      simp [Verity.Core.Uint256.mul_comm,
        Verity.Core.Uint256.add_assoc,
        Verity.Core.Uint256.add_left_comm,
        Verity.Core.Uint256.add_comm] at h_congr'
      exact h_congr'

/-! ## Generic List Sum Lemma: Transfer (Two-Point Update) -/

/-- When f' has f'(src) = f(src) - d and f'(dst) = f(dst) + d and agrees elsewhere,
    then sum(map f') + countOcc(src) * d = sum(map f) + countOcc(dst) * d. -/
theorem map_sum_transfer_eq
  (f f' : Address → Uint256) (src dst : Address) (d : Uint256)
  (h_ne : src ≠ dst)
  (h_src : f' src = f src - d)
  (h_dst : f' dst = f dst + d)
  (h_other : ∀ addr, addr ≠ src → addr ≠ dst → f' addr = f addr) :
  ∀ addrs : List Address,
    (addrs.map f').sum + countOccU src addrs * d
    = (addrs.map f).sum + countOccU dst addrs * d := by
  intro addrs
  induction addrs with
  | nil => simp [countOcc, countOccU]
  | cons a rest ih =>
    simp only [List.map, List.sum_cons]
    by_cases ha_s : a = src
    · simp [ha_s, h_src, countOccU_cons_eq, countOccU_cons_ne src dst rest h_ne]
      have h_mul : d * (1 + countOccU src rest) = d + d * countOccU src rest := by
        calc
          d * (1 + countOccU src rest)
              = (1 + countOccU src rest) * d := by
                  simp [Verity.Core.Uint256.mul_comm]
          _ = d + countOccU src rest * d := by
                  have h_add_mul := Verity.Core.Uint256.add_mul
                    (1 : Uint256) (countOccU src rest) d
                  calc
                    (1 + countOccU src rest) * d
                        = 1 * d + countOccU src rest * d := h_add_mul
                    _ = d + countOccU src rest * d := by
                        simp [Verity.Core.Uint256.one_mul]
          _ = d + d * countOccU src rest := by
                  simp [Verity.Core.Uint256.mul_comm]
      rw [h_mul]
      have h_cancel : f src - d + d = f src := Verity.Core.Uint256.sub_add_cancel_left (f src) d
      rw [← Verity.Core.Uint256.add_assoc (List.map f' rest).sum d _]
      rw [Verity.Core.Uint256.add_left_comm (List.map f' rest).sum d _]
      rw [Verity.Core.Uint256.add_assoc d (List.map f' rest).sum _]
      rw [← Verity.Core.Uint256.add_assoc (f src - d) d _]
      rw [h_cancel]
      have h_congr := congrArg (fun x => f src + x) ih
      have h_congr' := h_congr
      simp [Verity.Core.Uint256.mul_comm,
        Verity.Core.Uint256.add_assoc] at h_congr'
      exact h_congr'
    · by_cases ha_d : a = dst
      · simp [ha_d, h_dst]
        have h_ne_sym : dst ≠ src := Ne.symm h_ne
        simp [countOccU_cons_ne dst src rest h_ne_sym, countOccU_cons_eq]
        have h_mul : d * (1 + countOccU dst rest) = d + d * countOccU dst rest := by
          calc
            d * (1 + countOccU dst rest)
                = (1 + countOccU dst rest) * d := by
                    simp [Verity.Core.Uint256.mul_comm]
            _ = d + countOccU dst rest * d := by
                    have h_add_mul := Verity.Core.Uint256.add_mul
                      (1 : Uint256) (countOccU dst rest) d
                    calc
                      (1 + countOccU dst rest) * d
                          = 1 * d + countOccU dst rest * d := h_add_mul
                      _ = d + countOccU dst rest * d := by
                          simp [Verity.Core.Uint256.one_mul]
            _ = d + d * countOccU dst rest := by
                    simp [Verity.Core.Uint256.mul_comm]
        rw [h_mul]
        rw [← Verity.Core.Uint256.add_assoc d (f dst) _]
        rw [Verity.Core.Uint256.add_comm d (f dst)]
        rw [Verity.Core.Uint256.add_assoc (f dst) d _]
        have h_congr := congrArg (fun x => f dst + (d + x)) ih
        calc
          f dst + (d + ((List.map f' rest).sum + d * countOccU src rest))
              = f dst + (d + ((List.map f rest).sum + d * countOccU dst rest)) := by
                  have h_congr' := h_congr
                  simp [Verity.Core.Uint256.mul_comm] at h_congr'
                  exact h_congr'
          _ = f dst + ((List.map f rest).sum + (d + d * countOccU dst rest)) := by
                  rw [← Verity.Core.Uint256.add_assoc d (List.map f rest).sum _]
                  rw [Verity.Core.Uint256.add_comm d (List.map f rest).sum]
                  rw [← Verity.Core.Uint256.add_assoc (List.map f rest).sum d _]
      · simp [h_other a ha_s ha_d, countOccU_cons_ne a src rest ha_s, countOccU_cons_ne a dst rest ha_d]
        have h_congr := congrArg (fun x => f a + x) ih
        have h_congr' := h_congr
        simp [Verity.Core.Uint256.add_assoc] at h_congr'
        exact h_congr'

end Verity.Proofs.Stdlib.ListSum
