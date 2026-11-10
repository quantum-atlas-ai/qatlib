/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Aux
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false


open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix
set_option warningAsError false

variable {N : Type} [Fintype N] [DecidableEq N]

omit [Fintype N] in

theorem taylorStepMatrixV2_above (m k p : ℕ) (M : Matrix N N ℂ)
    (r c : Fin (m * (k + 1) + p + 1) × N) (h : r.1 < c.1) :
    taylorStepMatrixV2 m k p M r c = 0 := by
  have hne : r ≠ c := by intro he; subst c; exact lt_irrefl _ h
  have hprev : ¬ c.1.val + 1 = r.1.val := by omega
  have hclt : ¬ c.1.val < r.1.val := by omega
  simp [taylorStepMatrixV2, hne, hprev, hclt]

omit [Fintype N] in

theorem taylorStepMatrixV2_same_label (m k p : ℕ) (M : Matrix N N ℂ)
    (r c : Fin (m * (k + 1) + p + 1) × N) (h : r.1 = c.1) :
    taylorStepMatrixV2 m k p M r c = if r.2 = c.2 then 1 else 0 := by
  simp [taylorStepMatrixV2, Prod.ext_iff, h]

theorem taylorStepMatrixV2_det (m k p : ℕ) (M : Matrix N N ℂ) :
    (taylorStepMatrixV2 m k p M).det = 1 := by
  let b : (Fin (m * (k + 1) + p + 1) × N) → OrderDual (Fin (m * (k + 1) + p + 1)) :=
    fun r => OrderDual.toDual r.1
  have htri : (taylorStepMatrixV2 m k p M).BlockTriangular b := by
    intro r c hrc
    exact taylorStepMatrixV2_above m k p M r c hrc
  have hblock (l : OrderDual (Fin (m * (k + 1) + p + 1))) :
      (taylorStepMatrixV2 m k p M).toSquareBlock b l = 1 := by
    ext r c
    have hlabel : r.val.1 = c.val.1 := r.property.trans c.property.symm
    have heq : r.val.2 = c.val.2 ↔ r = c := by
      constructor
      · intro hdata
        apply Subtype.ext
        exact Prod.ext hlabel hdata
      · intro he
        rw [he]
    change taylorStepMatrixV2 m k p M r.val c.val = if r = c then 1 else 0
    rw [taylorStepMatrixV2_same_label m k p M r.val c.val hlabel]
    simp only [heq]
  rw [htri.det_fintype]
  apply Finset.prod_eq_one
  intro l _hl
  rw [hblock, Matrix.det_one]

theorem taylorStepMatrixV2_inverse (m k p : ℕ) (M : Matrix N N ℂ) :
    taylorStepMatrixV2 m k p M * (taylorStepMatrixV2 m k p M)⁻¹ = 1 ∧
      (taylorStepMatrixV2 m k p M)⁻¹ * taylorStepMatrixV2 m k p M = 1 := by
  have hdet : IsUnit (taylorStepMatrixV2 m k p M).det := by
    rw [taylorStepMatrixV2_det]
    exact isUnit_one
  exact ⟨Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet⟩

omit [Fintype N] [DecidableEq N] in

theorem label_mod_self (a j k : ℕ) : (a * (k + 1) + j) % (k + 1) = j % (k + 1) := by
  have h0 : a * (k + 1) % (k + 1) = 0 := Nat.mul_mod_left a (k + 1)
  rw [Nat.add_comm, Nat.add_mod, h0, add_zero, Nat.mod_mod]

omit [Fintype N] [DecidableEq N] in

theorem label_mod_of_le (a j k : ℕ) (hj : j ≤ k) : (a * (k + 1) + j) % (k + 1) = j := by
  rw [label_mod_self, Nat.mod_eq_of_lt (by omega)]

omit [Fintype N] [DecidableEq N] in

theorem step_label_lt (a m k p j : ℕ) (ha : a < m) (hj : j ≤ k) :
    a * (k + 1) + j < m * (k + 1) + p + 1 := by
  have h1 : (a + 1) * (k + 1) = a * (k + 1) + (k + 1) := Nat.succ_mul a (k + 1)
  have h2 : (a + 1) * (k + 1) ≤ m * (k + 1) := by gcongr; omega
  omega

omit [Fintype N] [DecidableEq N] in

theorem jump_label_lt (a m k p : ℕ) (ha : a ≤ m) :
    a * (k + 1) < m * (k + 1) + p + 1 := by
  have h : a * (k + 1) ≤ m * (k + 1) := by gcongr
  omega

omit [Fintype N] [DecidableEq N] in

theorem pad_label_lt (m k p j : ℕ) (hj : j ≤ p) :
    m * (k + 1) + j < m * (k + 1) + p + 1 := by omega

omit [Fintype N] [DecidableEq N] in

theorem pred_label_lt (a m k p j : ℕ) (ha : a < m) (hj : j ≤ k) (hj1 : 1 ≤ j) :
    a * (k + 1) + j - 1 < m * (k + 1) + p + 1 := by
  have h1 : (a + 1) * (k + 1) = a * (k + 1) + (k + 1) := Nat.succ_mul a (k + 1)
  have h2 : (a + 1) * (k + 1) ≤ m * (k + 1) := by gcongr; omega
  have h3 : a * (k + 1) + j - 1 ≤ a * (k + 1) + k := by omega
  omega

omit [DecidableEq N] in

theorem sum_label_single {P : ℕ} (w : Fin P) (F : Fin P × N → ℂ) :
    ∑ c : Fin P × N, (if c.1 = w then F c else 0) = ∑ n' : N, F (w, n') := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single_of_mem w (Finset.mem_univ w)]
  · simp
  · intro c1 _ hc1
    simp [hc1]

section RHS

omit [Fintype N] [DecidableEq N] in

theorem taylorRHS_at_zero (m k p : ℕ) (h : ℝ) (x_in b : QState N) (n : N) :
    taylorRHS m k p h x_in b (taylorTimeLabel m k p 0 (Nat.zero_le m), n) = x_in n := by
  simp [taylorRHS, taylorTimeLabel]

omit [Fintype N] [DecidableEq N] in

theorem taylorRHS_at_step (m k p : ℕ) (h : ℝ) (x_in b : QState N) (a j : ℕ)
    (ha : a < m) (hj1 : 1 ≤ j) (hjk : j ≤ k) (n : N) :
    taylorRHS m k p h x_in b (⟨a * (k + 1) + j, step_label_lt a m k p j ha hjk⟩, n) =
      (if j = 1 then h * b n else 0) := by
  have hle : a * (k + 1) + j ≤ m * (k + 1) := by
    have h1 : (a + 1) * (k + 1) = a * (k + 1) + (k + 1) := Nat.succ_mul a (k + 1)
    have h2 : (a + 1) * (k + 1) ≤ m * (k + 1) := by gcongr; omega
    omega
  have hne : ¬ (a * (k + 1) + j = 0) := by omega
  by_cases hj : j = 1
  · subst hj
    have hmod : (a * (k + 1) + 1) % (k + 1) = 1 := label_mod_of_le a 1 k (by omega)
    simp [taylorRHS, hle, hmod]
  · have hmod' : (a * (k + 1) + j) % (k + 1) ≠ 1 := by
      rw [label_mod_of_le a j k hjk]; omega
    have hj0 : (a * (k + 1) + j) % (k + 1) = j % (k + 1) := label_mod_self a j k
    have hjne : ¬ (j % (k + 1) = 1) := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp [taylorRHS, hjne, show ¬ (j = 0) by omega]
    exact fun hje => absurd hje hj

omit [Fintype N] [DecidableEq N] in

theorem taylorRHS_at_jump (m k p : ℕ) (h : ℝ) (x_in b : QState N) (a : ℕ)
    (ha1 : 1 ≤ a) (ham : a ≤ m) (n : N) :
    taylorRHS m k p h x_in b (⟨a * (k + 1), jump_label_lt a m k p ham⟩, n) = 0 := by
  simp [taylorRHS, show ¬ (a = 0) by omega]

omit [Fintype N] [DecidableEq N] in

theorem taylorRHS_at_pad (m k p : ℕ) (h : ℝ) (x_in b : QState N) (j : ℕ)
    (hj1 : 1 ≤ j) (hjp : j ≤ p) (n : N) :
    taylorRHS m k p h x_in b (⟨m * (k + 1) + j, pad_label_lt m k p j hjp⟩, n) = 0 := by
  have hgt : ¬ (m * (k + 1) + j ≤ m * (k + 1)) := by omega
  simp [taylorRHS, hgt, show ¬ (j = 0) by omega]

omit [Fintype N] [DecidableEq N] in

theorem taylorRHS_val_of_gt (m k p : ℕ) (h : ℝ) (x_in b : QState N)
    (r : Fin (m * (k + 1) + p + 1)) (hrg : m * (k + 1) < r.val) (n : N) :
    taylorRHS m k p h x_in b (r, n) = 0 := by
  have hgt : ¬ (r.val ≤ m * (k + 1)) := by omega
  have hne : ¬ (r.val = 0) := by omega
  simp [taylorRHS, hgt, hne]

end RHS

section Rows

variable (m k p : ℕ) (M : Matrix N N ℂ) (x : QState (Fin (m * (k + 1) + p + 1) × N))

theorem taylorV2_row_zero (n : N) :
    (taylorStepMatrixV2 m k p M *ᵥ x) (taylorTimeLabel m k p 0 (Nat.zero_le m), n) =
      x (taylorTimeLabel m k p 0 (Nat.zero_le m), n) := by
  have hv : (taylorTimeLabel m k p 0 (Nat.zero_le m) : Fin (m * (k + 1) + p + 1)).val = 0 := by
    simp [taylorTimeLabel]
  have hrow : ∀ c : Fin (m * (k + 1) + p + 1) × N,
      taylorStepMatrixV2 m k p M (taylorTimeLabel m k p 0 (Nat.zero_le m), n) c =
        (if (taylorTimeLabel m k p 0 (Nat.zero_le m), n) = c then (1 : ℂ) else 0) := by
    intro c
    by_cases hc : c.1.val = 0
    · have hlabel : (taylorTimeLabel m k p 0 (Nat.zero_le m) : Fin _) = c.1 :=
        Fin.ext (by rw [hv]; omega)
      rw [taylorStepMatrixV2_same_label m k p M _ c hlabel]
      by_cases hnn : n = c.2
      · simp [hlabel, hnn]
      · simp [hlabel, hnn, Prod.ext_iff]
    · rw [taylorStepMatrixV2_above m k p M _ c (by
        show (taylorTimeLabel m k p 0 (Nat.zero_le m) : Fin _).val < c.1.val
        rw [hv]; omega)]
      have hne : ¬ ((taylorTimeLabel m k p 0 (Nat.zero_le m), n) = c) := by
        intro he
        have h1 : (taylorTimeLabel m k p 0 (Nat.zero_le m) : Fin _) = c.1 :=
          congrArg Prod.fst he
        have h2 := congrArg Fin.val h1
        rw [hv] at h2
        omega
      simp [hne]
  show ∑ c : Fin (m * (k + 1) + p + 1) × N,
      taylorStepMatrixV2 m k p M (taylorTimeLabel m k p 0 (Nat.zero_le m), n) c * x c =
    x (taylorTimeLabel m k p 0 (Nat.zero_le m), n)
  simp only [hrow]
  simp

theorem taylorV2_row_step (r : Fin (m * (k + 1) + p + 1)) (hrj : 1 ≤ r.val % (k + 1))
    (hrm : r.val < m * (k + 1)) (n : N) :
    (taylorStepMatrixV2 m k p M *ᵥ x) (r, n) =
      x (r, n) -
        (((r.val % (k + 1) : ℕ) : ℂ)⁻¹ *
          (M *ᵥ taylorBlock x ⟨r.val - 1, by omega⟩) n) := by
  have hrow : ∀ c : Fin (m * (k + 1) + p + 1) × N,
      taylorStepMatrixV2 m k p M (r, n) c =
        (if (r, n) = c then (1 : ℂ) else 0) -
          (if c.1.val = r.val - 1 then ((r.val % (k + 1) : ℕ) : ℂ)⁻¹ * M n c.2 else 0) := by
    intro c
    have hjc : ¬ ((r.val ≤ m * (k + 1) ∧ 0 < r.val ∧ (k + 1 : ℕ) ∣ r.val ∧
        r.val - (k + 1) ≤ c.1.val ∧ c.1.val < r.val)) := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    have hpad : ¬ (m * (k + 1) < r.val ∧ c.1.val + 1 = r.val) := by omega
    have entry :
        taylorStepMatrixV2 m k p M (r, n) c =
          (if (r, n) = c then (1 : ℂ) else 0)
            - (if r.val < m * (k + 1) ∧ 1 ≤ r.val % (k + 1) ∧ c.1.val + 1 = r.val then
                M n c.2 / ((r.val % (k + 1) : ℕ) : ℂ) else 0)
            - (if r.val ≤ m * (k + 1) ∧ 0 < r.val ∧ (k + 1 : ℕ) ∣ r.val ∧
                r.val - (k + 1) ≤ c.1.val ∧ c.1.val < r.val then
                (if n = c.2 then (1 : ℂ) else 0) else 0)
            - (if m * (k + 1) < r.val ∧ c.1.val + 1 = r.val then
                (if n = c.2 then (1 : ℂ) else 0) else 0) := rfl
    rw [entry]
    by_cases hcc : c.1.val = r.val - 1
    · have hstep : r.val < m * (k + 1) ∧ 1 ≤ r.val % (k + 1) ∧ c.1.val + 1 = r.val := by
        refine ⟨hrm, hrj, ?_⟩
        have := Nat.mod_le r.val (k + 1)
        omega
      rw [if_pos hstep, if_neg hjc, if_neg hpad]
      have hne : ¬ ((r, n) = c) := by
        intro he
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Fin.val h1
        simp only [Fin.val_eq_val] at h2
        omega
      rw [if_neg hne, if_pos hcc]
      rw [div_eq_inv_mul]
      ring
    · have hstep : ¬ (r.val < m * (k + 1) ∧ 1 ≤ r.val % (k + 1) ∧ c.1.val + 1 = r.val) := by
        omega
      rw [if_neg hstep, if_neg hjc, if_neg hpad, if_neg hcc]
      by_cases hdiag : (r, n) = c
      · rw [if_pos hdiag]
        ring
      · rw [if_neg hdiag]
        ring
  have hS2 : ∑ c : Fin (m * (k + 1) + p + 1) × N,
      (if c.1.val = r.val - 1 then ((r.val % (k + 1) : ℕ) : ℂ)⁻¹ * M n c.2 else 0) * x c =
      ((r.val % (k + 1) : ℕ) : ℂ)⁻¹ *
        ∑ n' : N, M n n' * taylorBlock x ⟨r.val - 1, by omega⟩ n' := by
    have hrew : ∀ c : Fin (m * (k + 1) + p + 1) × N,
        (if c.1.val = r.val - 1 then ((r.val % (k + 1) : ℕ) : ℂ)⁻¹ * M n c.2 else 0) * x c =
        (if c.1 = (⟨r.val - 1, by omega⟩ : Fin (m * (k + 1) + p + 1)) then
          ((r.val % (k + 1) : ℕ) : ℂ)⁻¹ * M n c.2 * x c else 0) := by
      intro c
      by_cases hc : c.1.val = r.val - 1
      · have hfin : c.1 = ⟨r.val - 1, by omega⟩ := Fin.ext hc
        simp [hfin]
      · have hfin : ¬ (c.1 = ⟨r.val - 1, by omega⟩) := by
          intro he
          have hv2 : c.1.val = r.val - 1 := by rw [he]
          omega
        simp [hfin, hc]
    simp only [hrew, sum_label_single, taylorBlock]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [Matrix.mulVec, dotProduct]
  simp only [hrow]
  simp only [sub_mul, Finset.sum_sub_distrib]
  have hS1 : ∑ c : Fin (m * (k + 1) + p + 1) × N,
      (if (r, n) = c then (1 : ℂ) else 0) * x c = x (r, n) := by
    simp only [ite_mul, one_mul, zero_mul]
    simp
  rw [hS1, hS2]

theorem taylorV2_row_jump (r : Fin (m * (k + 1) + p + 1)) (hr0 : 0 < r.val)
    (hrd : (k + 1 : ℕ) ∣ r.val) (hrm : r.val ≤ m * (k + 1)) (n : N) :
    (taylorStepMatrixV2 m k p M *ᵥ x) (r, n) =
      x (r, n) -
        ∑ c1 : Fin (m * (k + 1) + p + 1),
          (if r.val - (k + 1) ≤ c1.val ∧ c1.val < r.val then x (c1, n) else 0) := by
  have hmod : r.val % (k + 1) = 0 := Nat.mod_eq_zero_of_dvd hrd
  have hrow : ∀ c : Fin (m * (k + 1) + p + 1) × N,
      taylorStepMatrixV2 m k p M (r, n) c =
        (if (r, n) = c then (1 : ℂ) else 0) -
          (if r.val - (k + 1) ≤ c.1.val ∧ c.1.val < r.val then
            (if n = c.2 then (1 : ℂ) else 0) else 0) := by
    intro c
    have hstep : ¬ (r.val < m * (k + 1) ∧ 1 ≤ r.val % (k + 1) ∧ c.1.val + 1 = r.val) := by
      intro hc
      have := hc.2.1
      omega
    have hjc : (r.val ≤ m * (k + 1) ∧ 0 < r.val ∧ (k + 1 : ℕ) ∣ r.val ∧
        r.val - (k + 1) ≤ c.1.val ∧ c.1.val < r.val) ↔
        (r.val - (k + 1) ≤ c.1.val ∧ c.1.val < r.val) := by
      simp [hrm, hr0, hrd]
    have hpad : ¬ (m * (k + 1) < r.val ∧ c.1.val + 1 = r.val) := by omega
    have entry :
        taylorStepMatrixV2 m k p M (r, n) c =
          (if (r, n) = c then (1 : ℂ) else 0)
            - (if r.val < m * (k + 1) ∧ 1 ≤ r.val % (k + 1) ∧ c.1.val + 1 = r.val then
                M n c.2 / ((r.val % (k + 1) : ℕ) : ℂ) else 0)
            - (if r.val ≤ m * (k + 1) ∧ 0 < r.val ∧ (k + 1 : ℕ) ∣ r.val ∧
                r.val - (k + 1) ≤ c.1.val ∧ c.1.val < r.val then
                (if n = c.2 then (1 : ℂ) else 0) else 0)
            - (if m * (k + 1) < r.val ∧ c.1.val + 1 = r.val then
                (if n = c.2 then (1 : ℂ) else 0) else 0) := rfl
    rw [entry, if_neg hstep, if_neg hpad]
    simp only [hjc]
    ring
  simp only [Matrix.mulVec, dotProduct]
  simp only [hrow]
  simp only [sub_mul, Finset.sum_sub_distrib]
  have hS1 : ∑ c : Fin (m * (k + 1) + p + 1) × N,
      (if (r, n) = c then (1 : ℂ) else 0) * x c = x (r, n) := by
    simp only [ite_mul, one_mul, zero_mul]
    simp
  have hS2 : ∑ c : Fin (m * (k + 1) + p + 1) × N,
      (if r.val - (k + 1) ≤ c.1.val ∧ c.1.val < r.val then
        (if n = c.2 then (1 : ℂ) else 0) else 0) * x c =
      ∑ c1 : Fin (m * (k + 1) + p + 1),
        (if r.val - (k + 1) ≤ c1.val ∧ c1.val < r.val then x (c1, n) else 0) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro c1 _
    by_cases hwin : r.val - (k + 1) ≤ c1.val ∧ c1.val < r.val
    · rw [if_pos hwin]
      simp only [ite_mul, one_mul, zero_mul, hwin, and_self, if_true]
      simp
    · simp only [hwin, if_false, zero_mul, Finset.sum_const_zero]
  rw [hS1, hS2]

theorem taylorV2_row_pad (r : Fin (m * (k + 1) + p + 1)) (hrg : m * (k + 1) < r.val)
    (n : N) :
    (taylorStepMatrixV2 m k p M *ᵥ x) (r, n) =
      x (r, n) - x (⟨r.val - 1, by omega⟩, n) := by
  have hrow : ∀ c : Fin (m * (k + 1) + p + 1) × N,
      taylorStepMatrixV2 m k p M (r, n) c =
        (if (r, n) = c then (1 : ℂ) else 0) -
          (if c.1.val = r.val - 1 then (if n = c.2 then (1 : ℂ) else 0) else 0) := by
    intro c
    have hstep : ¬ (r.val < m * (k + 1) ∧ 1 ≤ r.val % (k + 1) ∧ c.1.val + 1 = r.val) := by
      omega
    have hjc : ¬ (r.val ≤ m * (k + 1) ∧ 0 < r.val ∧ (k + 1 : ℕ) ∣ r.val ∧
        r.val - (k + 1) ≤ c.1.val ∧ c.1.val < r.val) := by
      omega
    have hpad : (m * (k + 1) < r.val ∧ c.1.val + 1 = r.val) ↔ (c.1.val = r.val - 1) := by
      constructor
      · intro hp
        omega
      · intro hc
        exact ⟨hrg, by omega⟩
    have entry :
        taylorStepMatrixV2 m k p M (r, n) c =
          (if (r, n) = c then (1 : ℂ) else 0)
            - (if r.val < m * (k + 1) ∧ 1 ≤ r.val % (k + 1) ∧ c.1.val + 1 = r.val then
                M n c.2 / ((r.val % (k + 1) : ℕ) : ℂ) else 0)
            - (if r.val ≤ m * (k + 1) ∧ 0 < r.val ∧ (k + 1 : ℕ) ∣ r.val ∧
                r.val - (k + 1) ≤ c.1.val ∧ c.1.val < r.val then
                (if n = c.2 then (1 : ℂ) else 0) else 0)
            - (if m * (k + 1) < r.val ∧ c.1.val + 1 = r.val then
                (if n = c.2 then (1 : ℂ) else 0) else 0) := rfl
    rw [entry, if_neg hstep, if_neg hjc]
    simp only [hpad]
    ring
  simp only [Matrix.mulVec, dotProduct]
  simp only [hrow]
  simp only [sub_mul, Finset.sum_sub_distrib]
  have hS1 : ∑ c : Fin (m * (k + 1) + p + 1) × N,
      (if (r, n) = c then (1 : ℂ) else 0) * x c = x (r, n) := by
    simp only [ite_mul, one_mul, zero_mul]
    simp
  have hS2 : ∑ c : Fin (m * (k + 1) + p + 1) × N,
      (if c.1.val = r.val - 1 then (if n = c.2 then (1 : ℂ) else 0) else 0) * x c =
      x (⟨r.val - 1, by omega⟩, n) := by
    have hrew : ∀ c : Fin (m * (k + 1) + p + 1) × N,
        (if c.1.val = r.val - 1 then (if n = c.2 then (1 : ℂ) else 0) else 0) * x c =
        (if c.1 = (⟨r.val - 1, by omega⟩ : Fin (m * (k + 1) + p + 1)) then
          (if n = c.2 then (1 : ℂ) else 0) * x c else 0) := by
      intro c
      by_cases hc : c.1.val = r.val - 1
      · have hfin : c.1 = ⟨r.val - 1, by omega⟩ := Fin.ext hc
        simp [hfin]
      · have hfin : ¬ (c.1 = ⟨r.val - 1, by omega⟩) := by
          intro he
          have hv2 : c.1.val = r.val - 1 := by rw [he]
          omega
        simp [hfin, hc]
    simp only [hrew, sum_label_single, ite_mul, one_mul, zero_mul]
    simp
  rw [hS1, hS2]

end Rows

section Recursion

variable (m k p : ℕ) (A : Matrix N N ℂ) (h : ℝ) (x_in b : QState N)
  (x : QState (Fin (m * (k + 1) + p + 1) × N))

theorem taylorV2_block_zero
    (hx : taylorStepMatrixV2 m k p A *ᵥ x = taylorRHS m k p h x_in b) :
    taylorBlock x (taylorTimeLabel m k p 0 (Nat.zero_le m)) = x_in := by
  ext n
  have h1 := congrFun hx (taylorTimeLabel m k p 0 (Nat.zero_le m), n)
  rw [taylorV2_row_zero m k p A x n, taylorRHS_at_zero m k p h x_in b n] at h1
  simpa [taylorBlock] using! h1

theorem taylorV2_block_step
    (hx : taylorStepMatrixV2 m k p A *ᵥ x = taylorRHS m k p h x_in b)
    (a j : ℕ) (ha : a < m) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    taylorBlock x ⟨a * (k + 1) + j, step_label_lt a m k p j ha hjk⟩ =
      (((j : ℕ) : ℂ)⁻¹) • (A *ᵥ taylorBlock x ⟨a * (k + 1) + j - 1,
        pred_label_lt a m k p j ha hjk hj1⟩)
      + (if j = 1 then h • b else 0) := by
  ext n
  have hmod : (a * (k + 1) + j) % (k + 1) = j := label_mod_of_le a j k hjk
  have hlt : (a * (k + 1) + j) < m * (k + 1) := by
    have h1 : (a + 1) * (k + 1) = a * (k + 1) + (k + 1) := Nat.succ_mul a (k + 1)
    have h2 : (a + 1) * (k + 1) ≤ m * (k + 1) := by gcongr; omega
    omega
  have h1 := congrFun hx (⟨a * (k + 1) + j, step_label_lt a m k p j ha hjk⟩, n)
  rw [taylorV2_row_step m k p A x ⟨a * (k + 1) + j, step_label_lt a m k p j ha hjk⟩
    (by show 1 ≤ (a * (k + 1) + j) % (k + 1); omega)
    (by show (a * (k + 1) + j) < m * (k + 1); exact hlt) n,
    taylorRHS_at_step m k p h x_in b a j ha hj1 hjk n] at h1
  rw [hmod] at h1
  have hite : (if j = 1 then h • b else 0) n = if j = 1 then ↑h * b n else 0 := by
    by_cases hj : j = 1
    · simp [hj]
    · simp [hj]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, taylorBlock, hite]
  linear_combination h1

theorem taylorV2_block_jump
    (hx : taylorStepMatrixV2 m k p A *ᵥ x = taylorRHS m k p h x_in b)
    (a : ℕ) (ha1 : 1 ≤ a) (ham : a ≤ m) :
    taylorBlock x ⟨a * (k + 1), jump_label_lt a m k p ham⟩ =
      ∑ i : Fin (k + 1), taylorBlock x ⟨(a - 1) * (k + 1) + i, by
        have hi := i.isLt
        have hj := jump_label_lt a m k p ham
        have hgeo : (a - 1) * (k + 1) + (k + 1) = a * (k + 1) := by
          rw [← Nat.succ_mul, show Nat.succ (a - 1) = a from by omega]
        omega⟩ := by
  ext n
  have hgeo : (a - 1) * (k + 1) + (k + 1) = a * (k + 1) := by
    rw [← Nat.succ_mul, show Nat.succ (a - 1) = a from by omega]
  have hA1 : 1 * (k + 1) ≤ a * (k + 1) := Nat.mul_le_mul_right (k + 1) ha1
  have hA : (k + 1) ≤ a * (k + 1) := by simpa using! hA1
  have hlo : a * (k + 1) - (k + 1) = (a - 1) * (k + 1) := by omega
  have h1 := congrFun hx (⟨a * (k + 1), jump_label_lt a m k p ham⟩, n)
  rw [taylorV2_row_jump m k p A x ⟨a * (k + 1), jump_label_lt a m k p ham⟩
    (by show 0 < a * (k + 1); omega)
    (by show (k + 1 : ℕ) ∣ a * (k + 1)
        rw [Nat.mul_comm]
        exact Nat.dvd_mul_right (k + 1) a)
    (by show a * (k + 1) ≤ m * (k + 1); gcongr) n,
    taylorRHS_at_jump m k p h x_in b a ha1 ham n] at h1
  rw [hlo] at h1
  have hwin : (∑ c1 : Fin (m * (k + 1) + p + 1),
      (if (a - 1) * (k + 1) ≤ c1.val ∧ c1.val < a * (k + 1) then x (c1, n) else 0)) =
      (∑ q : Fin (k + 1), x (⟨(a - 1) * (k + 1) + q.val, by
        have hq := q.isLt
        have hj := jump_label_lt a m k p ham
        have hgeo' : (a - 1) * (k + 1) + (k + 1) = a * (k + 1) := by
          rw [← Nat.succ_mul, show Nat.succ (a - 1) = a from by omega]
        omega⟩, n)) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij'
      (fun c1 hc => ⟨c1.val - ((a - 1) * (k + 1)), by
        have := Finset.mem_filter.mp hc
        omega⟩)
      (fun q _ => ⟨(a - 1) * (k + 1) + q.val, by
        have hq := q.isLt
        have hj := jump_label_lt a m k p ham
        have hgeo' : (a - 1) * (k + 1) + (k + 1) = a * (k + 1) := by
          rw [← Nat.succ_mul, show Nat.succ (a - 1) = a from by omega]
        omega⟩)
      (fun c1 hc => Finset.mem_univ _)
      (fun q _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        show (a - 1) * (k + 1) ≤ (a - 1) * (k + 1) + q.val ∧
            (a - 1) * (k + 1) + q.val < a * (k + 1)
        have hq := q.isLt
        have hgeo' : (a - 1) * (k + 1) + (k + 1) = a * (k + 1) := by
          rw [← Nat.succ_mul, show Nat.succ (a - 1) = a from by omega]
        omega⟩)
      (fun c1 hc => by
        have := Finset.mem_filter.mp hc
        apply Fin.ext
        show (a - 1) * (k + 1) + (c1.val - ((a - 1) * (k + 1))) = c1.val
        omega)
      (fun q _ => by
        have hq := q.isLt
        apply Fin.ext
        show (a - 1) * (k + 1) + q.val - ((a - 1) * (k + 1)) = q.val
        omega)
      (fun c1 hc => by
        have hmem := Finset.mem_filter.mp hc
        have hfe : c1 = ⟨(a - 1) * (k + 1) + (c1.val - ((a - 1) * (k + 1))), by
          have hj := jump_label_lt a m k p ham
          omega⟩ := by
          apply Fin.ext
          show c1.val = (a - 1) * (k + 1) + (c1.val - ((a - 1) * (k + 1)))
          omega
        exact congrArg (fun w => x (w, n)) hfe)
  rw [show ((⟨a * (k + 1), jump_label_lt a m k p ham⟩ :
    Fin (m * (k + 1) + p + 1)).val) = a * (k + 1) from rfl] at h1
  simp only [Finset.sum_apply, taylorBlock]
  linear_combination h1 + hwin

theorem taylorV2_block_pad
    (hx : taylorStepMatrixV2 m k p A *ᵥ x = taylorRHS m k p h x_in b)
    (r rp : Fin (m * (k + 1) + p + 1)) (hval : rp.val + 1 = r.val)
    (hrg : m * (k + 1) < r.val) :
    taylorBlock x r = taylorBlock x rp := by
  ext n
  have h1 := congrFun hx (r, n)
  rw [taylorV2_row_pad m k p A x r hrg n] at h1
  have hrp : (⟨r.val - 1, by omega⟩ : Fin (m * (k + 1) + p + 1)) = rp := by
    apply Fin.ext
    show r.val - 1 = rp.val
    omega
  rw [taylorRHS_val_of_gt m k p h x_in b r hrg n, hrp] at h1
  simp only [taylorBlock]
  linear_combination h1

theorem taylorV2_pad_copies
    (hx : taylorStepMatrixV2 m k p A *ᵥ x = taylorRHS m k p h x_in b) :
    ∀ j : ℕ, (hj1 : 1 ≤ j) → (hjp : j ≤ p) →
      taylorBlock x ⟨m * (k + 1) + j, pad_label_lt m k p j hjp⟩ =
        taylorBlock x (taylorTimeLabel m k p m (le_refl m)) := by
  intro j hj1 hjp
  induction j with
  | zero => exact absurd hj1 (by omega)
  | succ j ih =>
    by_cases hj0 : 1 ≤ j
    · have hstep := taylorV2_block_pad m k p A h x_in b x hx
        ⟨m * (k + 1) + (j + 1), pad_label_lt m k p (j + 1) (by omega)⟩
        ⟨m * (k + 1) + j, pad_label_lt m k p j (by omega)⟩ (by
          show m * (k + 1) + j + 1 = m * (k + 1) + (j + 1)
          rfl)
        (by show m * (k + 1) < m * (k + 1) + (j + 1); omega)
      rw [hstep]
      exact ih hj0 (by omega)
    · have hjz : j = 0 := by omega
      subst hjz
      have hstep := taylorV2_block_pad m k p A h x_in b x hx
        ⟨m * (k + 1) + 1, pad_label_lt m k p 1 (by omega)⟩
        (taylorTimeLabel m k p m (le_refl m)) (by
          show m * (k + 1) + 1 = m * (k + 1) + 1
          rfl)
        (by show m * (k + 1) < m * (k + 1) + 1; omega)
      rw [hstep]

end Recursion

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
