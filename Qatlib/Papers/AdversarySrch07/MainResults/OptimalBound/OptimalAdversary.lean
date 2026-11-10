/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdversarySrch07.MainResults.Definitions
import Qatlib.Papers.AdversarySrch07.MainResults.XiSequence.XiConvolution
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators ENNReal
open Finset Matrix

namespace Qatlib.Papers.AdversarySrch07.MainResults.OptimalBound

open Qatlib.Papers.AdversarySrch07.MainResults
open Qatlib.Papers.AdversarySrch07.MainResults.XiSequence

theorem AM_zero (m : ℕ) : AM m 0 = ∑ i ∈ Finset.range m, xi i ^ 2 := by
  unfold AM
  simp only [Nat.sub_zero, Nat.add_zero, pow_two]

theorem AM_eq_zero {m j : ℕ} (h : m ≤ j) : AM m j = 0 := by
  unfold AM
  rw [Nat.sub_eq_zero_of_le h]
  simp

theorem xi_corr_antitone (k j : ℕ) :
    ∑ i ∈ Finset.range k, xi i * xi (i + (j + 1)) ≤
      ∑ i ∈ Finset.range (k + 1), xi i * xi (i + j) := by
  have hterm : ∑ i ∈ Finset.range k, xi i * xi (i + (j + 1)) ≤
      ∑ i ∈ Finset.range k, xi i * xi (i + j) := by
    apply Finset.sum_le_sum
    intro i _
    have hstep : xi (i + (j + 1)) ≤ xi (i + j) := by
      have := xi_antitone (i + j)
      rwa [show i + j + 1 = i + (j + 1) by ring] at this
    exact mul_le_mul_of_nonneg_left hstep (le_of_lt (xi_pos i))
  have hstep2 : ∑ i ∈ Finset.range k, xi i * xi (i + j) ≤
      ∑ i ∈ Finset.range (k + 1), xi i * xi (i + j) := by
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right
      (mul_nonneg (le_of_lt (xi_pos _)) (le_of_lt (xi_pos _)))
  exact hterm.trans hstep2

theorem AM_antitone (m j : ℕ) : AM m (j + 1) ≤ AM m j := by
  by_cases h : j + 1 ≤ m
  · unfold AM
    have e2 : m - j = (m - (j + 1)) + 1 := by omega
    rw [e2]
    exact xi_corr_antitone (m - (j + 1)) j
  · have hle : m ≤ j := by omega
    rw [AM_eq_zero (by omega : m ≤ j + 1), AM_eq_zero hle]

theorem AM_succ_diag (m : ℕ) : AM (m + 1) m = xi m := by
  unfold AM
  rw [show m + 1 - m = 1 by omega, Finset.sum_range_one]
  simp

noncomputable def objective (n : ℕ) (γ : ℕ → ℝ) : ℝ :=
  γ n + 2 * ∑ i ∈ Finset.range (n - 1), γ (i + 1)

theorem sum_range_telescope (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (f i - f (i + 1)) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

noncomputable def gammaEven (m : ℕ) (i : ℕ) : ℝ := AM m (i - 1) - AM m i

noncomputable def gammaOdd (m : ℕ) (i : ℕ) : ℝ :=
  ((AM (m + 1) (i - 1) - AM (m + 1) i) + (AM m (i - 1) - AM m i)) / 2

def toeplitz (n : ℕ) (γ : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => γ (n - Int.natAbs ((i.val : ℤ) - (j.val : ℤ)))

noncomputable def uEven (m : ℕ) : Fin (2 * m) → ℝ :=
  fun k => if k.val < m then xi k.val else xi (2 * m - 1 - k.val)

noncomputable def uOdd (m : ℕ) : Fin (2 * m + 1) → ℝ :=
  fun k => if k.val ≤ m then xi k.val else xi (2 * m - k.val)

theorem gammaEven_apply_succ (m i : ℕ) : gammaEven m (i + 1) = AM m i - AM m (i + 1) := by
  unfold gammaEven; rw [Nat.add_sub_cancel]

theorem gammaOdd_apply_succ (m i : ℕ) :
    gammaOdd m (i + 1) = ((AM (m + 1) i - AM (m + 1) (i + 1)) + (AM m i - AM m (i + 1))) / 2 := by
  unfold gammaOdd; rw [Nat.add_sub_cancel]

theorem gammaEven_nonneg (m i : ℕ) : 0 ≤ gammaEven m i := by
  unfold gammaEven
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi; simp
  · have hpred : i - 1 + 1 = i := Nat.succ_pred_eq_of_pos hi
    have hle : AM m i ≤ AM m (i - 1) := by
      have := AM_antitone m (i - 1); rwa [hpred] at this
    linarith

theorem gammaOdd_nonneg (m i : ℕ) : 0 ≤ gammaOdd m i := by
  unfold gammaOdd
  have h1 : 0 ≤ AM (m + 1) (i - 1) - AM (m + 1) i := by
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; simp
    · have hpred : i - 1 + 1 = i := Nat.succ_pred_eq_of_pos hi
      have hle : AM (m + 1) i ≤ AM (m + 1) (i - 1) := by
        have := AM_antitone (m + 1) (i - 1); rwa [hpred] at this
      linarith
  have h2 : 0 ≤ AM m (i - 1) - AM m i := by
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; simp
    · have hpred : i - 1 + 1 = i := Nat.succ_pred_eq_of_pos hi
      have hle : AM m i ≤ AM m (i - 1) := by
        have := AM_antitone m (i - 1); rwa [hpred] at this
      linarith
  linarith

theorem objective_gammaEven (m : ℕ) :
    objective (2 * m) (gammaEven m) = 2 * AM m 0 := by
  have hlast : gammaEven m (2 * m) = 0 := by
    unfold gammaEven
    rw [AM_eq_zero (by omega : m ≤ 2 * m - 1), AM_eq_zero (by omega : m ≤ 2 * m)]
    ring
  unfold objective
  have hsum : ∑ i ∈ Finset.range (2 * m - 1), gammaEven m (i + 1) =
      AM m 0 - AM m (2 * m - 1) := by
    have h : ∀ i, gammaEven m (i + 1) = AM m i - AM m (i + 1) := gammaEven_apply_succ m
    simp_rw [h]
    exact sum_range_telescope (fun i => AM m i) (2 * m - 1)
  rw [hsum, hlast]
  have hzero : AM m (2 * m - 1) = 0 := AM_eq_zero (by omega)
  rw [hzero]; ring

theorem objective_gammaOdd (m : ℕ) (hm : 1 ≤ m) :
    objective (2 * m + 1) (gammaOdd m) = AM (m + 1) 0 + AM m 0 := by
  have hlast : gammaOdd m (2 * m + 1) = 0 := by
    unfold gammaOdd
    have e : 2 * m + 1 - 1 = 2 * m := by omega
    rw [e, AM_eq_zero (by omega : m + 1 ≤ 2 * m), AM_eq_zero (by omega : m + 1 ≤ 2 * m + 1),
      AM_eq_zero (by omega : m ≤ 2 * m), AM_eq_zero (by omega : m ≤ 2 * m + 1)]
    ring
  unfold objective
  rw [show 2 * m + 1 - 1 = 2 * m by omega]
  have hsum : ∑ i ∈ Finset.range (2 * m), gammaOdd m (i + 1) =
      ((AM (m + 1) 0 - AM (m + 1) (2 * m)) + (AM m 0 - AM m (2 * m))) / 2 := by
    have h : ∀ i, gammaOdd m (i + 1) =
        ((AM (m + 1) i - AM (m + 1) (i + 1)) + (AM m i - AM m (i + 1))) / 2 :=
      gammaOdd_apply_succ m
    simp_rw [h]
    rw [← Finset.sum_div]
    rw [Finset.sum_add_distrib, sum_range_telescope, sum_range_telescope]
  rw [hsum, hlast]
  have hz1 : AM (m + 1) (2 * m) = 0 := AM_eq_zero (by omega)
  have hz2 : AM m (2 * m) = 0 := AM_eq_zero (by omega)
  rw [hz1, hz2]; ring

theorem inner_split (g : ℕ → ℕ → ℝ) (s : ℕ) :
    ∑ i ∈ Finset.range (s + 1 + 1), g i (s + 1 - i)
      = g 0 (s + 1) + ∑ i ∈ Finset.range (s + 1), g (i + 1) (s - i) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
  rw [add_comm]

theorem sum_triangle (N : ℕ) : ∀ g : ℕ → ℕ → ℝ,
    (∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (N - i), g i k)
      = ∑ s ∈ Finset.range N, ∑ i ∈ Finset.range (s + 1), g i (s - i) := by
  induction N with
  | zero => intro g; simp
  | succ N ih =>
    intro g
    have hL : (∑ i ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1 - i), g i k)
        = (∑ k ∈ Finset.range (N + 1), g 0 k)
          + ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (N - i), g (i + 1) k := by
      rw [Finset.sum_range_succ']
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      exact add_comm _ _
    have hR : (∑ s ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (s + 1), g i (s - i))
        = (∑ k ∈ Finset.range (N + 1), g 0 k)
          + ∑ s ∈ Finset.range N, ∑ i ∈ Finset.range (s + 1), g (i + 1) (s - i) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.zero_sub, Nat.zero_add, Finset.sum_range_one]
      conv_rhs => rw [Finset.sum_range_succ']
      simp_rw [inner_split g]
      rw [Finset.sum_add_distrib]
      ring
    rw [hL, hR, ih (fun i k => g (i + 1) k)]

theorem corr_sum_shift (m j : ℕ) (_hj : j < m) :
    ∑ i ∈ Finset.range (m - j), AM m (i + j) * xi i
      = ∑ s ∈ Finset.range (m - j), xi (s + j) := by
  have hEq : ∀ i ∈ Finset.range (m - j), m - (i + j) = (m - j) - i := by
    intro i hi; have := Finset.mem_range.mp hi; omega
  have hstep : ∑ i ∈ Finset.range (m - j), AM m (i + j) * xi i
      = ∑ i ∈ Finset.range (m - j),
          ∑ k ∈ Finset.range ((m - j) - i), xi k * xi (k + (i + j)) * xi i := by
    apply Finset.sum_congr rfl
    intro i hi
    unfold AM
    rw [hEq i hi, Finset.sum_mul]
  rw [hstep, sum_triangle]
  apply Finset.sum_congr rfl
  intro s _
  have hfac : ∀ i ∈ Finset.range (s + 1),
      xi (s - i) * xi ((s - i) + (i + j)) * xi i = xi (s + j) * (xi i * xi (s - i)) := by
    intro i hi
    have his : i ≤ s := Finset.mem_range_succ_iff.mp hi
    rw [show (s - i) + (i + j) = s + j by omega]
    ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum, source_proposition_four s]; ring

theorem corr_sum_shift_succ (m j : ℕ) (hj : j < m) :
    ∑ i ∈ Finset.range (m - j), AM m (i + j + 1) * xi i
      = ∑ s ∈ Finset.range (m - j - 1), xi (s + j + 1) := by
  have hsplit : ∑ i ∈ Finset.range (m - j), AM m (i + j + 1) * xi i
      = ∑ i ∈ Finset.range (m - j - 1), AM m (i + j + 1) * xi i := by
    conv_lhs => rw [show m - j = (m - j - 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    have hz : AM m ((m - j - 1) + j + 1) = 0 := by
      apply AM_eq_zero
      omega
    rw [hz]; ring
  rw [hsplit]
  have hEq : ∀ i ∈ Finset.range (m - j - 1), m - (i + j + 1) = (m - j - 1) - i := by
    intro i hi; have := Finset.mem_range.mp hi; omega
  have hstep : ∑ i ∈ Finset.range (m - j - 1), AM m (i + j + 1) * xi i
      = ∑ i ∈ Finset.range (m - j - 1),
          ∑ k ∈ Finset.range ((m - j - 1) - i), xi k * xi (k + (i + j + 1)) * xi i := by
    apply Finset.sum_congr rfl
    intro i hi
    unfold AM
    rw [hEq i hi, Finset.sum_mul]
  rw [hstep, sum_triangle]
  apply Finset.sum_congr rfl
  intro s _
  have hfac : ∀ i ∈ Finset.range (s + 1),
      xi (s - i) * xi ((s - i) + (i + j + 1)) * xi i = xi (s + j + 1) * (xi i * xi (s - i)) := by
    intro i hi
    have his : i ≤ s := Finset.mem_range_succ_iff.mp hi
    rw [show (s - i) + (i + j + 1) = s + j + 1 by omega]
    ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum, source_proposition_four s]; ring

theorem eigen_identity (m j : ℕ) (hj : j < m) :
    ∑ i ∈ Finset.range (m - j), (AM m (i + j) - AM m (i + j + 1)) * xi i = xi j := by
  have hsub : ∑ i ∈ Finset.range (m - j), (AM m (i + j) - AM m (i + j + 1)) * xi i
      = (∑ i ∈ Finset.range (m - j), AM m (i + j) * xi i)
        - ∑ i ∈ Finset.range (m - j), AM m (i + j + 1) * xi i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hsplit : ∑ s ∈ Finset.range (m - j), xi (s + j)
      = (∑ s ∈ Finset.range (m - j - 1), xi (s + j + 1)) + xi j := by
    conv_lhs => rw [show m - j = (m - j - 1) + 1 by omega]
    rw [Finset.sum_range_succ']
    simp_rw [show ∀ s : ℕ, xi ((s + 1) + j) = xi (s + j + 1) by
      intro s; rw [show (s + 1) + j = s + j + 1 by omega]]
    simp
  rw [hsub, corr_sum_shift m j hj, corr_sum_shift_succ m j hj, hsplit]
  ring

end Qatlib.Papers.AdversarySrch07.MainResults.OptimalBound
