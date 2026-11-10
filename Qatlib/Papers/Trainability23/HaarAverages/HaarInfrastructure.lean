/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Linarith

namespace Qatlib.Papers.Trainability23.HaarAverages

theorem unitaryGroup_mul_star_diag {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A ∈ Matrix.unitaryGroup n ℂ) (i : n) :
    ∑ k, A i k * star (A i k) = 1 := by
  have h1 : (A * star A) i i = 1 := by
    rw [Matrix.mem_unitaryGroup_iff.mp hA, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h1
  rw [← h1]
  exact Finset.sum_congr rfl fun k _ => by rw [Matrix.star_apply]

theorem unitaryGroup_sum_normSq {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A ∈ Matrix.unitaryGroup n ℂ) (i : n) :
    ∑ k, ‖A i k‖ ^ 2 = 1 := by
  have hcast : ((∑ k, ‖A i k‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum, ← unitaryGroup_mul_star_diag hA i]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcast' : ((∑ k, ‖A i k‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_one]
    exact hcast
  exact Complex.ofReal_injective hcast'

theorem unitaryGroup_entry_normSq_le_one {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A ∈ Matrix.unitaryGroup n ℂ) (i j : n) :
    ‖A i j‖ ^ 2 ≤ 1 := by
  have hterm : ‖A i j‖ ^ 2 ≤ ∑ k, ‖A i k‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖A i k‖ ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ j)
  rw [unitaryGroup_sum_normSq hA i] at hterm
  exact hterm

theorem unitaryGroup_entry_norm_le_one {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A ∈ Matrix.unitaryGroup n ℂ) (i j : n) :
    ‖A i j‖ ≤ 1 := by
  have h := unitaryGroup_entry_normSq_le_one hA i j
  nlinarith [norm_nonneg (A i j)]

end Qatlib.Papers.Trainability23.HaarAverages
