/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# Ideal flag rotation in Lemma 11

In arXiv:1705.01843v4 the squared flag-zero amplitude for each diagonal
entry is obtained by taking the sine of its inverse-sine angle. A
uniform input register averages these probabilities.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Matrix
open Qatlib.Papers.QSDPsolver17.MainResults

namespace Qatlib.Papers.QSDPsolver17.MainResults

variable {n : ℕ}

/-- The target flag probability at one diagonal entry in Lemma 11. -/
def diagonalFlagWeight (A H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  (1 + A i i / 2) / 4 * Real.exp (-(H i i))

/-- The induced norm hypothesis bounds every diagonal entry by one. -/
private theorem abs_diag_le_one (A : Matrix (Fin n) (Fin n) ℝ) (hA : OpNormLE_R A 1) (i : Fin n) :
    |A i i| ≤ 1 := by
  let v : EuclideanSpace ℝ (Fin n) := PiLp.single 2 i 1
  have h := (opNormLE_R_iff_mulVec A (by norm_num : 0 ≤ (1 : ℝ))).mp hA v
  have hcoord := (PiLp.norm_apply_le (WithLp.toLp 2 (A.mulVec v.ofLp)) i).trans h
  simpa [v, PiLp.ofLp_single, PiLp.norm_single, Matrix.mulVec_single_one, Matrix.col,
    Real.norm_eq_abs] using hcoord

/-- The flag probability lies between zero and the source's upper bound `3/8`. -/
theorem diagonalFlagWeight_bounds (A H : Matrix (Fin n) (Fin n) ℝ)
    (hA : OpNormLE_R A 1) (hH : ∀ i, 0 ≤ H i i) (i : Fin n) :
    0 ≤ diagonalFlagWeight A H i ∧ diagonalFlagWeight A H i ≤ 3 / 8 := by
  have ha := abs_le.mp (abs_diag_le_one A hA i)
  have hp : 0 ≤ (1 + A i i / 2) / 4 := by linarith [ha.1]
  unfold diagonalFlagWeight
  exact ⟨mul_nonneg hp (Real.exp_pos _).le,
    (mul_le_of_le_one_right hp (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hH i)))).trans
      (by linarith [ha.2])⟩

/-- The ideal controlled angles yield the prescribed average flag
probability in the diagonal model of Lemma 11. -/
theorem lemma11_diagonal_flag_exact (A H : Matrix (Fin n) (Fin n) ℝ)
    (hA : OpNormLE_R A 1) (hH : ∀ i, 0 ≤ H i i) :
    (∑ i, Real.sin (Real.arcsin (Real.sqrt (diagonalFlagWeight A H i))) ^ 2) / (n : ℝ) =
      (∑ i, diagonalFlagWeight A H i) / (n : ℝ) := by
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hp := diagonalFlagWeight_bounds A H hA hH i
  rw [Real.sin_arcsin ((by norm_num : (-1 : ℝ) ≤ 0).trans (Real.sqrt_nonneg _))
    (Real.sqrt_le_one.mpr (hp.2.trans (by norm_num))), Real.sq_sqrt hp.1]

/-- Given per-entry additive probability errors bounded by `μ`,
the uniform-branch estimate has additive error at most `μ`. -/
theorem lemma11_diagonal_flag_additive_error (hn : 0 < n)
    (p δ : Fin n → ℝ) (μ : ℝ) (hδ : ∀ i, |δ i| ≤ μ) :
    |(∑ i, (p i + δ i)) / (n : ℝ) - (∑ i, p i) / (n : ℝ)| ≤ μ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Finset.sum_add_distrib, add_div, add_sub_cancel_left, abs_div, abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑ i, |δ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, μ := Finset.sum_le_sum fun i _ => hδ i
    _ = _ := by simp [mul_comm]

end Qatlib.Papers.QSDPsolver17.MainResults
