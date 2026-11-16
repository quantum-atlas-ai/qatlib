/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TreeSizeEst17.MainResults.Bounds
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # Counterexamples to underspecified legacy contracts, arXiv:1704.06774v3.
These reject the old Lean statements, not the paper's graph and spectral theorems.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.TreeSizeEst17.MainResults

/-- At overlap parameter one, the legacy logarithmic bound vanishes although the count is positive. -/
theorem repetitions_positive : 0 < lemmaOneRepetitions 1 1 (1 / 2) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have ht : 0 < Nat.ceil (Real.log (2 : ℝ) ^ 2) := Nat.ceil_pos.mpr (sq_pos_of_pos hlog)
  have htR : (0 : ℝ) < Nat.ceil (Real.log (2 : ℝ) ^ 2) := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ Nat.ceil (Real.log (2 : ℝ) ^ 2) := by exact_mod_cast ht
  have harg : (1 : ℝ) < 2 * (Nat.ceil (Real.log (2 : ℝ) ^ 2) : ℝ) / (1 / 2) := by
    linarith
  have hsecond : 0 < Nat.ceil (Real.log (2 * (Nat.ceil (Real.log (2 : ℝ) ^ 2) : ℝ) / (1 / 2))) :=
    Nat.ceil_pos.mpr (Real.log_pos harg)
  unfold lemmaOneRepetitions
  norm_num only [one_div_one, one_mul, one_div_div, div_one]
  exact mul_pos htR (by exact_mod_cast hsecond)

/-- No constant repairs the legacy bound at C=1; a clamped logarithm is necessary. -/
theorem repetition_bound_false (c : ℕ) :
    ¬ lemmaOneRepetitions 1 1 (1 / 2) ≤
      (c : ℝ) * (1 / 1) * (1 / 1) * Real.log (1 / 1) * (Real.log (1 / (1 / 2))) ^ 2 := by
  simpa using (not_le.mpr repetitions_positive)

/-- The old overlap theorem leaves the overlap unrelated to its spectral parameters. -/
theorem overlap_counterexample :
    ∃ n alpha overlap : ℝ, 0 < n ∧ Real.sqrt (2 * n) ≤ alpha ∧ ¬ (2 / 3 ≤ overlap) := by
  exact ⟨1, Real.sqrt 2, 0, by norm_num, by norm_num, by norm_num⟩

/-- Two unrestricted subspaces need not have trivial intersection. -/
theorem subspace_counterexample :
    ∃ HA HB : Submodule ℝ ℝ, HA ⊓ HB ≠ ⊥ := by
  exact ⟨⊤, ⊤, by simp⟩

/-- Row sums alone do not identify the arbitrary number called the maximal eigenvalue. -/
theorem eigenvalue_counterexample :
    ∃ K : Matrix (Fin 1) (Fin 1) ℝ,
      (∀ i, (∑ j, K i j) = 0) ∧ ¬ ((0 : ℝ) ≤ 1 ∧ 1 ≤ (1 + 1) * 0) := by
  exact ⟨0, by simp, by norm_num⟩

/-- An arbitrary zero matrix does not have the corner entries of the fundamental matrix. -/
theorem corner_counterexample :
    (0 : Fin 2) ≠ 1 ∧ (1 / 2 : ℝ) ≠ 0 ∧ (1 / 2 : ℝ) ≠ 1 ∧
      ¬ (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 1 / (1 - (1 / 2 : ℝ)) := by
  norm_num

/-- The first-column formula fails for unrestricted matrices even at positive d1. -/
theorem column_counterexample :
    ¬ ∀ i : Fin 1, (0 : Matrix (Fin 1) (Fin 1) ℝ) i 0 = 1 / (1 : ℝ) := by
  norm_num

/-- The harmonic formula needs the fundamental-matrix relation absent from the old statement. -/
theorem harmonic_counterexample :
    ¬ ∀ i j : Fin 3, i ≠ 0 → i ≠ 2 → j ≠ 2 →
      (0 : Matrix (Fin 3) (Fin 3) ℝ) i j =
        (0 : ℝ) ^ 2 + 1 / 1 + (1 - 0) * 0 := by
  intro h
  have := h 1 1 (by decide) (by decide) (by decide)
  norm_num at this

/-- An arbitrary zero matrix is not the Green matrix of a rooted tree. -/
theorem ancestor_counterexample :
    ¬ ∀ i j : Fin 1, (0 : Matrix (Fin 1) (Fin 1) ℝ) i j =
      (0 : ℝ) ^ 2 + 1 / 1 + 0 := by
  norm_num

/-- The nonnegative Green-function bound fails without the Green-function hypotheses. -/
theorem depth_counterexample :
    ¬ (0 : ℝ) ≤ (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 - ((0 : ℝ) ^ 2 + 1 / 1) := by
  norm_num

/-- The block-inverse identity fails when K is unrelated to the other matrices. -/
theorem factor_counterexample :
    (1 : Matrix (Fin 1) (Fin 1) ℝ) ≠
      Matrix.diagonal (fun _ => (0 : ℝ)) * (0 : Matrix (Fin 1) (Fin 1) ℝ) *
        Matrix.diagonal (fun _ => (0 : ℝ)) := by
  simp

/-- A nonempty vertex set cannot be bounded by an unrelated zero depth budget. -/
theorem heavy_counterexample :
    ¬ (({0} : Finset ℕ).card : ℝ) ≤ (0 : ℝ) * 6 * 1 / 1 := by
  norm_num

/-- Two unconstrained states need not have zero error at epsilon zero. -/
theorem state_counterexample :
    ¬ ‖(1 : ℝ) - (-1 : ℝ) ^ (0 : ℕ) • (0 : ℝ)‖ ≤ 2 * Real.sqrt (0 : ℝ) := by
  norm_num

end Qatlib.Papers.TreeSizeEst17.MainResults
