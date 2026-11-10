/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Defs
import Qatlib.Papers.NonSparseHam09.MainResults.NormChain
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma norm_one_matrix : ‖(1 : Matrix ι ι ℂ)‖ = 1 := by
  rw [← specNorm_eq_l2, specNorm_one]

lemma unitary_mul_star (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    U * Uᴴ = 1 := by
  rw [← Matrix.star_eq_conjTranspose U]
  exact Matrix.mem_unitaryGroup_iff.mp hU

lemma unitary_star_mul (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    Uᴴ * U = 1 := by
  rw [← Matrix.star_eq_conjTranspose U]
  exact Matrix.mem_unitaryGroup_iff'.mp hU

lemma unitary_star_mem (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    Uᴴ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [show star (Uᴴ) = U by rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_involutive]]
  exact unitary_star_mul U hU

lemma norm_unitary (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) : ‖U‖ = 1 := by
  have h2 : ‖U‖ * ‖U‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self U, unitary_star_mul U hU, norm_one_matrix]
  nlinarith [norm_nonneg U]

lemma specNorm_conjTranspose (H : Matrix ι ι ℂ) : specNorm Hᴴ = specNorm H := by
  rw [specNorm_eq_l2, specNorm_eq_l2, Matrix.l2_opNorm_conjTranspose]

lemma specNorm_mul_unitary_left (U : Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) : specNorm (U * H) = specNorm H := by
  refine le_antisymm ?_ ?_
  · rw [specNorm_eq_l2, specNorm_eq_l2]
    calc ‖U * H‖ ≤ ‖U‖ * ‖H‖ := Matrix.l2_opNorm_mul U H
      _ = ‖H‖ := by rw [norm_unitary U hU, one_mul]
  · rw [specNorm_eq_l2, specNorm_eq_l2]
    have he : Uᴴ * (U * H) = H := by
      rw [← Matrix.mul_assoc, unitary_star_mul U hU, Matrix.one_mul]
    calc ‖H‖ = ‖Uᴴ * (U * H)‖ := by rw [he]
      _ ≤ ‖Uᴴ‖ * ‖U * H‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖U * H‖ := by
          rw [Matrix.l2_opNorm_conjTranspose, norm_unitary U hU, one_mul]

lemma specNorm_mul_unitary_right (U : Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) : specNorm (H * U) = specNorm H := by
  refine le_antisymm ?_ ?_
  · rw [specNorm_eq_l2, specNorm_eq_l2]
    calc ‖H * U‖ ≤ ‖H‖ * ‖U‖ := Matrix.l2_opNorm_mul H U
      _ = ‖H‖ := by rw [norm_unitary U hU, mul_one]
  · rw [specNorm_eq_l2, specNorm_eq_l2]
    have he : H * U * Uᴴ = H := by
      rw [Matrix.mul_assoc, unitary_mul_star U hU, Matrix.mul_one]
    calc ‖H‖ = ‖H * U * Uᴴ‖ := by rw [he]
      _ ≤ ‖H * U‖ * ‖Uᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖H * U‖ := by
          rw [Matrix.l2_opNorm_conjTranspose, norm_unitary U hU, mul_one]

theorem specNorm_conj_unitary (U : Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    specNorm (U * H * Uᴴ) = specNorm H := by
  rw [Matrix.mul_assoc, specNorm_mul_unitary_left U (H * Uᴴ) hU,
    specNorm_mul_unitary_right Uᴴ H (unitary_star_mem U hU)]

theorem specNorm_abs_of_gauge (U : Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (hconj : U * H * Uᴴ = (absMatrix H).map Complex.ofReal) :
    specNorm ((absMatrix H).map Complex.ofReal) = specNorm H := by
  have h := specNorm_conj_unitary U H hU
  rw [hconj] at h
  exact h

lemma diagonal_mem_unitaryGroup (φ : ι → ℂ) (hφ : ∀ i, ‖φ i‖ = 1) :
    Matrix.diagonal φ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl]
    simp only [Pi.star_apply]
    have hz : φ i * star (φ i) = (‖φ i‖ : ℂ) ^ 2 := RCLike.mul_conj (φ i)
    rw [hz, hφ i]
    norm_num
  · rw [if_neg h, if_neg h]

theorem diagonal_gauge_eq_abs (φ : ι → ℂ) (H : Matrix ι ι ℂ)
    (hentry : ∀ i j, φ i * H i j * star (φ j) = ((‖H i j‖ : ℝ) : ℂ)) :
    Matrix.diagonal φ * H * (Matrix.diagonal φ)ᴴ = (absMatrix H).map Complex.ofReal := by
  ext i j
  rw [Matrix.mul_assoc, Matrix.diagonal_conjTranspose]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  have hR : (absMatrix H).map Complex.ofReal i j = ((‖H i j‖ : ℝ) : ℂ) := by
    simp [absMatrix, Matrix.map_apply]
  rw [hR, ← hentry i j, mul_assoc]

end Qatlib.Papers.NonSparseHam09.MainResults
