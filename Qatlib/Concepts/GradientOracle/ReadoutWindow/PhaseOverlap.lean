/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Overlap under bounded phase perturbations

This module computes the overlap of a vector with its componentwise phase perturbation. For
normalized vectors and phase angles bounded by `θ ≤ π/2`, it proves real-overlap and
squared-overlap lower bounds used in the precision analysis of [Jordan2005Gradient].

## Main statements

* `re_overlap_phasePerturbed_ge_cos`: real overlap is at least `cos θ`.
* `normSq_overlap_phasePerturbed_ge_cos_sq`: squared overlap is at least `cos θ ^ 2`.
* `overlap_preserved_by_isometry`: complex linear isometries preserve inner products.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace

namespace Qatlib.Concepts.GradientOracle.ReadoutWindow

variable {n : ℕ}

/-- The vector obtained by multiplying component `j` of `a` by `exp (i * δ j)`. -/
def phasePerturbed (a : Fin n → ℂ) (δ : Fin n → ℝ) : Fin n → ℂ :=
  fun j => a j * Complex.exp ((δ j : ℂ) * Complex.I)

/-- The complex overlap `∑ j, conj (a j) * b j` of two finite vectors. -/
def overlap (a b : Fin n → ℂ) : ℂ := ∑ j, star (a j) * b j

/-- The real overlap of a vector with its phase perturbation is the sum of `‖a j‖^2 * cos (δ
j)`. -/
theorem re_overlap_phasePerturbed (a : Fin n → ℂ) (δ : Fin n → ℝ) :
    (overlap a (phasePerturbed a δ)).re = ∑ j, ‖a j‖ ^ 2 * Real.cos (δ j) := by
  unfold overlap phasePerturbed
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hsq : star (a j) * a j = ((‖a j‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hres : (star (a j) * (a j * Complex.exp ((δ j : ℂ) * Complex.I))).re
      = ‖a j‖ ^ 2 * Real.cos (δ j) := by
    rw [← mul_assoc, hsq, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  exact hres

/-- For a normalized vector and phase angles bounded in absolute value by `0 ≤ θ ≤ π/2`, the
real overlap with the perturbed vector is at least `cos θ`. See [Jordan2005Gradient]. -/
theorem re_overlap_phasePerturbed_ge_cos (a : Fin n → ℂ) (δ : Fin n → ℝ) (θ : ℝ)
    (hnorm : ∑ j, ‖a j‖ ^ 2 = 1)
    (hδ : ∀ j, |δ j| ≤ θ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi / 2) :
    Real.cos θ ≤ (overlap a (phasePerturbed a δ)).re := by
  rw [re_overlap_phasePerturbed]
  have hcos : ∀ j, Real.cos θ ≤ Real.cos (δ j) := by
    intro j
    have h : Real.cos θ ≤ Real.cos |δ j| :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) (hδ j)
    rwa [Real.cos_abs] at h
  calc Real.cos θ = ∑ j, ‖a j‖ ^ 2 * Real.cos θ := by
        rw [← Finset.sum_mul, hnorm, one_mul]
    _ ≤ ∑ j, ‖a j‖ ^ 2 * Real.cos (δ j) := by
        refine Finset.sum_le_sum ?_
        intro j _
        exact mul_le_mul_of_nonneg_left (hcos j) (sq_nonneg _)

/-- For a normalized vector and phase angles bounded by `0 ≤ θ ≤ π/2`, the squared overlap with
its phase perturbation is at least `cos θ ^ 2`. See [Jordan2005Gradient]. -/
theorem normSq_overlap_phasePerturbed_ge_cos_sq (a : Fin n → ℂ) (δ : Fin n → ℝ) (θ : ℝ)
    (hnorm : ∑ j, ‖a j‖ ^ 2 = 1)
    (hδ : ∀ j, |δ j| ≤ θ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi / 2) :
    Real.cos θ ^ 2 ≤ Complex.normSq (overlap a (phasePerturbed a δ)) := by
  have hre := re_overlap_phasePerturbed_ge_cos a δ θ hnorm hδ hθ0 hθπ
  have hRe_nonneg : 0 ≤ (overlap a (phasePerturbed a δ)).re :=
    le_trans (Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθπ⟩) hre
  have hbound : Real.cos θ ^ 2 ≤ (overlap a (phasePerturbed a δ)).re ^ 2 := by
    exact pow_le_pow_left₀ (Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθπ⟩) hre 2
  have hnorm : (overlap a (phasePerturbed a δ)).re ^ 2
      ≤ Complex.normSq (overlap a (phasePerturbed a δ)) := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (overlap a (phasePerturbed a δ)).im]
  exact le_trans hbound hnorm

/-- A phase perturbation of a basis vector retains squared amplitude one at its supported
coordinate. -/
theorem measProb_phasePerturbed_single (k : Fin n) (δ : Fin n → ℝ) :
    ‖phasePerturbed (fun j => if j = k then (1 : ℂ) else 0) δ k‖ ^ 2 = 1 := by
  unfold phasePerturbed
  have h1 : ((fun j => if j = k then (1 : ℂ) else 0) k) = 1 := by simp
  rw [h1, one_mul, Complex.norm_exp_ofReal_mul_I, one_pow]

/-- For `0 ≤ θ ≤ π/2`, the squared amplitude at the support of a phase-perturbed basis vector is
at least `cos θ ^ 2`. See [Jordan2005Gradient]. -/
theorem measProb_phasePerturbed_single_ge_cos_sq (k : Fin n) (δ : Fin n → ℝ) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi / 2) :
    Real.cos θ ^ 2 ≤ ‖phasePerturbed (fun j => if j = k then (1 : ℂ) else 0) δ k‖ ^ 2 := by
  rw [measProb_phasePerturbed_single]
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθπ⟩
  nlinarith [sq_nonneg (Real.cos θ), hc, Real.cos_le_one θ]

/-- A complex linear isometric equivalence preserves the inner product of any two vectors. This
supplies overlap invariance in the precision setting of [Jordan2005Gradient]. -/
theorem overlap_preserved_by_isometry {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (U : E ≃ₗᵢ[ℂ] E) (a b : E) :
    ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ :=
  U.inner_map_map a b

end Qatlib.Concepts.GradientOracle.ReadoutWindow
