/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRange
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
open Qatlib.Foundations.OpCalculus.ContourCalc

/-!
# Numerical-range separation and actual resolvents

Cauchy--Schwarz turns separation from the Rayleigh quotients into a lower
singular-value bound.  In finite dimension this constructs a two-sided inverse,
with norm at most the reciprocal separation.  No normality is required.
The inverse is a mathematical operator, not a query circuit.
-/
namespace Qatlib.Foundations.OpCalculus.ContourCalc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Numerical-range values are bounded by the operator norm, with no assertion
that this enclosure is tight. -/
theorem norm_le_of_mem_numericalRange (A : E →L[ℂ] E) {w : ℂ}
    (hw : w ∈ numericalRange A) : ‖w‖ ≤ ‖A‖ := by
  obtain ⟨x, hx, rfl⟩ := hw
  calc
    ‖inner ℂ x (A x)‖ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg x)
    _ = ‖A‖ := by rw [hx]; simp

/-- A positive separation certificate bounds every shifted output from below. -/
theorem shiftedOperator_lower_bound (A : E →L[ℂ] E) (z : ℂ) (r : ℝ)
    (hsep : ∀ w ∈ numericalRange A, r ≤ ‖z - w‖) (x : E) :
    r * ‖x‖ ≤ ‖shiftedOperator A z x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let u : E := ((‖x‖ : ℂ)⁻¹) • x
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, norm_inv, Complex.norm_real, inv_mul_cancel₀ hn.ne']
  have hw : inner ℂ u (A u) ∈ numericalRange A := ⟨u, hu, rfl⟩
  have hi : inner ℂ u (shiftedOperator A z u) = z - inner ℂ u (A u) := by
    simp [shiftedOperator, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hu]
  have hb : r ≤ ‖shiftedOperator A z u‖ := by
    calc
      r ≤ ‖z - inner ℂ u (A u)‖ := hsep _ hw
      _ = ‖inner ℂ u (shiftedOperator A z u)‖ := congrArg norm hi.symm
      _ ≤ ‖u‖ * ‖shiftedOperator A z u‖ := norm_inner_le_norm _ _
      _ = ‖shiftedOperator A z u‖ := by rw [hu, one_mul]
  have hs : ‖shiftedOperator A z u‖ = ‖shiftedOperator A z x‖ / ‖x‖ := by
    simp [u, map_smul, norm_smul, norm_inv, Complex.norm_real, div_eq_inv_mul]
  rw [hs] at hb
  exact (le_div_iff₀ hn).mp hb

/-- Separation produces an actual two-sided inverse and its reciprocal norm
bound.  Empty spaces are included; the range hypothesis is then vacuous. -/
theorem exists_resolvent_of_numericalRange_separation [FiniteDimensional ℂ E]
    (A : E →L[ℂ] E) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ w ∈ numericalRange A, r ≤ ‖z - w‖) :
    ∃ R : E →L[ℂ] E,
      (shiftedOperator A z).comp R = ContinuousLinearMap.id ℂ E ∧
      R.comp (shiftedOperator A z) = ContinuousLinearMap.id ℂ E ∧
      ‖R‖ ≤ r⁻¹ := by
  let S := shiftedOperator A z
  have hzero : ∀ x : E, S x = 0 → x = 0 := by
    intro x hx
    have hb := shiftedOperator_lower_bound A z r hsep x
    change r * ‖x‖ ≤ ‖S x‖ at hb
    rw [hx, norm_zero] at hb
    have hn : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp hn
  have hinj : Function.Injective S := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero (x - y)
    rw [map_sub, hxy, sub_self]
  let e : E ≃L[ℂ] E :=
    (LinearEquiv.ofInjectiveEndo S.toLinearMap hinj).toContinuousLinearEquiv
  have he : ∀ x : E, e x = S x := fun _ => rfl
  refine ⟨e.symm.toContinuousLinearMap, ?_, ?_, ?_⟩
  · ext x
    exact (he (e.symm x)).symm.trans (e.apply_symm_apply x)
  · ext x
    change e.symm (S x) = x
    rw [← he, e.symm_apply_apply]
  · apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hr.le)
    intro x
    have hb := shiftedOperator_lower_bound A z r hsep (e.symm x)
    change r * ‖e.symm x‖ ≤ ‖S (e.symm x)‖ at hb
    rw [← he, e.apply_symm_apply] at hb
    simpa [div_eq_inv_mul] using
      (le_div_iff₀ hr).mpr (by simpa [mul_comm] using hb)

end Qatlib.Foundations.OpCalculus.ContourCalc
