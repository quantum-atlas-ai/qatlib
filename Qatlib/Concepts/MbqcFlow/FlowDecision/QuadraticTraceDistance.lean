/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.DiagonalTraceDistance
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Mathlib.Tactic.Linarith

/-!
# Quadratic forms controlled by trace distance

Relates `trace (outerProduct z * X)` to the quadratic form of `X` at `z`. For trace-zero
matrices, it bounds the absolute real part of this form by half the trace norm when `z` is
normalized, and by the same bound multiplied by the vector's squared mass in general.

These estimates express the control of measurement expectations by trace distance; see
[Watrous2018].

## Main statements

* `abs_quadratic_re_le_half_traceNorm`: the normalized-vector bound.
* `abs_quadratic_re_le_mass_half_traceNorm`: the bound for arbitrary vectors.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
open Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MbqcFlow.FlowDecision
open Matrix

/-- The trace of `outerProduct z * X` equals the quadratic form `star z ⬝ᵥ X *ᵥ z`. -/
theorem trace_outerProduct_mul_eq_quadratic
    {I : Type*} [Fintype I] [DecidableEq I] (z : QState I) (X : Matrix I I ℂ) :
    (outerProduct z * X).trace = star z ⬝ᵥ X *ᵥ z := by
  classical
  simp only [Matrix.trace, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change z i*star (z j)*X j i = star (z j)*(X j i*z i)
  ring

/-- For a trace-zero matrix and a normalized vector, the absolute real part of the quadratic
form is at most half the matrix trace norm. -/
theorem abs_quadratic_re_le_half_traceNorm
    {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ)
    (htrace : X.trace = 0) (z : QState I) (hz : Normalized z) :
    |(star z ⬝ᵥ X *ᵥ z).re| ≤ (1/2 : ℝ)*X.traceNorm := by
  classical
  let U := ReflectionAbout (outerProduct z)
  have hu : U.Isometry := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using!
      outerProduct_reflection_unitary hz
  have ht : (U*X).trace = 2*(outerProduct z*X).trace := by
    simp only [U, ReflectionAbout, sub_mul, smul_mul_assoc, one_mul,
      Matrix.trace_sub, Matrix.trace_smul, htrace, sub_zero]
    rfl
  have hb := Matrix.abs_trace_le_traceNorm (U*X)
  rw [Matrix.traceNorm_isometry_left (by convert! hu using 1), ht, norm_mul] at hb
  norm_num at hb
  rw [← trace_outerProduct_mul_eq_quadratic]
  have hr := Complex.abs_re_le_norm ((outerProduct z*X).trace)
  linarith

/-- For a trace-zero matrix and an arbitrary vector, the absolute real quadratic form is bounded
by the vector's squared mass times half the trace norm. -/
theorem abs_quadratic_re_le_mass_half_traceNorm
    {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ)
    (htrace : X.trace = 0) (z : QState I) :
    |(star z ⬝ᵥ X *ᵥ z).re| ≤ (∑ i, ‖z i‖^2)*((1/2 : ℝ)*X.traceNorm) := by
  classical
  let m : ℝ := ∑ i, ‖z i‖^2
  have hm0 : 0 ≤ m := Finset.sum_nonneg (fun i _ => sq_nonneg ‖z i‖)
  by_cases hm : m = 0
  · have hz : z = 0 := by
      funext i
      have hi : ‖z i‖^2 ≤ m := Finset.single_le_sum
        (fun j _ => sq_nonneg ‖z j‖) (Finset.mem_univ i)
      have hni : ‖z i‖ = 0 := by nlinarith [norm_nonneg (z i)]
      exact norm_eq_zero.mp hni
    simp [hz]
  have hmp : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm)
  let c : ℝ := (Real.sqrt m)⁻¹
  let w : QState I := (c : ℂ) • z
  have hc : c^2 = m⁻¹ := by dsimp [c]; rw [inv_pow, Real.sq_sqrt hm0]
  have hw : Normalized w := by
    unfold Normalized
    simp only [w, Pi.smul_apply, norm_smul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, ← Finset.mul_sum]
    change c^2*m = 1
    rw [hc, inv_mul_cancel₀ hm]
  have hscale : star w ⬝ᵥ X *ᵥ w = ((m⁻¹ : ℝ) : ℂ)*(star z ⬝ᵥ X *ᵥ z) := by
    simp only [w, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    have hc' : (c : ℂ)*(c : ℂ) = ((m⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast (show c*c=m⁻¹ by nlinarith [hc])
    rw [← mul_assoc, hc']
  have hb := abs_quadratic_re_le_half_traceNorm X htrace w hw
  rw [hscale] at hb
  have hb' : m⁻¹*|(star z ⬝ᵥ X *ᵥ z).re| ≤ (1/2 : ℝ)*X.traceNorm := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, abs_mul, abs_of_pos (inv_pos.mpr hmp)] using hb
  change _ ≤ m*((1/2 : ℝ)*X.traceNorm)
  calc
    _ = m*(m⁻¹*|(star z ⬝ᵥ X *ᵥ z).re|) := by rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb' hm0

end Qatlib.Concepts.MbqcFlow.FlowDecision
