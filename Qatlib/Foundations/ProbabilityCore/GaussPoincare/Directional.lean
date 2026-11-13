/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.GaussPoincare.Rotation
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Gaussian directional derivatives along rotations

This module computes second moments of real continuous linear functionals under the standard
Gaussian on a finite-dimensional real inner product space. It combines these moments with
pair-rotation invariance and the fundamental theorem of calculus for C¹ observables, supplying
directional estimates for Gaussian interpolation arguments [GohMuller2026].

## Main statements

* `dual_square_integral`: A linear functional's Gaussian second moment equals its squared
  operator norm.
* `rotated_gradient_square_integral`: Rotated directional energy equals the Gaussian integral of
  the squared derivative norm.
* `rotation_path_integral`: The angular derivative integrates to the endpoint increment.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal
namespace Qatlib.Foundations.ProbabilityCore.GaussPoincare.Directional
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The second moment of a real continuous linear functional under the standard Gaussian is the
square of its operator norm. -/
theorem dual_square_integral (L : E→L[ℝ]ℝ) :
    (∫ y,(L y)^2 ∂stdGaussian E)=‖L‖^2 := by
  have hm : (∫ y,L y ∂stdGaussian E)=0 := by
    simpa only [id_eq,integral_id_stdGaussian,map_zero] using
      L.integral_comp_comm (IsGaussian.integrable_id (μ:=stdGaussian E))
  have hl : MemLp L 2 (stdGaussian E) := L.lipschitz.comp_memLp (map_zero L)
    (IsGaussian.memLp_id (stdGaussian E) 2 (by simp))
  have h := variance_eq_sub hl
  rw [variance_dual_stdGaussian,hm] at h
  simpa only [zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,Pi.pow_apply] using h.symm

/-- For a C¹ function that is `L`-Lipschitz, the squared derivative evaluated on an independent
Gaussian direction is integrable under the Gaussian product measure. -/
theorem gradient_pair_integrable (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hLip : LipschitzWith L f) :
    Integrable (fun z:E×E => ((fderiv ℝ f z.1) z.2)^2)
      ((stdGaussian E).prod (stdGaussian E)) := by
  have hn : Integrable (fun y:E=>‖y‖^2) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) 2 (by simp)).integrable_norm_pow'
  have hd :=
      ((measurePreserving_snd (μ:=stdGaussian E) (ν:=stdGaussian E)).integrable_comp_of_integrable hn).const_mul ((L:ℝ)^2)
  apply hd.mono' ((hf.continuous_fderiv_apply (by norm_num)).pow 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hb : |(fderiv ℝ f z.1) z.2|≤(L:ℝ)*‖z.2‖ := by
    calc
      _ ≤ ‖fderiv ℝ f z.1‖*‖z.2‖ := (fderiv ℝ f z.1).le_opNorm z.2
      _ ≤ _ := mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg _)
  have := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.mpr hb
  simpa only [sq_abs,mul_pow,Function.comp_apply] using! this

/-- For a C¹ function that is `L`-Lipschitz, the Gaussian pair integral of the rotated squared
directional derivative equals the Gaussian integral of the squared derivative norm. -/
theorem rotated_gradient_square_integral (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hLip : LipschitzWith L f) (θ : ℝ) :
    (∫ z:E×E,((fderiv ℝ f (ContinuousLinearMap.rotation θ z).1)
      (ContinuousLinearMap.rotation θ z).2)^2 ∂((stdGaussian E).prod (stdGaussian E))) =
      ∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E := by
  rw [Qatlib.Foundations.ProbabilityCore.GaussPoincare.Rotation.rotation_integral θ (fun z:E×E=>((fderiv ℝ f z.1) z.2)^2)
    (gradient_pair_integrable f hf L hLip).aestronglyMeasurable]
  rw [integral_prod _ (gradient_pair_integrable f hf L hLip)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x=>dual_square_integral (fderiv ℝ f x)

/-- For a C¹ function that is `L`-Lipschitz, the Gaussian pair integral of the rotated squared
directional derivative is at most `L ^ 2`. -/
theorem rotated_gradient_square_le (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hLip : LipschitzWith L f) (θ : ℝ) :
    (∫ z:E×E,((fderiv ℝ f (ContinuousLinearMap.rotation θ z).1)
      (ContinuousLinearMap.rotation θ z).2)^2 ∂((stdGaussian E).prod (stdGaussian E))) ≤ (L:ℝ)^2 := by
  rw [rotated_gradient_square_integral f hf L hLip θ]
  have hb : ∀ x:E,‖‖fderiv ℝ f x‖^2‖≤(L:ℝ)^2 := by
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) L.coe_nonneg).mpr (norm_fderiv_le_of_lipschitz ℝ hLip)
  have h := norm_integral_le_of_norm_le_const (μ:=stdGaussian E) (Filter.Eventually.of_forall hb)
  simp only [probReal_univ,mul_one,Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

/-- For a C¹ observable, integrating the derivative along the quarter-circle rotation path gives
`f z.2 - f z.1`. -/
theorem rotation_path_integral (f : E→ℝ) (hf : ContDiff ℝ 1 f) (z : E×E) :
    (∫ θ in (0:ℝ)..Real.pi/2, (fderiv ℝ f (ContinuousLinearMap.rotation θ z).1)
      (ContinuousLinearMap.rotation θ z).2)=f z.2-f z.1 := by
  have hc : Continuous (fun θ:ℝ=>(fderiv ℝ f (ContinuousLinearMap.rotation θ z).1)
      (ContinuousLinearMap.rotation θ z).2) := by
    apply (hf.continuous_fderiv_apply (by norm_num)).comp
    simp only [ContinuousLinearMap.rotation_apply]
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=Real.pi/2)
    (fun θ _=>Qatlib.Foundations.ProbabilityCore.GaussPoincare.Rotation.observable_rotation_deriv f z θ ((hf.differentiable (by norm_num)).differentiableAt))
    (hc.intervalIntegrable 0 (Real.pi/2))
  simpa only [ContinuousLinearMap.rotation_apply,Real.cos_pi_div_two,Real.sin_pi_div_two,
    Real.cos_zero,Real.sin_zero,zero_smul,one_smul,add_zero,zero_add] using h
end Qatlib.Foundations.ProbabilityCore.GaussPoincare.Directional
