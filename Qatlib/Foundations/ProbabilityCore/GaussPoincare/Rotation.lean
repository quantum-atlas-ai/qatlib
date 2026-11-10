/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Probability.Independence.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Qatlib.Foundations.ProbabilityCore.GaussPoincare.Rotation
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem rotation_preserving (θ : ℝ) :
    MeasurePreserving (ContinuousLinearMap.rotation θ : E×E→L[ℝ] E×E)
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) := by
  exact ⟨by fun_prop, IsGaussian.map_rotation_eq_self (integral_id_stdGaussian (E:=E)) θ⟩
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem rotation_position_deriv (z : E×E) (θ : ℝ) :
    HasDerivAt (fun a : ℝ => (ContinuousLinearMap.rotation a z).1)
      (ContinuousLinearMap.rotation θ z).2 θ := by
  simpa only [ContinuousLinearMap.rotation_apply] using!
    ((Real.hasDerivAt_cos θ).smul_const z.1).add ((Real.hasDerivAt_sin θ).smul_const z.2)
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem observable_rotation_deriv (f : E→ℝ) (z : E×E) (θ : ℝ)
    (hf : DifferentiableAt ℝ f (ContinuousLinearMap.rotation θ z).1) :
    HasDerivAt (fun a : ℝ => f (ContinuousLinearMap.rotation a z).1)
      ((fderiv ℝ f (ContinuousLinearMap.rotation θ z).1)
        (ContinuousLinearMap.rotation θ z).2) θ := by
  exact hf.hasFDerivAt.comp_hasDerivAt θ (rotation_position_deriv z θ)

theorem rotation_integral (θ : ℝ) (g : E×E→ℝ) (hg : AEStronglyMeasurable g
    ((stdGaussian E).prod (stdGaussian E))) :
    (∫ z, g (ContinuousLinearMap.rotation θ z) ∂((stdGaussian E).prod (stdGaussian E))) =
      ∫ z, g z ∂((stdGaussian E).prod (stdGaussian E)) := by
  have h := rotation_preserving (E:=E) θ
  calc
    _ = ∫ z, g z ∂Measure.map (ContinuousLinearMap.rotation θ)
        ((stdGaussian E).prod (stdGaussian E)) :=
      (integral_map h.measurable.aemeasurable (by simpa only [h.map_eq] using hg)).symm
    _ = _ := by rw [h.map_eq]
end Qatlib.Foundations.ProbabilityCore.GaussPoincare.Rotation
