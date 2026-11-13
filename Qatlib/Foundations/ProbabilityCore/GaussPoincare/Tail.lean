/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.GaussPoincare.Poincare

/-!
# Centered Gaussian tails from derivative energy

This module combines the π²/8 Gaussian Poincare estimate with Chebyshev's inequality. It bounds
centered deviations of one C¹ observable and the union of deviations of a finite family by their
Gaussian squared-derivative integrals, providing concentration estimates for Gaussian
interpolation applications [GohMuller2026].

## Main statements

* `centered_tail`: A centered deviation has probability at most π²/8 times derivative energy
  divided by ε².
* `finite_centered_tail`: A finite-family deviation is bounded by the sum of the derivative
  energies.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators
namespace Qatlib.Foundations.ProbabilityCore.GaussPoincare.Tail
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- For a C¹ Gaussian square-integrable function with integrable squared derivative norm and `ε
> 0`, the probability of a centered absolute deviation at least `ε` is at most π²/8 times
its derivative energy divided by ε². -/
theorem centered_tail (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (hm : MemLp f 2 (stdGaussian E))
    (hgrad : Integrable (fun x:E=>‖fderiv ℝ f x‖^2) (stdGaussian E))
    (ε : ℝ) (hε : 0<ε) :
    (stdGaussian E).real {x | ε≤|f x-(∫ y,f y ∂stdGaussian E)|} ≤
      (Real.pi^2/8)*(∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E)/ε^2 := by
  have h := meas_ge_le_variance_div_sq hm hε
  have hr := ENNReal.toReal_le_of_le_ofReal
    (div_nonneg (variance_nonneg f (stdGaussian E)) (sq_nonneg ε)) h
  have hp := div_le_div_of_nonneg_right
    (Qatlib.Foundations.ProbabilityCore.GaussPoincare.Poincare.c1_gaussian_poincare_gradient f hf hm hgrad) (sq_nonneg ε)
  exact hr.trans hp

/-- For a finite family of C¹ Gaussian square-integrable functions with integrable squared
derivative norms, the probability that any centered absolute deviation reaches `ε > 0` is at
most π²/(8ε²) times the sum of their derivative energies. -/
theorem finite_centered_tail {J : Type} [Fintype J] (f : J→E→ℝ)
    (hf : ∀ j,ContDiff ℝ 1 (f j)) (hm : ∀ j,MemLp (f j) 2 (stdGaussian E))
    (hgrad : ∀ j,Integrable (fun x:E=>‖fderiv ℝ (f j) x‖^2) (stdGaussian E))
    (ε : ℝ) (hε : 0<ε) :
    (stdGaussian E).real {x | ∃ j,ε≤|f j x-(∫ y,f j y ∂stdGaussian E)|} ≤
      (Real.pi^2/8)/ε^2 * ∑ j,(∫ x,‖fderiv ℝ (f j) x‖^2 ∂stdGaussian E) := by
  have he : {x:E | ∃ j,ε≤|f j x-(∫ y,f j y ∂stdGaussian E)|}=
      ⋃ j:J,{x | ε≤|f j x-(∫ y,f j y ∂stdGaussian E)|} := by ext x;simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ j,(Real.pi^2/8)*(∫ x,‖fderiv ℝ (f j) x‖^2 ∂stdGaussian E)/ε^2 :=
      Finset.sum_le_sum (fun j _=>centered_tail (f j) (hf j) (hm j) (hgrad j) ε hε)
    _ = _ := by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro j _;ring
end Qatlib.Foundations.ProbabilityCore.GaussPoincare.Tail
