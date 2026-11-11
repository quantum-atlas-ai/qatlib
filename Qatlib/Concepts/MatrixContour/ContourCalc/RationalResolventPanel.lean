/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.PolynomialCoefficientEnvelope
import Qatlib.Foundations.OpCalculus.ContourCalc.RationalMomentCertificate

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc


/-! An actual rational moment receipt controls the literal polynomial times
canonical resolvent. The coefficient envelope is scalar-only. This uses
the normalized real panel [-1,1]; the contour dz factor is its direction. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib Polynomial MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator

/-- Typeclass instance for moment Panel ENormed Add Monoid in the rational resolvent panel model. -/
noncomputable local instance momentPanelENormedAddMonoid {I : Type} [Fintype I] [DecidableEq I] :
    ENormedAddMonoid (Matrix I I ℂ) := NormedAddGroup.toENormedAddMonoid

/-- The identity or estimate `rational_polynomial_resolvent_panel` holds with the displayed separation, geometry and norm hypotheses. -/
theorem rational_polynomial_resolvent_panel
    {I : Type} [Fintype I] [DecidableEq I]
    (Q d m : ℕ) (node weight : Fin Q → ℚ) (η : ℚ)
    (hc : rationalPositiveMomentCheck Q (d+m) node weight η = true)
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (z₀ v : ℂ) (r M : ℝ)
    (hr : 0 < r) (hv : ‖v‖ ≤ r/8) (hp : p.natDegree ≤ d) (hM : 0 ≤ M)
    (hsep : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ w ∈ matrixNumericalRange A,
      r ≤ ‖contourPanel z₀ v (-1) 2 t-w‖)
    (hpbound : ∀ t ∈ Icc (-1 : ℝ) 1, ‖p.eval (contourPanel z₀ v (-1) 2 t)‖ ≤ M) :
    ‖(∫ t in (-1 : ℝ)..1, p.eval (contourPanel z₀ v (-1) 2 t) •
        matrixResolvent A (contourPanel z₀ v (-1) 2 t)) -
      ∑ q, (weight q : ℝ) • (p.eval (contourPanel z₀ v (-1) 2 (node q : ℝ)) •
        matrixResolvent A (contourPanel z₀ v (-1) 2 (node q : ℝ)))‖ ≤
      (2+∑ q, (weight q : ℝ))*(M*r⁻¹*(1/8 : ℝ)^(m+1)) +
        polynomialPanelCoefficientEnvelope p z₀ v (-1) 2 r d m * (η : ℝ) := by
  let z : ℝ → ℂ := contourPanel z₀ v (-1) 2
  let c := polynomialLocalCoefficients A p z₀ v (-1) 2 d m
  let f : ℝ → Matrix I I ℂ := fun t => p.eval (z t) • matrixResolvent A (z t)
  have hsep₀ : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z₀-w‖ := by
    intro w hw
    have hs := hsep 0 (by constructor <;> norm_num) w hw
    simpa [contourPanel] using hs
  have hnear (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : ‖z t-z₀‖ ≤ r/8 := by
    have ht' : |t| ≤ 1 := abs_le.mpr ht
    simp only [z, contourPanel]
    norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel,
      sub_zero, add_sub_cancel_left]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact ((mul_le_mul_of_nonneg_right ht' (norm_nonneg v)).trans_eq (one_mul _)).trans hv
  have hz := contourPanel_continuous z₀ v (-1) 2
  have hRcont : ContinuousOn (fun t => matrixResolvent A (z t)) (Icc (-1 : ℝ) 1) :=
    (matrixResolvent_continuousOn_of_separation A r hr).comp' hz.continuousOn
      (fun t ht => hsep t ht)
  have hpcont : Continuous (fun t => p.eval (z t)) := p.continuous.comp hz
  have hfcont : ContinuousOn f (Icc (-1 : ℝ) 1) := hpcont.continuousOn.smul hRcont
  have hf : IntervalIntegrable f volume (-1) 1 :=
    _root_.ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hfcont
  have hC := polynomialLocalCoefficients_norm_sum_le A p z₀ v (-1) 2 r d m hr hsep₀
  have happrox (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      ‖f t - finiteVectorPolynomial (d+m) c t‖ ≤ M*r⁻¹*(1/8 : ℝ)^(m+1) := by
    have he := (local_resolvent_approximation A z₀ (z t) r m hr hsep₀
      (hsep t ht) (hnear t ht)).2
    rw [polynomial_local_resolvent_coefficients_explicit A p z₀ v (-1) 2 d m hp]
    change ‖p.eval (z t) • matrixResolvent A (z t) -
      p.eval (z t) • localResolventPolynomial A z₀ m (z t)‖ ≤ _
    rw [← smul_sub, norm_smul]
    exact (mul_le_mul (hpbound t ht) he (norm_nonneg _) hM).trans_eq (by ring)
  exact rational_positive_rule_error Q (d+m) node weight η hc c f
    (M*r⁻¹*(1/8 : ℝ)^(m+1))
    (polynomialPanelCoefficientEnvelope p z₀ v (-1) 2 r d m) hf hC happrox

end Qatlib.Concepts.MatrixContour.ContourCalc
