/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.PolynomialPanelGauss

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc


/-! A scalar-only envelope for the actual local matrix polynomial. The
coordinate L1 bound can be evaluated in rational arithmetic when the scalar
input is Gaussian rational; no unknown matrix entries enter this envelope. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib Polynomial
open scoped BigOperators Matrix.Norms.L2Operator

/-- Construction for polynomial Panel Scalar Coefficient in the polynomial coefficient envelope model. -/
def polynomialPanelScalarCoefficient (p : Polynomial ℂ) (z₀ u : ℂ)
    (a h : ℝ) (n j : ℕ) : ℂ :=
  let tc := a + h / 2
  let q := p.comp (C (z₀ - (tc : ℂ)*u) + C u*X)
  let v := C (-u)*(X-C (tc : ℂ))
  (q*v^n).coeff j

/-- Construction for polynomial Panel Coefficient Envelope in the polynomial coefficient envelope model. -/
def polynomialPanelCoefficientEnvelope (p : Polynomial ℂ) (z₀ u : ℂ)
    (a h r : ℝ) (d m : ℕ) : ℝ :=
  ∑ j : Fin (d+m+1), ∑ n ∈ Finset.range (m+1),
    (|(polynomialPanelScalarCoefficient p z₀ u a h n j).re| +
      |(polynomialPanelScalarCoefficient p z₀ u a h n j).im|) * (r⁻¹)^(n+1)

/-- The exposed coefficient array is the same literal one used in the
existing polynomial-times-resolvent expansion. -/
theorem polynomialLocalCoefficients_eq
    {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (z₀ u : ℂ) (a h : ℝ) (d m : ℕ)
    (j : Fin (d+m+1)) :
    polynomialLocalCoefficients A p z₀ u a h d m j =
      ∑ n ∈ Finset.range (m+1), polynomialPanelScalarCoefficient p z₀ u a h n j •
        (matrixResolvent A z₀)^(n+1) := rfl

/-- Actual numerical-range separation at the midpoint bounds the matrix
coefficients by known scalar polynomial arithmetic, before any matrix is
used to choose the moment precision. No final vector-error bound is assumed. -/
theorem polynomialLocalCoefficients_norm_sum_le
    {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (z₀ u : ℂ) (a h r : ℝ) (d m : ℕ)
    (hr : 0 < r) (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z₀-w‖) :
    (∑ j, ‖polynomialLocalCoefficients A p z₀ u a h d m j‖) ≤
      polynomialPanelCoefficientEnvelope p z₀ u a h r d m := by
  have hR := (matrixResolvent_inverse_norm_of_separation A z₀ r hr hsep).2.2
  unfold polynomialPanelCoefficientEnvelope
  apply Finset.sum_le_sum
  intro j _
  rw [polynomialLocalCoefficients_eq]
  calc
    _ ≤ ∑ n ∈ Finset.range (m+1),
        ‖polynomialPanelScalarCoefficient p z₀ u a h n j •
          (matrixResolvent A z₀)^(n+1)‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun n _ => by
      rw [norm_smul]
      apply mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        ((norm_pow_le' _ (Nat.succ_pos n)).trans
          (pow_le_pow_left₀ (norm_nonneg _) hR _))
        (norm_nonneg _) (by positivity))

end Qatlib.Concepts.MatrixContour.ContourCalc
