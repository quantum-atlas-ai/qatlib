/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.WordLeakage.ActualLeakage
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Source majorants for product-word leakage

This module defines `sourceRate` and `sourceStepExponent` in the parameterization used for the
leakage analysis of [HejaziZiniArrazola2024]. It compares the direct rate and integrated
exponent with these majorants and derives the corresponding product-word leakage estimate.

## Main statements

* `actual_exponent_le_source`: Bounds the direct step exponent by the source exponent.
* `actual_source_majorant_leakage`: Gives leakage control with `sourceStepExponent`.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.WordLeakage
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ProductError
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}

/-- The source majorant rate `exp 1 * J * k * d * (M + timeBudget stages)`. -/
def sourceRate (k d : ℕ) (J : ℝ) (stages : List (ℝ × Fin M)) : ℝ :=
  Real.exp 1*J*k*d*((M : ℝ)+timeBudget stages)

/-- The source integrated exponent `L * exp 1 * J * timeBudget stages * s * (sourceRate * s) ^ p
/ ((p + 1) * (1 - sourceRate * s))`. -/
def sourceStepExponent (L k d : ℕ) (J : ℝ) (stages : List (ℝ × Fin M)) (p : ℕ) (s : ℝ) : ℝ :=
  ((L : ℝ)*Real.exp 1*J*timeBudget stages)*s*(sourceRate k d J stages*s)^p /
    ((p+1)*(1-sourceRate k d J stages*s))

/-- For nonnegative interaction strength, the direct rate `2 * J * k * d * timeBudget stages` is
at most `sourceRate`. -/
theorem actual_rate_le_source (k d : ℕ) (J : ℝ) (hJ : 0 ≤ J) (stages : List (ℝ × Fin M)) :
    2*J*k*d*timeBudget stages ≤ sourceRate k d J stages := by
  have hA := timeBudget_nonneg stages
  unfold sourceRate
  gcongr
  · exact Real.exp_one_gt_two.le
  · exact le_add_of_nonneg_left (Nat.cast_nonneg M)
/-- For a nonnegative step with `sourceRate * s < 1`, the direct step exponent is at most
`sourceStepExponent`. -/
theorem actual_exponent_le_source (L k d : ℕ) (J : ℝ) (hJ : 0 ≤ J)
    (stages : List (ℝ × Fin M)) (p : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hsmall : sourceRate k d J stages*s < 1) :
    stepExponent L k d J stages p s ≤ sourceStepExponent L k d J stages p s := by
  have hA := timeBudget_nonneg stages
  have hrate := actual_rate_le_source k d J hJ stages
  have hsmall' : 2*J*k*d*timeBudget stages*s < 1 :=
    (mul_le_mul_of_nonneg_right hrate hs).trans_lt hsmall
  have hden : 0 < 1-sourceRate k d J stages*s := sub_pos.mpr hsmall
  have hden' : 0 < 1-2*J*k*d*timeBudget stages*s := sub_pos.mpr hsmall'
  have hsrc : 0 ≤ sourceRate k d J stages := by unfold sourceRate; positivity
  have he : stepExponent L k d J stages p s =
      ((L : ℝ)*(2*J)*timeBudget stages)*s*(2*J*k*d*timeBudget stages*s)^p /
        ((p+1)*(1-2*J*k*d*timeBudget stages*s)) := by
    unfold stepExponent growthCoefficient
    rw [mul_pow, pow_succ]
    field_simp
    ring
  rw [he]
  unfold sourceStepExponent
  have hD : (L : ℝ)*(2*J)*timeBudget stages ≤ (L : ℝ)*Real.exp 1*J*timeBudget stages := by
    calc
      _ = (L : ℝ)*2*J*timeBudget stages := by ring
      _ ≤ _ := by gcongr; exact Real.exp_one_gt_two.le
  have hnum : ((L : ℝ)*(2*J)*timeBudget stages)*s*(2*J*k*d*timeBudget stages*s)^p ≤
      ((L : ℝ)*Real.exp 1*J*timeBudget stages)*s*(sourceRate k d J stages*s)^p := by
    gcongr
  exact div_le_div₀ (by positivity) hnum (by positivity) (by gcongr)

/-- Under locality, cancellation, and the source small-step condition, product-word leakage is
bounded by `exp (-(Λ - Δ) / (2 * J * k * d) + sourceStepExponent L k d J stages p s)`. -/
theorem actual_source_majorant_leakage (h : Hamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (stages : List (ℝ × Fin M))
    (p : ℕ) (hp : 0 < p) (horder : lowerOrderCancellation h stages p)
    (s : ℝ) (hs : 0 ≤ s) (hsmall : sourceRate k d J stages*s < 1) (Δ Λ : ℝ) :
    ‖high h.total h.total_hermitian Λ*approximate h stages s*low h.total h.total_hermitian Δ‖ ≤
      Real.exp (-(1/(2*J*k*d))*(Λ-Δ)+sourceStepExponent L k d J stages p s) := by
  have hsmall' :=
      (mul_le_mul_of_nonneg_right (actual_rate_le_source k d J hJ.le stages) hs).trans_lt hsmall
  exact (actual_product_word_leakage h hJ hk hd L hL stages p hp horder s hs hsmall' Δ Λ).trans
    (Real.exp_le_exp.mpr (add_le_add le_rfl (actual_exponent_le_source L k d J hJ.le stages p s hs hsmall)))
end Qatlib.Papers.LowEnergyProd24.WordLeakage
