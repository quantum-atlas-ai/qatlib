/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.WordLeakage.ActualLeakage

/-!
# Energy cutoffs for prescribed product-word leakage

This module defines `toleranceCutoff` by solving the exponential leakage estimate for its output
cutoff. It identifies the cutoff increment as a step-growth term plus a logarithmic tolerance
term and proves the desired leakage bound for [HejaziZiniArrazola2024].

## Main statements

* `toleranceCutoff_increment`: Splits the cutoff increment into integrated growth and `log (1 /
  θ)` terms.
* `actual_product_tolerance_cutoff`: Bounds leakage above the chosen cutoff by `θ`.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.WordLeakage
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ProductError
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}

/-- The integrated step exponent is nonnegative for nonnegative interaction strength and time
under the small-step condition. -/
theorem stepExponent_nonneg (L k d : ℕ) (J : ℝ) (hJ : 0 ≤ J) (stages : List (ℝ × Fin M))
    (p : ℕ) (s : ℝ) (hs : 0 ≤ s) (hsmall : 2*J*k*d*timeBudget stages*s < 1) :
    0 ≤ stepExponent L k d J stages p s := by
  have hA := timeBudget_nonneg stages
  have hden : 0 < 1-2*J*k*d*timeBudget stages*s := sub_pos.mpr hsmall
  unfold stepExponent growthCoefficient
  positivity

/-- The output cutoff `Δ + 2 * J * k * d * (stepExponent L k d J stages p s - log θ)` associated
with leakage tolerance `θ`. -/
def toleranceCutoff (L k d : ℕ) (J : ℝ) (stages : List (ℝ × Fin M))
    (p : ℕ) (s Δ θ : ℝ) : ℝ := Δ+2*J*k*d*(stepExponent L k d J stages p s-Real.log θ)

/-- For `0 < θ ≤ 1`, nonnegative interaction strength and time, and the small-step condition,
the tolerance cutoff is at least the input cutoff. -/
theorem toleranceCutoff_ge (L k d : ℕ) (J : ℝ) (hJ : 0 ≤ J) (stages : List (ℝ × Fin M))
    (p : ℕ) (s Δ θ : ℝ) (hs : 0 ≤ s) (hsmall : 2*J*k*d*timeBudget stages*s < 1)
    (hθ : 0 < θ) (hθone : θ ≤ 1) : Δ ≤ toleranceCutoff L k d J stages p s Δ θ := by
  have he := stepExponent_nonneg L k d J hJ stages p s hs hsmall
  have hl : Real.log θ ≤ 0 := Real.log_nonpos hθ.le hθone
  unfold toleranceCutoff
  have hg : 0 ≤ 2*J*k*d*(stepExponent L k d J stages p s-Real.log θ) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (hl.trans he))
  linarith

/-- The tolerance-cutoff increment equals `2 * J * k * d * stepExponent` plus `2 * J * k * d *
log (1 / θ)`. -/
theorem toleranceCutoff_increment (L k d : ℕ) (J : ℝ) (stages : List (ℝ × Fin M))
    (p : ℕ) (s Δ θ : ℝ) :
    toleranceCutoff L k d J stages p s Δ θ-Δ =
      2*J*k*d*stepExponent L k d J stages p s+2*J*k*d*Real.log (1/θ) := by
  simp only [toleranceCutoff, add_sub_cancel_left, one_div, Real.log_inv]
  ring

/-- Under locality, lower-order cancellation, and the small-step condition, leakage above
`toleranceCutoff` from the input low-energy sector is at most any prescribed positive `θ`. -/
theorem actual_product_tolerance_cutoff (h : Hamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (stages : List (ℝ × Fin M))
    (p : ℕ) (hp : 0 < p) (horder : lowerOrderCancellation h stages p)
    (s : ℝ) (hs : 0 ≤ s) (hsmall : 2*J*k*d*timeBudget stages*s < 1) (Δ θ : ℝ) (hθ : 0 < θ) :
    ‖high h.total h.total_hermitian (toleranceCutoff L k d J stages p s Δ θ)*
      approximate h stages s*low h.total h.total_hermitian Δ‖ ≤ θ := by
  have hn : (2*J*k*d : ℝ) ≠ 0 := by positivity
  have he : -(1/(2*J*k*d))*(toleranceCutoff L k d J stages p s Δ θ-Δ)+
      stepExponent L k d J stages p s = Real.log θ := by
    unfold toleranceCutoff
    field_simp
    ring
  simpa only [he, Real.exp_log hθ] using
    actual_product_word_leakage h hJ hk hd L hL stages p hp horder s hs hsmall Δ
      (toleranceCutoff L k d J stages p s Δ θ)
end Qatlib.Papers.LowEnergyProd24.WordLeakage
