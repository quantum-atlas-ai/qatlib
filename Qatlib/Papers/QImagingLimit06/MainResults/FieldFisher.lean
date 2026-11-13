/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QImagingLimit06.MainResults.FisherCore
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Gaussian field Fisher information and resolution

`gaussPixelFisher` models the Fisher expression for pixel derivatives with common Gaussian
noise. Substituting the field derivative scale gives Fisher information `4N / (b²σ²)` and the
associated conditional Cramér–Rao resolution bound. See [DelaubertEtAl2008] for the paper
context.

## Main statements

* `gauss_field_fisher_value`: Under the derivative scale identity for positive `b`, the Gaussian
  field Fisher expression equals `4 * N / (b² * σ²)`.
* `gauss_field_quantum_limit`: For positive `N`, `b`, and `σ`, if the Fisher information equals
  `4N / (b²σ²)` and variance satisfies its reciprocal bound, then the resolution is at least `bσ
  / (2√N)`.

## References

* [Delaubert et al., 2008][DelaubertEtAl2008]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QImagingLimit06.MainResults

/-- The sum of squared pixel derivatives divided by the common Gaussian variance `σ²`. -/
def gaussPixelFisher {ι : Type} [Fintype ι] (σ : ℝ) (dP : ι → ℝ) : ℝ :=
  (1 / σ ^ 2) * ∑ k, (dP k) ^ 2

/-- Under the derivative scale identity for positive `b`, the Gaussian field Fisher expression
equals `4 * N / (b² * σ²)`. See [DelaubertEtAl2008]. -/
theorem gauss_field_fisher_value {ι : Type} [Fintype ι] {N b σ : ℝ}
    (hN : 0 < N) (hb : 0 < b) (hσ : 0 < σ) (du : ι → ℝ)
    (hb_def : 1 / b ^ 2 = ∑ k, du k ^ 2) :
    gaussPixelFisher σ (fun k => 2 * Real.sqrt N * du k) =
      4 * N / (b ^ 2 * σ ^ 2) := by
  unfold gaussPixelFisher
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt (le_of_lt hN)
  have hsum : ∑ k, (2 * Real.sqrt N * du k) ^ 2 = 4 * N * ∑ k, du k ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [mul_pow, mul_pow, hsq]; ring
  rw [hsum, ← hb_def]
  have hb0 : b ≠ 0 := hb.ne'
  have hσ0 : σ ≠ 0 := hσ.ne'
  field_simp

/-- For positive `N`, `b`, and `σ`, if the Fisher information equals `4N / (b²σ²)` and variance
satisfies its reciprocal bound, then the resolution is at least `bσ / (2√N)`. See
[DelaubertEtAl2008]. -/
theorem gauss_field_quantum_limit {N b σ Var pmin : ℝ} (hN : 0 < N)
    (hb : 0 < b) (hσ : 0 < σ) (IF : ℝ) (hIF : IF = 4 * N / (b ^ 2 * σ ^ 2))
    (hVar : 1 / IF ≤ Var) (hpmin : pmin = Real.sqrt Var) :
    b * σ / (2 * Real.sqrt N) ≤ pmin := by
  have hIFpos : 0 < IF := by rw [hIF]; positivity
  have hbnd := cramerRao_bound hIFpos hVar hpmin
  rwa [hIF, resolution_gauss_fisher hN hb hσ] at hbnd

end Qatlib.Papers.QImagingLimit06.MainResults
