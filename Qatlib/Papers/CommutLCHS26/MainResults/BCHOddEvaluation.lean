/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHControlled

/-!
# Evaluation of odd logarithm tails

Under `OddControl`, this module proves convergence of the odd logarithm tail of a symmetric half
step throughout the closed control disk. The logarithm evaluates to its linear generator sum
plus terms of odd degree at least three.

The real time formulation `real_tail_hasSum` supplies the convergent tail identity needed for
the perturbation estimates in [AftabAnTrivisa2026].

## Main statements

* `tail_norm_summable`: proves absolute summability of the odd logarithm tail.
* `evaluate_eq_linear_add_tail`: separates the linear term from the evaluated logarithm.
* `real_tail_hasSum`: identifies the tail sum at real times.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHOddEvaluation

open scoped BigOperators Classical Matrix.Norms.L2Operator NNReal ENNReal
open BCHFormal BCHConvergence BCHControlled BCHHalfBudget
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Under `OddControl`, the norms of the odd logarithm terms of degrees at least three form a
summable sequence throughout the closed control disk. -/
theorem tail_norm_summable (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ)
    (hc : OddControl xs r J) (z : ℂ) (hz : ‖z‖ ≤ r) :
    Summable (fun j : ℕ => ‖z ^ (2 * j + 3) • logCoefficient
      (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0)) (2 * j + 3)‖) := by
  have h := (log_norm_summable_closed xs r J hc z hz).comp_injective
    (show Function.Injective (fun j : ℕ => 2 * j + 3) by
      intro a b h; change 2 * a + 3 = 2 * b + 3 at h; omega)
  simpa only [scaled, logSeries, PowerSeries.coeff_mk] using! h

/-- Under `OddControl`, evaluating the symmetric half step logarithm within the control disk
gives the linear generator sum plus its odd tail starting at degree three. -/
theorem evaluate_eq_linear_add_tail (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ)
    (hc : OddControl xs r J) (z : ℂ) (hz : ‖z‖ ≤ r) :
    evaluate (logSeries (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0))) z =
      z • xs.sum + ∑' j : ℕ, z ^ (2 * j + 3) • logCoefficient
        (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0)) (2 * j + 3) := by
  let d := scaled (logSeries (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0))) z
  have hd : Summable d := (log_norm_summable_closed xs r J hc z hz).of_norm
  have he : Summable (fun j : ℕ => d (2 * j)) :=
    hd.comp_injective (by intro a b h; change 2 * a = 2 * b at h; omega)
  have ho : Summable (fun j : ℕ => d (2 * j + 1)) :=
    hd.comp_injective (by intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega)
  have hzero (j : ℕ) : d (2 * j) = 0 := by
    simp only [d, scaled, logSeries, PowerSeries.coeff_mk,
      frozen_half_log_even xs _ (even_two_mul j), smul_zero]
  have hsplit := tsum_even_add_odd he ho
  simp only [hzero, tsum_zero, zero_add] at hsplit
  change (∑' n, d n) = _
  rw [← hsplit, ho.tsum_eq_zero_add]
  have hfirst : d 1 = z • xs.sum := by
    simp only [d, scaled, logSeries, PowerSeries.coeff_mk, pow_one, frozen_half_log_one]
  rw [show 2 * 0 + 1 = 1 by decide, hfirst]
  congr 1
  apply tsum_congr
  intro j
  dsimp only [d, scaled, logSeries, PowerSeries.coeff_mk]
  rw [show 2 * (j + 1) + 1 = 2 * j + 3 by omega]
  simp only [PowerSeries.coeff_mk]

/-- Under `OddControl`, the odd logarithm tail at a real time within the control radius sums to
the evaluated logarithm minus its linear term. -/
theorem real_tail_hasSum (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ)
    (hc : OddControl xs r J) (t : ℝ) (ht : |t| ≤ r) :
    HasSum (fun j : ℕ => t ^ (2 * j + 3) • logCoefficient
      (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0)) (2 * j + 3))
      (evaluate (logSeries (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0)))
        (t : ℂ) - t • xs.sum) := by
  have ht' : ‖(t : ℂ)‖ ≤ r := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using! ht
  have hs := (tail_norm_summable xs r J hc (t : ℂ) ht').of_norm.hasSum
  have he := evaluate_eq_linear_add_tail xs r J hc (t : ℂ) ht'
  simp only [← Complex.ofReal_pow, Complex.coe_smul] at hs he
  rw [he, add_sub_cancel_left]
  exact hs

end Qatlib.Papers.CommutLCHS26.MainResults.BCHOddEvaluation
