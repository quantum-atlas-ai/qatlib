/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.Sqrt

/-!
# Euclidean distance and basis-measurement distributions

This module compares the Euclidean distance `euclidDist` between finite quantum states with the
full sum `bornL1Dist` of absolute differences between their computational-basis Born
probabilities. For normalized states, `bornL1Dist_le_two_euclid` proves a factor-two bound using
a pointwise difference-of-squares estimate and Cauchy–Schwarz.

`theorem31_source` recovers the factor-four statement of Theorem 3.1 quoted from
Bernstein–Vazirani in [BennettEtAl1997]. Here `bornL1Dist` is the full L1 sum, matching the
quantity called total variation in that source statement.

## Main statements

* `abs_born_sub_born_le` bounds one Born-probability difference by the amplitude difference
  times the sum of amplitude norms.
* `bornL1Dist_le_two_euclid` bounds the L1 distance by twice the Euclidean distance for
  normalized states.
* `theorem31_source` gives the source-form conclusion `bornL1Dist ψ φ ≤ 4 * ε` when `euclidDist
  ψ φ ≤ ε`.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWeakness97.MainResults

open Qatlib.Foundations.PureStateMath
open scoped BigOperators

variable {I : Type} [Fintype I]

/-- The Euclidean distance between two finite amplitude vectors, defined as the square root of
the sum of squared coordinate differences. -/
def euclidDist (ψ φ : QState I) : ℝ :=
  Real.sqrt (∑ i, ‖ψ i - φ i‖ ^ 2)

/-- The full L1 distance between the states' computational-basis Born probabilities, defined as
the sum of their absolute coordinatewise differences. -/
def bornL1Dist (ψ φ : QState I) : ℝ :=
  ∑ i, |BornProb ψ i - BornProb φ i|

/-- The L1 distance between the computational-basis Born probabilities is nonnegative. -/
theorem bornL1Dist_nonneg (ψ φ : QState I) : 0 ≤ bornL1Dist ψ φ :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The Euclidean distance between finite amplitude vectors is nonnegative. -/
theorem euclidDist_nonneg (ψ φ : QState I) : 0 ≤ euclidDist ψ φ :=
  Real.sqrt_nonneg _

/-- The absolute difference of the squared norms of two complex amplitudes is at most the norm
of their difference multiplied by the sum of their norms. -/
theorem abs_born_sub_born_le (a b : ℂ) :
    |BornProb (fun _ : Unit => a) () - BornProb (fun _ : Unit => b) ()| ≤
      ‖a - b‖ * (‖a‖ + ‖b‖) := by
  have h1 : |‖a‖ - ‖b‖| ≤ ‖a - b‖ := abs_norm_sub_norm_le a b
  have h2 : ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) := by ring
  have h3 : BornProb (fun _ : Unit => a) () - BornProb (fun _ : Unit => b) ()
      = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) := by
    unfold BornProb
    simpa using h2
  rw [h3, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖a‖ + ‖b‖)]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- The L1 distance of Born probabilities is bounded by the sum of coordinatewise amplitude
differences weighted by the sums of amplitude norms. This is the pointwise-estimate step
toward Theorem 3.1 of [BennettEtAl1997]. -/
theorem bornL1Dist_le_weighted (ψ φ : QState I) :
    bornL1Dist ψ φ ≤ ∑ i, ‖ψ i - φ i‖ * (‖ψ i‖ + ‖φ i‖) := by
  unfold bornL1Dist BornProb
  exact Finset.sum_le_sum fun i _ => by
    have := abs_born_sub_born_le (ψ i) (φ i)
    simpa using! this

/-- Cauchy–Schwarz bounds the weighted amplitude-difference sum by the product of the Euclidean
norm of the difference and the square root of the sum of squared coordinatewise norm sums. -/
theorem weighted_sum_le_cauchy (ψ φ : QState I) :
    (∑ i, ‖ψ i - φ i‖ * (‖ψ i‖ + ‖φ i‖)) ≤
      Real.sqrt (∑ i, ‖ψ i - φ i‖ ^ 2) *
        Real.sqrt (∑ i, (‖ψ i‖ + ‖φ i‖) ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
    (fun i => ‖ψ i - φ i‖) (fun i => ‖ψ i‖ + ‖φ i‖)
  have hf : 0 ≤ ∑ i, ‖ψ i - φ i‖ * (‖ψ i‖ + ‖φ i‖) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (by positivity)
  have hs : 0 ≤ ∑ i, ‖ψ i - φ i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hg : 0 ≤ ∑ i, (‖ψ i‖ + ‖φ i‖) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hstep : (∑ i, ‖ψ i - φ i‖ * (‖ψ i‖ + ‖φ i‖)) ^ 2 ≤
      (∑ i, ‖ψ i - φ i‖ ^ 2) * ∑ i, (‖ψ i‖ + ‖φ i‖) ^ 2 := hcs
  have hsqrt := Real.sqrt_le_sqrt hstep
  rwa [Real.sqrt_sq hf, Real.sqrt_mul hs] at hsqrt

/-- For two normalized states, the sum of the squares of their coordinatewise amplitude-norm
sums is at most four. -/
theorem norm_sum_sq_le_four (ψ φ : QState I)
    (hψ : Normalized ψ) (hφ : Normalized φ) :
    (∑ i, (‖ψ i‖ + ‖φ i‖) ^ 2) ≤ 4 := by
  have hsplit : ∀ i : I, (‖ψ i‖ + ‖φ i‖) ^ 2 ≤ 2 * ‖ψ i‖ ^ 2 + 2 * ‖φ i‖ ^ 2 := by
    intro i
    nlinarith [sq_nonneg (‖ψ i‖ - ‖φ i‖)]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hsplit i)
  rw [Finset.sum_add_distrib] at hsum
  have h2 : (∑ i, 2 * ‖ψ i‖ ^ 2) = 2 * ∑ i, ‖ψ i‖ ^ 2 := by
    rw [Finset.mul_sum]
  have h3 : (∑ i, 2 * ‖φ i‖ ^ 2) = 2 * ∑ i, ‖φ i‖ ^ 2 := by
    rw [Finset.mul_sum]
  rw [h2, h3] at hsum
  have hψ' : (∑ i, ‖ψ i‖ ^ 2) = 1 := hψ
  have hφ' : (∑ i, ‖φ i‖ ^ 2) = 1 := hφ
  rw [hψ', hφ'] at hsum
  norm_num at hsum ⊢
  exact hsum

/-- For normalized states, the full L1 distance between their computational-basis Born
distributions is at most twice their Euclidean distance. This strengthens the factor-four
estimate stated in Theorem 3.1 of [BennettEtAl1997]. -/
theorem bornL1Dist_le_two_euclid (ψ φ : QState I)
    (hψ : Normalized ψ) (hφ : Normalized φ) :
    bornL1Dist ψ φ ≤ 2 * euclidDist ψ φ := by
  have h1 := bornL1Dist_le_weighted ψ φ
  have h2 := weighted_sum_le_cauchy ψ φ
  have h3 := norm_sum_sq_le_four ψ φ hψ hφ
  have hsq_nonneg : 0 ≤ ∑ i, (‖ψ i‖ + ‖φ i‖) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsqrt_le : Real.sqrt (∑ i, (‖ψ i‖ + ‖φ i‖) ^ 2) ≤ 2 := by
    have := Real.sqrt_le_sqrt h3
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h4] at this
  have hnon : 0 ≤ Real.sqrt (∑ i, ‖ψ i - φ i‖ ^ 2) := Real.sqrt_nonneg _
  calc bornL1Dist ψ φ
      ≤ ∑ i, ‖ψ i - φ i‖ * (‖ψ i‖ + ‖φ i‖) := h1
    _ ≤ Real.sqrt (∑ i, ‖ψ i - φ i‖ ^ 2) *
          Real.sqrt (∑ i, (‖ψ i‖ + ‖φ i‖) ^ 2) := h2
    _ ≤ Real.sqrt (∑ i, ‖ψ i - φ i‖ ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left hsqrt_le hnon
    _ = 2 * euclidDist ψ φ := by
        unfold euclidDist
        ring

/-- Two normalized states within Euclidean distance `ε` have computational-basis Born
probabilities whose full L1 distance is at most `4 * ε`. This recovers the source-form
statement of Theorem 3.1 in [BennettEtAl1997]. -/
theorem theorem31_source (ψ φ : QState I) (hψ : Normalized ψ) (hφ : Normalized φ)
    (ε : ℝ) (h : euclidDist ψ φ ≤ ε) :
    bornL1Dist ψ φ ≤ 4 * ε := by
  have h2 := bornL1Dist_le_two_euclid ψ φ hψ hφ
  have hε : 0 ≤ ε := le_trans (euclidDist_nonneg ψ φ) h
  linarith

end Qatlib.Papers.QWeakness97.MainResults
