/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Normed.Group.Basic
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Uniform sampling for normalized character estimates

This module defines the uniform finite law and proves sampling bounds for a real function whose
sum equals a supplied character value. With the explicit identity and pointwise bound assumed,
`normalized_character_sample_bound` gives the normalized-character estimate used in
[Jordan2008a].

## Main statements

* `normalized_character_expectation`: the uniform expectation of a character summand.
* `normalized_character_sample_bound`: a `4 / (L * ε^2)` deviation bound.

## References

* [Jordan, 2008][Jordan2008a]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.GroupReps08.MainResults.CharacterEstimation

variable {Λ : Type*} [Fintype Λ] [Nonempty Λ]

/-- The uniform probability distribution on a finite nonempty type [Jordan2008a]. -/
def uniformLaw (Λ : Type*) [Fintype Λ] [Nonempty Λ] : FinDist Λ where
  prob _ := (Fintype.card Λ : ℝ)⁻¹
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card Λ : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card Λ ≠ 0)
    field_simp

/-- If `χ` is the sum of `W`, the uniform expectation of `W` equals `χ` divided by the
cardinality of the sample space [Jordan2008a]. -/
theorem normalized_character_expectation (W : Λ → ℝ) (χ : ℝ)
    (hRoichman : χ = ∑ x, W x) :
    (uniformLaw Λ).expect W = χ / (Fintype.card Λ : ℝ) := by
  show (∑ x, (Fintype.card Λ : ℝ)⁻¹ * W x) = χ / (Fintype.card Λ : ℝ)
  rw [← Finset.mul_sum, ← hRoichman, div_eq_inv_mul]

/-- A real function bounded in absolute value by one has uniform expectation bounded in absolute
value by one [Jordan2008a]. -/
theorem abs_expect_le_one (W : Λ → ℝ) (hf : ∀ x, |W x| ≤ 1) :
    |(uniformLaw Λ).expect W| ≤ 1 := by
  show |∑ x, (Fintype.card Λ : ℝ)⁻¹ * W x| ≤ 1
  calc |∑ x, (Fintype.card Λ : ℝ)⁻¹ * W x|
      ≤ ∑ x, |(Fintype.card Λ : ℝ)⁻¹ * W x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, (Fintype.card Λ : ℝ)⁻¹ * |W x| := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ ∑ _x : Λ, (Fintype.card Λ : ℝ)⁻¹ * 1 := by
          refine Finset.sum_le_sum fun x _ => ?_
          gcongr
          exact hf x
    _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hc : (Fintype.card Λ : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_ne_zero : Fintype.card Λ ≠ 0)
          field_simp

/-- A real function bounded in absolute value by one has uniform variance at most four
[Jordan2008a]. -/
theorem uniform_variance_le_four (W : Λ → ℝ) (hf : ∀ x, |W x| ≤ 1) :
    (uniformLaw Λ).variance W ≤ 4 := by
  have hμ := abs_expect_le_one W hf
  have hbound : ∀ x, (W x - (uniformLaw Λ).expect W) ^ 2 ≤ 4 := by
    intro x
    have hz : |W x - (uniformLaw Λ).expect W| ≤ 2 := by
      calc |W x - (uniformLaw Λ).expect W|
          ≤ |W x| + |(uniformLaw Λ).expect W| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              abs_add_le (W x) (-(uniformLaw Λ).expect W)
        _ ≤ 1 + 1 := add_le_add (hf x) hμ
        _ = 2 := by norm_num
    nlinarith [(abs_le.mp hz).1, (abs_le.mp hz).2]
  show ∑ x, (Fintype.card Λ : ℝ)⁻¹ * (W x - (uniformLaw Λ).expect W) ^ 2 ≤ 4
  calc ∑ x, (Fintype.card Λ : ℝ)⁻¹ * (W x - (uniformLaw Λ).expect W) ^ 2
      ≤ ∑ _x : Λ, (Fintype.card Λ : ℝ)⁻¹ * 4 := by
          refine Finset.sum_le_sum fun x _ => ?_
          exact mul_le_mul_of_nonneg_left (hbound x) (by positivity)
    _ = 4 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hc : (Fintype.card Λ : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_ne_zero : Fintype.card Λ ≠ 0)
          field_simp

/-- Given the character-sum identity and `|W| ≤ 1`, the probability that the average of `L > 0`
uniform samples differs from the normalized character by more than positive `ε` is at most
`4 / (L * ε^2)` [Jordan2008a]. -/
theorem normalized_character_sample_bound [DecidableEq Λ] (W : Λ → ℝ) (χ : ℝ)
    (hRoichman : χ = ∑ x, W x) (hf : ∀ x, |W x| ≤ 1)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) :
    FinDist.probEvent (L := L) (uniformLaw Λ)
        (fun ω => ε < |FinDist.avg W ω - χ / (Fintype.card Λ : ℝ)|)
      ≤ 4 / (L * ε ^ 2) := by
  have hcheb := FinDist.chebyshev_avg (uniformLaw Λ) W hL ε hε
  rw [normalized_character_expectation W χ hRoichman] at hcheb
  refine le_trans hcheb ?_
  have hvar := uniform_variance_le_four W hf
  have hden : (0 : ℝ) ≤ (L : ℝ) * ε ^ 2 := by positivity
  calc (uniformLaw Λ).variance W / ((L : ℝ) * ε ^ 2)
      ≤ 4 / ((L : ℝ) * ε ^ 2) := div_le_div_of_nonneg_right hvar hden
    _ = 4 / (L * ε ^ 2) := by ring

end Qatlib.Papers.GroupReps08.MainResults.CharacterEstimation
