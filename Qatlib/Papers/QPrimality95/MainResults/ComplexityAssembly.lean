/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CostRecurrences.UniformCosts
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Auxiliary estimates for primality-test complexity

This module supplies elementary analytic and probabilistic inequalities used in the complexity
analysis of [ChauLo1995]. `trialDivision_bracket` bounds the trial-division expression,
`repeat_success_ge` compares repeated success with the half-success baseline, and
`average_success_ge` converts a lower bound on a good subset into a lower bound on the uniform
average.

## Main statements

* `trialDivision_bracket`: If `L > 1`, `B = log L`, and `B ≥ 1`, then `L² / B + L² * B / log (L²
  / B) ≤ 2 * L²`.
* `repeat_success_ge`: For a success probability `p` between one half and one, the expression `1
  - (1 - p) ^ k` is at least `1 - (1 / 2) ^ k`.
* `average_success_ge`: A nonnegative finite family bounded below by `c` on a good subset has
  uniform average at least `c` times the fraction of good indices.

## References

* [Chau and Lo, 1995][ChauLo1995]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.QPrimality95.MainResults

/-- If `L > 1`, `B = log L`, and `B ≥ 1`, then `L² / B + L² * B / log (L² / B) ≤ 2 * L²`. -/
theorem trialDivision_bracket (L B : ℝ) (hL : 1 < L) (hB : B = Real.log L)
    (hB1 : 1 ≤ B) :
    L ^ 2 / B + L ^ 2 * B / Real.log (L ^ 2 / B) ≤ 2 * L ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hB0 : 0 < B := by linarith
  have hkpos : 0 < L ^ 2 / B := div_pos (pow_pos hL0 2) hB0
  have hlogk : Real.log (L ^ 2 / B) = 2 * B - Real.log B := by
    rw [Real.log_div (pow_ne_zero 2 hL0.ne') hB0.ne', Real.log_pow, hB]
    ring
  have hlogB : Real.log B ≤ B := Real.log_le_self (by linarith)
  have hlogk_ge : B ≤ Real.log (L ^ 2 / B) := by
    rw [hlogk]
    linarith
  have hfirst : L ^ 2 / B ≤ L ^ 2 := by
    rw [div_le_iff₀ hB0]
    have h1 : (0 : ℝ) ≤ L ^ 2 := sq_nonneg L
    nlinarith
  have hsecond : L ^ 2 * B / Real.log (L ^ 2 / B) ≤ L ^ 2 := by
    have hlogpos : 0 < Real.log (L ^ 2 / B) := lt_of_lt_of_le (by linarith) hlogk_ge
    rw [div_le_iff₀ hlogpos]
    have h1 : L ^ 2 * B ≤ L ^ 2 * Real.log (L ^ 2 / B) :=
      mul_le_mul_of_nonneg_left hlogk_ge (sq_nonneg L)
    linarith
  linarith

/-- For a success probability `p` between one half and one, the expression `1 - (1 - p) ^ k` is
at least `1 - (1 / 2) ^ k`. -/
theorem repeat_success_ge (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    1 - (1 / 2 : ℝ) ^ k ≤ 1 - (1 - p) ^ k := by
  have h0 : 0 ≤ 1 - p := by linarith
  have h : 1 - p ≤ 1 / 2 := by linarith
  have hk := pow_le_pow_left₀ h0 h k
  linarith

/-- A nonnegative finite family bounded below by `c` on a good subset has uniform average at
least `c` times the fraction of good indices. -/
theorem average_success_ge {ι : Type*} [Fintype ι] (s : ι → ℝ) (good : Finset ι)
    (c : ℝ) (_hc : 0 ≤ c) (hs : ∀ i, 0 ≤ s i) (hgood : ∀ i ∈ good, c ≤ s i) :
    c * (good.card : ℝ) / (Fintype.card ι : ℝ) ≤ (∑ i, s i) / (Fintype.card ι : ℝ) := by
  have hsum : c * (good.card : ℝ) ≤ ∑ i, s i := by
    have h1 : (∑ i ∈ good, c) ≤ ∑ i ∈ good, s i := Finset.sum_le_sum hgood
    have h2 : (∑ i ∈ good, s i) ≤ ∑ i, s i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
        (fun i _ _ => hs i)
    have h3 : (∑ i ∈ good, c) = c * good.card := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    calc c * (good.card : ℝ) = ∑ i ∈ good, c := h3.symm
      _ ≤ ∑ i ∈ good, s i := h1
      _ ≤ ∑ i, s i := h2
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

end Qatlib.Papers.QPrimality95.MainResults
