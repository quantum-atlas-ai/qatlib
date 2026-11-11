/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt

/-!
# Expectations for repeated heuristic trials

`classical_trial_tail_sum` evaluates the geometric tail sum for uniform random seeds.
`heuristic_double_expectation` compares the average square-root trial scale with the square root
of the average classical trial scale. The mathematical context is
[BrassardHoyerTapp1998Counting].

## Main statements

* `classical_trial_tail_sum`: For `0 < h ≤ R`, the geometric tail series with failure
  probability `1 - h/R` has sum `R/h`.
* `heuristic_double_expectation`: For a finite probability distribution and positive
  seed-success counts, the weighted mean of `sqrt (R/h)` is bounded by the square root of the
  weighted mean of `R/h`.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCounting98.MainResults.HeuristicExpectation

open scoped BigOperators

/-- For `0 < h ≤ R`, the geometric tail series with failure probability `1 - h/R` has sum `R/h`.
See [BrassardHoyerTapp1998Counting]. -/
theorem classical_trial_tail_sum (R h : ℕ) (hR : 0 < R) (hh : 0 < h) (hhR : h ≤ R) :
    HasSum (fun j : ℕ => (1 - (h : ℝ) / (R : ℝ)) ^ j) ((R : ℝ) / (h : ℝ)) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hpos : 0 < (h : ℝ) / (R : ℝ) := div_pos hh' hR'
  have hp1 : (h : ℝ) / (R : ℝ) ≤ 1 :=
    (div_le_one hR').mpr (by exact_mod_cast hhR)
  have hr0 : 0 ≤ 1 - (h : ℝ) / (R : ℝ) := by linarith
  have hr1 : 1 - (h : ℝ) / (R : ℝ) < 1 := by linarith
  have hgeom := hasSum_geometric_of_lt_one hr0 hr1
  have hone : 1 - (1 - (h : ℝ) / (R : ℝ)) = (h : ℝ) / (R : ℝ) := by ring
  rw [hone] at hgeom
  rwa [inv_div] at hgeom

/-- For a finite probability distribution and positive seed-success counts, the weighted mean of
`sqrt (R/h)` is bounded by the square root of the weighted mean of `R/h`. See
[BrassardHoyerTapp1998Counting]. -/
theorem heuristic_double_expectation {F : Type} [Fintype F]
    (P : F → ℝ) (R : ℕ) (h : F → ℕ)
    (hP : ∀ i, 0 ≤ P i) (hsum : ∑ i, P i = 1)
    (hR : 0 < R) (hh : ∀ i, 0 < h i) (_hhR : ∀ i, h i ≤ R) :
    (∑ i, P i * Real.sqrt ((R : ℝ) / (h i : ℝ)))
      ≤ Real.sqrt (∑ i, P i * ((R : ℝ) / (h i : ℝ))) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hratio_nonneg (i : F) : 0 ≤ (R : ℝ) / (h i : ℝ) :=
    div_nonneg hR'.le (by exact_mod_cast (hh i).le)
  set a : F → ℝ := fun i => Real.sqrt (P i) with ha
  set b : F → ℝ := fun i => Real.sqrt (P i) * Real.sqrt ((R : ℝ) / (h i : ℝ)) with hb
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) a b
  have hleft : (∑ i, a i * b i) = ∑ i, P i * Real.sqrt ((R : ℝ) / (h i : ℝ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ha, hb]
    rw [← mul_assoc, Real.mul_self_sqrt (hP i)]
  have hfa : (∑ i, a i ^ 2) = 1 := by
    simp only [ha]
    rw [← hsum]
    exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hP i)
  have hgb : (∑ i, b i ^ 2) = ∑ i, P i * ((R : ℝ) / (h i : ℝ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hb]
    rw [mul_pow, Real.sq_sqrt (hP i), Real.sq_sqrt (hratio_nonneg i)]
  rw [hleft, hfa, hgb, one_mul] at hcs
  exact Real.le_sqrt_of_sq_le hcs

end Qatlib.Papers.QCounting98.MainResults.HeuristicExpectation
