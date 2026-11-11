/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Tactic.Ring

/-!
# Mean and variance of finite ensembles

This module defines `ensembleMean` and `ensembleVariance` for a real-valued function on a finite
probability space. It proves their behavior under constant shifts and characterizes zero
variance by constancy on the support. See [RudolphEtAl2024].

## Main statements

* `ensembleVariance_add_const`: adding a constant leaves variance unchanged.
* `ensembleVariance_eq_zero_iff`: zero variance is equivalent to equality with the mean at every
  point of nonzero probability.
* `ensembleVariance_eq_meanSq_sub_sq`: variance equals the second moment minus the squared mean.

## References

* [Rudolph et al., 2024][RudolphEtAl2024]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.Trainability23.VarianceScaling

open scoped BigOperators

/-- The probability-weighted mean of a real-valued function over a finite ensemble. -/
noncomputable def ensembleMean {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (L : Θ → ℝ) : ℝ :=
  ∑ θ, P.prob θ * L θ

/-- The probability-weighted mean of the squared deviation of `L` from its ensemble mean. -/
noncomputable def ensembleVariance {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (L : Θ → ℝ) : ℝ :=
  ∑ θ, P.prob θ * (L θ - ensembleMean P L) ^ 2

/-- The mean of a constant function is that constant. -/
theorem ensembleMean_const {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (c : ℝ) :
    ensembleMean P (fun _ => c) = c := by
  unfold ensembleMean
  rw [← Finset.sum_mul, P.sum_one, one_mul]

/-- A constant function has zero ensemble variance. -/
theorem ensembleVariance_const {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (c : ℝ) :
    ensembleVariance P (fun _ => c) = 0 := by
  unfold ensembleVariance
  rw [ensembleMean_const]
  simp

/-- Adding a constant to a function adds the same constant to its ensemble mean. -/
theorem ensembleMean_add_const {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (L : Θ → ℝ) (c : ℝ) :
    ensembleMean P (fun θ => L θ + c) = ensembleMean P L + c := by
  have h : ∀ θ : Θ, P.prob θ * (L θ + c) = P.prob θ * L θ + P.prob θ * c := fun θ => by ring
  unfold ensembleMean
  rw [Finset.sum_congr rfl fun θ _ => h θ, Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_one,
    one_mul]

/-- Adding a constant to a function leaves its ensemble variance unchanged. -/
theorem ensembleVariance_add_const {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (L : Θ → ℝ) (c : ℝ) :
    ensembleVariance P (fun θ => L θ + c) = ensembleVariance P L := by
  unfold ensembleVariance
  rw [ensembleMean_add_const]
  exact Finset.sum_congr rfl fun θ _ => by ring

/-- The ensemble variance of a real-valued function is nonnegative. -/
theorem ensembleVariance_nonneg {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (L : Θ → ℝ) :
    0 ≤ ensembleVariance P L :=
  Finset.sum_nonneg fun θ _ => mul_nonneg (P.nonneg θ) (sq_nonneg _)

/-- The ensemble variance is zero exactly when the function equals its mean at every point with
nonzero probability. -/
theorem ensembleVariance_eq_zero_iff {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (L : Θ → ℝ) :
    ensembleVariance P L = 0 ↔ ∀ θ, P.prob θ ≠ 0 → L θ = ensembleMean P L := by
  constructor
  · intro h
    have hnn : ∀ θ ∈ (Finset.univ : Finset Θ),
        0 ≤ P.prob θ * (L θ - ensembleMean P L) ^ 2 :=
      fun θ _ => mul_nonneg (P.nonneg θ) (sq_nonneg _)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
    intro θ hθ
    have h0 := hall θ (Finset.mem_univ θ)
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hθ
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h1)
  · intro h
    refine Finset.sum_eq_zero fun θ _ => ?_
    by_cases hθ : P.prob θ = 0
    · rw [hθ, zero_mul]
    · rw [h θ hθ]
      ring

/-- The ensemble variance equals the probability-weighted second moment minus the square of the
ensemble mean. -/
theorem ensembleVariance_eq_meanSq_sub_sq {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (L : Θ → ℝ) :
    ensembleVariance P L = (∑ θ, P.prob θ * (L θ) ^ 2) - (ensembleMean P L) ^ 2 := by
  have h : ∀ θ : Θ, P.prob θ * (L θ - ensembleMean P L) ^ 2
      = P.prob θ * (L θ) ^ 2 - 2 * ensembleMean P L * (P.prob θ * L θ)
        + (ensembleMean P L) ^ 2 * P.prob θ := fun θ => by ring
  unfold ensembleVariance
  rw [Finset.sum_congr rfl fun θ _ => h θ, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [show (∑ θ : Θ, P.prob θ * L θ) = ensembleMean P L from rfl, P.sum_one, mul_one]
  ring

end Qatlib.Papers.Trainability23.VarianceScaling
