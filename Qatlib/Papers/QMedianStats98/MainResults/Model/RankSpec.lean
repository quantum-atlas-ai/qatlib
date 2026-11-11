/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMedianStats98.MainResults.Model.Basic

/-!
# Rank and counting approximation specifications

This module specifies the approximate order statistics and counting tasks studied in
[NayakWu1998]. Ranks are represented by an interval of possible positions, so repeated values
are handled through the counts of elements strictly below and strictly above the chosen element.

The counting predicates use strict error inequalities. Since strict relative error is impossible
at zero weight, `IsRelativeCount` explicitly requires the estimate to be zero on that input.

## Main statements

- `rankSet`, `IsApproxKth`, and `IsApproxMedian`: specify rank approximation with ties.
* `IsApproxCount` and `IsStrictRelativeCount`: specify additive and strict relative counting
  error.
* `strict_relative_zero_impossible` and `relative_zero_iff`: justify and characterize the
  zero-count convention.

## References

[Nayak and Wu, 1998][NayakWu1998]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QMedianStats98.MainResults.Model

/-- The finite set of indices whose values are strictly smaller than the value at index `i`. -/
def below {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => x j < x i)

/-- The finite set of indices whose values are strictly larger than the value at index `i`. -/
def above {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => x i < x j)

/-- The interval of possible ranks of the element at index `i`, from one plus the number of
strictly smaller elements through `n` minus the number of strictly larger elements. -/
def rankSet {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : Finset ℕ :=
  Finset.Icc ((below x i).card + 1) (n - (above x i).card)

/-- The element at index `i` is a `delta`-approximate kth element when one of its possible ranks
differs from `k` by strictly less than `delta`. -/
def IsApproxKth {n : ℕ} (x : Fin n → ℝ) (k : ℕ) (delta : ℝ) (i : Fin n) : Prop :=
  ∃ r ∈ rankSet x i, |(r : ℝ) - (k : ℝ)| < delta

/-- The element at index `i` is an `epsilon`-approximate median when the numbers of elements
strictly below and strictly above it are both strictly less than `(1 + epsilon) * n / 2`. -/
def IsApproxMedian {n : ℕ} (x : Fin n → ℝ) (epsilon : ℝ) (i : Fin n) : Prop :=
  ((below x i).card : ℝ) < (1 + epsilon) * n / 2 ∧
    ((above x i).card : ℝ) < (1 + epsilon) * n / 2

/-- The estimate approximates the Boolean input's Hamming weight with absolute error strictly
less than `delta`. -/
def IsApproxCount {n : ℕ} (X : Fin n → Bool) (delta estimate : ℝ) : Prop :=
  |estimate - (weight X : ℝ)| < delta

/-- The estimate approximates the Boolean input's Hamming weight with absolute error strictly
less than `epsilon` times that weight. -/
def IsStrictRelativeCount {n : ℕ} (X : Fin n → Bool) (epsilon estimate : ℝ) : Prop :=
  |estimate - (weight X : ℝ)| < epsilon * (weight X : ℝ)

/-- The all-false Boolean input has Hamming weight zero. -/
theorem weight_all_false (n : ℕ) : weight (fun _ : Fin n => false) = 0 := by
  simp [weight]

/-- No estimate satisfies strict relative counting error on the all-false input, since the
required error bound is strictly below zero. -/
theorem strict_relative_zero_impossible (n : ℕ) (epsilon estimate : ℝ) :
    ¬ IsStrictRelativeCount (fun _ : Fin n => false) epsilon estimate := by
  simp only [IsStrictRelativeCount, weight_all_false, Nat.cast_zero, sub_zero, mul_zero]
  exact not_lt_of_ge (abs_nonneg estimate)

/-- Relative counting requires an exact zero estimate at zero weight and the strict
relative-error predicate at every nonzero weight. -/
def IsRelativeCount {n : ℕ} (X : Fin n → Bool) (epsilon estimate : ℝ) : Prop :=
  if weight X = 0 then estimate = 0 else IsStrictRelativeCount X epsilon estimate

/-- On the all-false input, the relative counting predicate holds exactly when the estimate is
zero. -/
theorem relative_zero_iff (n : ℕ) (epsilon estimate : ℝ) :
    IsRelativeCount (fun _ : Fin n => false) epsilon estimate ↔ estimate = 0 := by
  simp [IsRelativeCount, weight_all_false]

end Qatlib.Papers.QMedianStats98.MainResults.Model
