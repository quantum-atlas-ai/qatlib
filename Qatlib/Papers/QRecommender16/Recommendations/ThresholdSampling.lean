/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRecommender16.QramMatrix.MatrixStorage
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Recommendations from a thresholded right singular subspace

[KerenidisPrakash2017], Sections 5.3 and 6, projects a row of the subsampled
preference matrix onto a right singular subspace and samples a column from the
normalized squared amplitudes. This module computes the ideal filter given the
right singular data and reads the input row from dynamic QRAM. A nonzero
filtered row is required for the sampling law.

[Fixed source](https://arxiv.org/abs/1603.08675v3)
-/

set_option autoImplicit false

namespace Qatlib.Papers.QRecommender16.Recommendations

open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Papers.QRecommender16.QramMatrix
open scoped BigOperators

variable {columns : ℕ} {Index : Type*} [Fintype Index]

/-- Expand a row in the retained right singular directions. -/
noncomputable def thresholdProjection (right : Index → Address columns → ℝ)
    (singular : Index → ℝ) (cutoff : ℝ) (row : Address columns → ℝ)
    (column : Address columns) : ℝ :=
  ∑ i, if cutoff ≤ singular i then (∑ j, right i j * row j) * right i column else 0

/-- An orthonormal family keeps the coefficient of every retained right singular vector and
zeros the coefficients of discarded vectors. -/
theorem threshold_projection_coefficient [DecidableEq Index]
    (right : Index → Address columns → ℝ) (singular : Index → ℝ) (cutoff : ℝ)
    (row : Address columns → ℝ) (index : Index)
    (hOrthogonal : ∀ i k, (∑ j, right i j * right k j) = if i = k then 1 else 0) :
    ∑ column, right index column * thresholdProjection right singular cutoff row column =
      if cutoff ≤ singular index then ∑ j, right index j * row j else 0 := by
  let coefficient : Index → ℝ :=
    fun i => if cutoff ≤ singular i then ∑ j, right i j * row j else 0
  have hExpand (column : Address columns) :
      thresholdProjection right singular cutoff row column =
        ∑ i, coefficient i * right i column := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hKeep : cutoff ≤ singular i <;> simp [coefficient, hKeep]
  simp_rw [hExpand, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, coefficient i * ∑ column, right index column * right i column := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro column _
      ring
    _ = coefficient index := by
      simp only [hOrthogonal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    _ = _ := rfl

/-- Apply the ideal filter to the row of the subsampled matrix read from QRAM. -/
noncomputable def filteredRow {rows : ℕ} (storage : MatrixStorage rows columns)
    (user : Address rows) (right : Index → Address columns → ℝ)
    (singular : Index → ℝ) (cutoff : ℝ) : Address columns → ℝ :=
  thresholdProjection right singular cutoff (entry storage user)

/-- Threshold the singular-value estimates at the midpoint of the transition interval. -/
noncomputable def estimatedProjection {rows : ℕ} (storage : MatrixStorage rows columns)
    (user : Address rows) (right : Index → Address columns → ℝ)
    (estimatedSingular : Index → ℝ) (cutoff halfWidth : ℝ) : Address columns → ℝ :=
  filteredRow storage user right estimatedSingular (cutoff - halfWidth)

/-- An estimate within the half-width retains every singular value at or above the cutoff. -/
theorem estimate_keeps_above (singular estimate cutoff halfWidth : ℝ)
    (hError : |estimate - singular| ≤ halfWidth) (hAbove : cutoff ≤ singular) :
    cutoff - halfWidth ≤ estimate := by
  have hLower := (abs_le.mp hError).1
  linarith

/-- An estimate within the half-width discards values strictly below the transition interval. -/
theorem estimate_discards_below (singular estimate cutoff halfWidth : ℝ)
    (hError : |estimate - singular| ≤ halfWidth) (hBelow : singular < cutoff - 2 * halfWidth) :
    estimate < cutoff - halfWidth := by
  have hUpper := (abs_le.mp hError).2
  linarith

/-- The probability of recommending a column after conditioning on successful projection. -/
noncomputable def recommendationWeight (row : Address columns → ℝ) (column : Address columns) :
    ℝ := row column ^ 2 / ∑ j, row j ^ 2

/-- Squared amplitudes of any nonzero filtered row define a probability law. -/
theorem recommendation_weights_sum (row : Address columns → ℝ)
    (h : 0 < ∑ j, row j ^ 2) : ∑ column, recommendationWeight row column = 1 := by
  simp only [recommendationWeight, ← Finset.sum_div, div_self h.ne']

/-- The recommendation weights are nonnegative. -/
theorem recommendation_weight_nonneg (row : Address columns → ℝ) (column : Address columns) :
    0 ≤ recommendationWeight row column :=
  div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The cutoff in Algorithm 6.1, using the root Frobenius norm of the subsample. -/
noncomputable def recommendationCutoff {rows : ℕ} (storage : MatrixStorage rows columns)
    (relativeError observationProbability : ℝ) (rank : ℕ) : ℝ :=
  Real.sqrt (relativeError ^ 2 * observationProbability / (2 * rank)) * Real.sqrt (mass storage)

/-- Apply the paper's cutoff and transition width to a user's row and its spectral estimates. -/
noncomputable def recommendationRow {rows : ℕ} (storage : MatrixStorage rows columns)
    (user : Address rows) (right : Index → Address columns → ℝ)
    (estimatedSingular : Index → ℝ) (relativeError observationProbability : ℝ)
    (rank : ℕ) : Address columns → ℝ :=
  let cutoff := recommendationCutoff storage relativeError observationProbability rank
  estimatedProjection storage user right estimatedSingular cutoff (cutoff / 6)

/-- The classical product law of Algorithm 6.1 conditional on the retained spectral subspace. -/
noncomputable def recommendationDistribution {rows : ℕ} (storage : MatrixStorage rows columns)
    (user : Address rows) (right : Index → Address columns → ℝ)
    (estimatedSingular : Index → ℝ) (relativeError observationProbability : ℝ)
    (rank : ℕ) : Address columns → ℝ :=
  recommendationWeight (recommendationRow storage user right estimatedSingular
    relativeError observationProbability rank)

/-- The conditional product law sums to one whenever the retained user row is nonzero. -/
theorem recommendation_distribution_sum {rows : ℕ} (storage : MatrixStorage rows columns)
    (user : Address rows) (right : Index → Address columns → ℝ)
    (estimatedSingular : Index → ℝ) (relativeError observationProbability : ℝ)
    (rank : ℕ) (hRow : 0 < ∑ column, recommendationRow storage user right estimatedSingular
      relativeError observationProbability rank column ^ 2) :
    ∑ column, recommendationDistribution storage user right estimatedSingular
      relativeError observationProbability rank column = 1 :=
  recommendation_weights_sum _ hRow

/-- Probability mass assigned to the products that have zero true preference. -/
noncomputable def badRecommendationProbability (truth approximate : Address columns → ℝ) : ℝ :=
  ∑ column, if truth column = 0 then recommendationWeight approximate column else 0

/-- Every contribution to a bad recommendation is a component of squared approximation error. -/
theorem bad_recommendation_le_row_error (truth approximate : Address columns → ℝ) :
    badRecommendationProbability truth approximate ≤
      (∑ column, (truth column - approximate column) ^ 2) / ∑ column, approximate column ^ 2 := by
  rw [badRecommendationProbability, Finset.sum_div]
  apply Finset.sum_le_sum
  intro column _
  by_cases hTrue : truth column = 0
  · simp [hTrue, recommendationWeight]
  · simp only [ite_eq_right hTrue]
    exact div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end Qatlib.Papers.QRecommender16.Recommendations
