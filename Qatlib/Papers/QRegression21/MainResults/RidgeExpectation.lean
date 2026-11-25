/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRegression21.MainResults.ExpectedLossExpansion
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# The Ridge loss as a distributional expectation

The first paragraph of Section 5 of the fixed source derives
`L_{D'_{p,W}}(θ) = ‖θ‖₂² (1 - 4p²) / d + (2p ⟨θ, θ*⟩ - 1)²` from the product law
`D'_{p,W}` whose coordinates take the values `±1/√d`. This module closes that step for the
objects of `SourceModel`: the expected squared loss of `D'_{p,W}` equals the closed form
`ridgeLoss`.

The computation is the variance decomposition of `Qatlib.Papers.QRegression21.MainResults.expect_sq_sub_one_eq`
with the coordinate moments `E[x_j] = 2p θ*_j` and `E[x_j²] = 1/d`.

Boundary: only the expectation identity is proved; the near-minimizer statements of Theorem 5.2
and the sign recovery of Theorem 5.3 are separate paper-layer results.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QRegression21.MainResults.RidgeExpectation

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Papers.QRegression21.MainResults
open Qatlib.Papers.QRegression21.MainResults

/-- The first coordinate moment of the Ridge law: `E[x_j] = 2p θ*_j`. -/
theorem ridgeCoord_expect {d : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (W : Finset (Fin d)) (j : Fin d) :
    (ridgeCoord p hp0 hp1 W j).expect (ridgeX d) = 2 * p * thetaStarRidge d W j := by
  unfold ridgeCoord ridgeX ridgeScale thetaStarRidge
  split_ifs with hj
  · rw [bernoulli_expect_scale]
    ring
  · rw [bernoulli_expect_scale]
    ring

/-- The second coordinate moment of the Ridge law is `1 / d`. -/
theorem ridgeCoord_expect_sq {d : ℕ} (hd : 0 < d) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (W : Finset (Fin d)) (j : Fin d) :
    (ridgeCoord p hp0 hp1 W j).expect (fun b => ridgeX d b ^ 2) = 1 / (d : ℝ) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hscale : (1 / Real.sqrt (d : ℝ)) ^ 2 = 1 / (d : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt hdpos.le]
  unfold ridgeCoord ridgeX ridgeScale
  split_ifs with hj
  · rw [bernoulli_expect_scale_sq, hscale]
  · rw [bernoulli_expect_scale_sq, hscale]

/-- The square of a Ridge reference coordinate is `1 / d`. -/
theorem thetaStarRidge_sq {d : ℕ} (hd : 0 < d) (W : Finset (Fin d)) (j : Fin d) :
    thetaStarRidge d W j ^ 2 = 1 / (d : ℝ) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hsq : (1 / Real.sqrt (d : ℝ)) ^ 2 = 1 / (d : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt hdpos.le]
  unfold thetaStarRidge
  rw [mul_pow]
  by_cases hj : j ∈ W
  · rw [ite_eq_left hj, hsq]
    norm_num
  · rw [ite_eq_right hj, hsq]
    norm_num

/-- Section 5, first paragraph: the expected squared loss of `D'_{p,W}` equals `ridgeLoss`. -/
theorem ridgeLoss_eq_expectation {d : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (W : Finset (Fin d)) (θ : Fin d → ℝ) (hd : 0 < d) :
    expectedLoss (ridgeDist p hp0 hp1 W) (ridgeX d) θ = ridgeLoss d p W θ := by
  classical
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hμ := ridgeCoord_expect p hp0 hp1 W
  have hs := ridgeCoord_expect_sq hd p hp0 hp1 W
  have h1 : (∑ j, θ j * (2 * p * thetaStarRidge d W j))
      = 2 * p * dot θ (thetaStarRidge d W) := by
    rw [dot, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (∑ j, θ j ^ 2 * (1 / (d : ℝ) - (2 * p * thetaStarRidge d W j) ^ 2))
      = (1 - 4 * p ^ 2) / (d : ℝ) * ∑ j, θ j ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsq := thetaStarRidge_sq hd W j
    have hterm : (2 * p * thetaStarRidge d W j) ^ 2 = 4 * p ^ 2 / (d : ℝ) := by
      rw [mul_pow, mul_pow, hsq]
      field_simp
      ring
    rw [hterm]
    field_simp
  change (independentSampleLaw (ridgeCoord p hp0 hp1 W)).expect
      (fun b => ((∑ j, θ j * ridgeX d (b j)) - 1) ^ 2) = ridgeLoss d p W θ
  rw [expect_sq_sub_one_eq (p := ridgeCoord p hp0 hp1 W) (xval := ridgeX d) (θ := θ)]
  simp only [hμ, hs]
  rw [h1, h2]
  unfold ridgeLoss l2NormSq
  ring

end Qatlib.Papers.QRegression21.MainResults.RidgeExpectation
