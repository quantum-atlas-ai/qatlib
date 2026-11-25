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
# The Lasso loss as a distributional expectation

Theorem 4.1 of the fixed source displays `L_{D_{p,W}}(θ)` as an explicit function of `θ`, and the
proof of the theorem derives it from the product laws `D_{p,W}` of Section 4.1. This module
closes that step: for the sign law `D_{p,W}` of `SourceModel`, the expected squared loss
`expectedLoss (lassoDist p W) lassoX θ` equals the closed form `lassoLoss p W θ`.

The computation is the variance decomposition of `Qatlib.Papers.QRegression21.MainResults.expect_sq_sub_one_eq`
applied to the coordinate moments `E[x_j] = 2p` on `W`, `E[x_j] = 0` off `W`, and `E[x_j^2] = 1`.

Boundary: only the expectation identity is proved. The uniqueness and stability statements for
this loss live in the paper-layer Lasso modules of the public library.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QRegression21.MainResults.LassoExpectation

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Papers.QRegression21.MainResults
open Qatlib.Papers.QRegression21.MainResults

/-- The Bernoulli sign law evaluated at `lassoX` has expectation `2 q - 1`. -/
theorem bernoulli_expect_lassoX (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (bernoulli q h0 h1).expect lassoX = 2 * q - 1 :=
  bernoulli_expect_sgn q h0 h1

/-- The squared Bernoulli sign evaluated at `lassoX` has expectation one. -/
theorem bernoulli_expect_lassoX_sq (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (bernoulli q h0 h1).expect (fun b => lassoX b ^ 2) = 1 :=
  bernoulli_expect_sgn_sq q h0 h1

/-- The first coordinate moment of the Lasso law: `E[x_j] = 2p` on `W` and zero off `W`. -/
theorem lassoCoord_expect {d : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (W : Finset (Fin d)) (j : Fin d) :
    (lassoCoord p hp0 hp1 W j).expect lassoX = if j ∈ W then 2 * p else 0 := by
  unfold lassoCoord
  by_cases hj : j ∈ W
  · rw [ite_eq_left hj, ite_eq_left hj, bernoulli_expect_lassoX]
    ring
  · rw [ite_eq_right hj, ite_eq_right hj, bernoulli_expect_lassoX]
    ring

/-- The second coordinate moment of the Lasso law is one. -/
theorem lassoCoord_expect_sq {d : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (W : Finset (Fin d)) (j : Fin d) :
    (lassoCoord p hp0 hp1 W j).expect (fun b => lassoX b ^ 2) = 1 := by
  unfold lassoCoord
  by_cases hj : j ∈ W
  · rw [ite_eq_left hj, bernoulli_expect_lassoX_sq]
  · rw [ite_eq_right hj, bernoulli_expect_lassoX_sq]

/-- A summand that vanishes off `W` sums to a restricted sum. -/
theorem sum_ite_mem_univ {d : ℕ} (W : Finset (Fin d)) (g : Fin d → ℝ) :
    (∑ j, (if j ∈ W then g j else 0)) = ∑ j ∈ W, g j :=
  Fintype.sum_ite_mem W g

/-- Theorem 4.1, first display: the expected squared loss of the Lasso sign law equals the
closed form `lassoLoss`. -/
theorem lassoLoss_eq_expectation {d : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (W : Finset (Fin d)) (θ : Fin d → ℝ) :
    expectedLoss (lassoDist p hp0 hp1 W) lassoX θ = lassoLoss p W θ := by
  classical
  have hμ := lassoCoord_expect p hp0 hp1 W
  have hs := lassoCoord_expect_sq p hp0 hp1 W
  have h1 : (∑ j, θ j * (if j ∈ W then 2 * p else 0)) = 2 * p * ∑ j ∈ W, θ j := by
    calc (∑ j, θ j * (if j ∈ W then 2 * p else 0))
        = ∑ j, (if j ∈ W then θ j * (2 * p) else 0) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : j ∈ W <;> simp [hj]
      _ = ∑ j ∈ W, θ j * (2 * p) := sum_ite_mem_univ W _
      _ = 2 * p * ∑ j ∈ W, θ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (∑ j, θ j ^ 2 * (1 - (if j ∈ W then 2 * p else 0) ^ 2))
      = (∑ j, θ j ^ 2) - 4 * p ^ 2 * ∑ j ∈ W, θ j ^ 2 := by
    calc (∑ j, θ j ^ 2 * (1 - (if j ∈ W then 2 * p else 0) ^ 2))
        = ∑ j, (θ j ^ 2 - (if j ∈ W then θ j ^ 2 * (4 * p ^ 2) else 0)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs with hj
          · ring
          · ring
      _ = (∑ j, θ j ^ 2) - ∑ j, (if j ∈ W then θ j ^ 2 * (4 * p ^ 2) else 0) := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ j, θ j ^ 2) - 4 * p ^ 2 * ∑ j ∈ W, θ j ^ 2 := by
          rw [sum_ite_mem_univ W (fun j => θ j ^ 2 * (4 * p ^ 2)), Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by ring
  change (independentSampleLaw (lassoCoord p hp0 hp1 W)).expect
      (fun b => ((∑ j, θ j * lassoX (b j)) - 1) ^ 2) = lassoLoss p W θ
  rw [expect_sq_sub_one_eq (p := lassoCoord p hp0 hp1 W) (xval := lassoX) (θ := θ)]
  simp only [hμ, hs]
  rw [h1, h2]
  unfold lassoLoss
  ring

end Qatlib.Papers.QRegression21.MainResults.LassoExpectation
