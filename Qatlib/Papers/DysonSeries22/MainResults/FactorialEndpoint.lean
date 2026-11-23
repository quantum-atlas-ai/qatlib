/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DysonSeries22.MainResults

@[expose] public section

/-!
# Explicit factorial endpoint error

This continuation combines the paper's endpoint rank-one estimate with the finite Dyson
factorial tails.  It keeps the Euclidean/operator-norm constants and all finite-interval
premises explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DysonSeries22.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.DysonSeries22.ExactSource
open Qatlib.Papers.DysonSeries22.MainResults
open Qatlib.Papers.DysonSeries22.Truncation
open Qatlib.Papers.DysonSeries22.PureDistance

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The finite Dyson endpoint rank-one error with the explicit factorial evolution and forcing
tails.  The matrix bound `M`, driving bound `C`, nonnegative constants, and interval hypotheses
are all part of the statement, so the estimate applies to every finite truncation order `K`. -/
theorem finite_endpoint_rankone_factorial_error
    (A : ℝ → Matrix I I ℂ) (b x : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b)
    (s t M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hboundA : ∀ u ∈ Set.uIcc s t, ‖A u‖ ≤ M)
    (hboundb : ∀ u ∈ Set.uIcc s t,
      ‖toEuclidean_fromVec (b u)‖ ≤ C)
    (hx : ∀ u, HasDerivAt x (A u *ᵥ x u + b u) u) (K : ℕ) :
    rankOneDistance (truncatedSolution A b (x s) s t K)
        (toEuclidean_fromVec (x t)) ≤
      (M * |t - s|) ^ (K + 1) / ((K + 1).factorial : ℝ) *
          Real.exp (M * |t - s|) * ‖toEuclidean_fromVec (x s)‖ +
        C * |t - s| *
          ((M * |t - s|) ^ K / ((K + 1).factorial : ℝ) *
            Real.exp (M * |t - s|)) := by
  have hendpoint := finite_endpoint_rankone_error A b x hA hb s t hx K
  have hevolution := evolution_error_factorial A hA s t M hM hboundA K
  have hsource := source_error_factorial A b hA hb s t M C hM hC hboundA hboundb K
  exact hendpoint.trans
    (add_le_add
      (mul_le_mul_of_nonneg_right hevolution (norm_nonneg _)) hsource)

end Qatlib.Papers.DysonSeries22.MainResults
