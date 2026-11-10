/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DysonSeries22.TimeSteps
import Qatlib.Papers.DysonSeries22.HistorySystem
set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Papers.DysonSeries22.MainResults
open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.DysonSeries22.ExactSource
open Qatlib.Papers.DysonSeries22.Truncation
open Qatlib.Papers.DysonSeries22.TimeSteps
open Qatlib.Papers.DysonSeries22.PureDistance
variable {I : Type} [Fintype I] [DecidableEq I]

theorem finite_endpoint_rankone_error (A : ℝ → Matrix I I ℂ) (b x : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b) (s t : ℝ)
    (hx : ∀ u, HasDerivAt x (A u *ᵥ x u + b u) u) (K : ℕ) :
    rankOneDistance (truncatedSolution A b (x s) s t K) (toEuclidean_fromVec (x t)) ≤
      ‖orderedEvolution (fun u => -A u) s t - truncatedEvolution A s t K‖ *
        ‖toEuclidean_fromVec (x s)‖ +
      ‖toEuclidean_fromVec (dysonSourceSeries A b s t) - truncatedSource A b s t K‖ := by
  apply (rankOneDistance_le_vector_error _ _).trans
  rw [norm_sub_rev]
  exact solution_error_le A b x hA hb s t hx K

theorem long_endpoint_rankone_error (A : ℝ → Matrix I I ℂ) (b x : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b) (hlog : HasNonpositiveLogNorm A)
    (hx : ∀ u, HasDerivAt x (A u *ᵥ x u + b u) u)
    (t : ℕ → ℝ) (ht : ∀ n, t n≤t (n+1)) (K n : ℕ) :
    rankOneDistance (finiteMarch A b t K (toEuclidean_fromVec (x (t 0))) n)
      (toEuclidean_fromVec (x (t n))) ≤
      ∑ j ∈ Finset.range n, localDefect A b t K
        (finiteMarch A b t K (toEuclidean_fromVec (x (t 0)))) j :=
  (rankOneDistance_le_vector_error _ _).trans (finiteMarch_error A b x hA hb hlog hx t ht K n)

theorem constant_derivative_scale (T bMax lamA xMax : ℝ) : DBound T bMax lamA xMax 0 0=0 := by
  simp [DBound]
end Qatlib.Papers.DysonSeries22.MainResults
