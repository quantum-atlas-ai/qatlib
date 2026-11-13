/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DysonSeries22.TimeSteps
import Qatlib.Papers.DysonSeries22.HistorySystem

/-!
# Dyson endpoint error bounds

This module combines the Dyson solution and time marching estimates with the phase insensitive
distance `rankOneDistance`. It bounds finite interval endpoint error by evolution and source
truncation errors, and bounds the endpoint error of a dissipative time march by the sum of local
defects. It also records the vanishing derivative scale for constant coefficients.

The mathematical setting follows [BerryCosta2024].

## Main statements

* `finite_endpoint_rankone_error`: endpoint distance bounded by the two truncation errors.
* `long_endpoint_rankone_error`: endpoint distance bounded by accumulated local defects.

## References

* [Berry and Costa, 2024][BerryCosta2024]
-/

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

/-- For a solution with continuous coefficients, the rank one endpoint distance of the truncated
solution is bounded by the evolution truncation error times the initial norm plus the source
truncation error. -/
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

/-- For a dissipative equation on a nondecreasing time grid, the rank one distance between the
finite march and the exact endpoint is at most the sum of the local defects. See [Berry and
Costa, 2024, Theorem 4.1; Eqs. (80)–(108)][BerryCosta2024]. -/
theorem long_endpoint_rankone_error (A : ℝ → Matrix I I ℂ) (b x : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b) (hlog : HasNonpositiveLogNorm A)
    (hx : ∀ u, HasDerivAt x (A u *ᵥ x u + b u) u)
    (t : ℕ → ℝ) (ht : ∀ n, t n≤t (n+1)) (K n : ℕ) :
    rankOneDistance (finiteMarch A b t K (toEuclidean_fromVec (x (t 0))) n)
      (toEuclidean_fromVec (x (t n))) ≤
      ∑ j ∈ Finset.range n, localDefect A b t K
        (finiteMarch A b t K (toEuclidean_fromVec (x (t 0)))) j :=
  (rankOneDistance_le_vector_error _ _).trans (finiteMarch_error A b x hA hb hlog hx t ht K n)

/-- The derivative scale `DBound` vanishes when both derivative parameters are zero. See [Berry
and Costa, 2024, Eqs. (71)–(77), (88), (92)][BerryCosta2024]. -/
theorem constant_derivative_scale (T bMax lamA xMax : ℝ) : DBound T bMax lamA xMax 0 0=0 := by
  simp [DBound]
end Qatlib.Papers.DysonSeries22.MainResults
