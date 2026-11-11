/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.RestartLaw.Section3RestartExpectedSubgoalStat
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Geometric expectations for Grover restarts

Proves `geometric_restart_expectation` for a real cost and a success probability in `(0, 1]`.
Applying the formula to Grover measurement probabilities establishes
`section3RestartExpectedSubgoal`. For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `geometric_restart_expectation`: For `0 < p ≤ 1` and any real cost `c`, the sum of `(r + 1) *
  c` against the geometric first-success weights `(1 - p) ^ r * p` equals `c / p`.
* `section3RestartExpectedSubgoal`: Establishes `Section3RestartExpectedSubgoal`, evaluating the
  expected Grover iteration cost of fixed-length restarts.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option warningAsError false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.SearchStopping.RestartLaw

open Qatlib.Concepts.SearchStopping.KnownCount

/-- For `0 < p ≤ 1` and any real cost `c`, the sum of `(r + 1) * c` against the geometric
first-success weights `(1 - p) ^ r * p` equals `c / p`. -/
theorem geometric_restart_expectation (p c : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑' r : ℕ, ((r + 1 : ℕ) : ℝ) * c * ((1 - p)^r * p)) = c / p := by
  have hr : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp1)]
    linarith
  have hs : HasSum (fun r : ℕ => ((r + 1 : ℕ) : ℝ) * (1 - p)^r) (1 / p^2) := by
    simpa using hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hr
  have hscaled := hs.mul_right (c * p)
  have heq : (fun r : ℕ => ((r + 1 : ℕ) : ℝ) * c * ((1 - p)^r * p)) =
      (fun r : ℕ => (((r + 1 : ℕ) : ℝ) * (1 - p)^r) * (c * p)) := by
    funext r
    ring
  rw [heq, hscaled.tsum_eq]
  field_simp

/-- Establishes `Section3RestartExpectedSubgoal`, evaluating the expected Grover iteration cost
of fixed-length restarts. -/
theorem section3RestartExpectedSubgoal : Section3RestartExpectedSubgoal := by
  intro I _ _ hN A θ j hθ hθupper hangle hp
  have hs : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos])).ne'
  have hc : Real.cos θ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθupper⟩).ne'
  have hp1 : MeasureProb (GroverState A j) A ≤ 1 := by
    rw [measureProb_groverState hN A θ hangle hs hc j]
    nlinarith [Real.sin_le_one ((2 * (j : ℝ) + 1) * θ),
      Real.neg_one_le_sin ((2 * (j : ℝ) + 1) * θ)]
  exact geometric_restart_expectation _ _ hp hp1

end Qatlib.Concepts.SearchStopping.RestartLaw
