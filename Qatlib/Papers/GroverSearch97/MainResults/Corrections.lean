/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroverSearch96.MainResults.Counterexamples

/-!
# Corrections to Grover amplitude and success claims

The module records explicit small register examples that delimit strict success and amplitude
gain assertions. `source_two_state_counterexample` gives constant success one half, and
`source_printed_parametrization_not_normalized` exhibits a four state vector that fails
normalization.

The remaining examples compute actual Grover updates and show that the corresponding marked
amplitude increments fail the displayed stronger bounds. See [Grover1997].

## Main statements

* `source_two_state_counterexample`: Singleton Grover search on a two state register has success
  probability exactly `1/2` at every iteration count.
* `source_actual_step_counterexample`: The normalized two state vector with amplitudes `3/5` and
  `4/5` evolves in one Grover step to amplitudes `4/5` and `-3/5`, with marked gain at most `1 /
  (2 * sqrt 2)`.
* `source_four_state_strong_gain_counterexample`: The normalized four state vector with
  amplitudes `2/3` and `sqrt 15 / 9` satisfies the stated positivity and marked threshold
  conditions, but its actual Grover marked amplitude gain is strictly less than `1 / sqrt 8`.

## References

* [Grover, 1997][Grover1997]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Papers.GroverSearch97.MainResults

/-- Singleton Grover search on a two state register has success probability exactly `1/2` at
every iteration count. See [Grover1997]. -/
theorem source_two_state_counterexample (w : Reg 1) (j : ℕ) :
    MeasureProb (GroverState ({w} : Finset (Reg 1)) j) {w} = 1 / 2 :=
  Qatlib.Papers.GroverSearch96.MainResults.two_state_no_strict_success w j

/-- The parameter `3/5` lies strictly between `1/2` and `1`, but the four state vector with
amplitudes `-4/5` and `3/10` is not normalized. See [Grover1997]. -/
theorem source_printed_parametrization_not_normalized (w : Reg 2) :
    (1 / 2 : ℝ) < 3 / 5 ∧ (3 / 5 : ℝ) < 1 ∧
      ¬ Normalized (MarkedVector {w} ((-4 / 5 : ℝ) : ℂ) ((3 / 10 : ℝ) : ℂ)) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [Qatlib.Papers.GroverSearch96.MainResults.normalized_singleton_real_iff]
  norm_num [twoAmplitudeMass]

/-- The normalized two state vector with amplitudes `3/5` and `4/5` evolves in one Grover step
to amplitudes `4/5` and `-3/5`, with marked gain at most `1 / (2 * sqrt 2)`. -/
theorem source_actual_step_counterexample (w : Reg 1) :
    Normalized (MarkedVector {w} ((3 / 5 : ℝ) : ℂ) ((4 / 5 : ℝ) : ℂ)) ∧
      Run (SetOracle {w}) (GroverStep (Reg 1))
        (MarkedVector {w} ((3 / 5 : ℝ) : ℂ) ((4 / 5 : ℝ) : ℂ)) =
        MarkedVector {w} ((4 / 5 : ℝ) : ℂ) ((-3 / 5 : ℝ) : ℂ) ∧
      (4 / 5 - 3 / 5 : ℝ) ≤ 1 / (2 * Real.sqrt 2) := by
  have h := Qatlib.Papers.GroverSearch96.MainResults.theorem3_actual_two_state_counterexample w
  exact ⟨h.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- The normalized four state vector with amplitudes `2/3` and `sqrt 15 / 9` satisfies the
stated positivity and marked threshold conditions, but its actual Grover marked amplitude
gain is strictly less than `1 / sqrt 8`. See [Grover1997]. -/
theorem source_four_state_strong_gain_counterexample (w : Reg 2) :
    Normalized (MarkedVector {w} ((2 / 3 : ℝ) : ℂ) ((Real.sqrt 15 / 9 : ℝ) : ℂ)) ∧
      (0 : ℝ) < 2 / 3 ∧ (2 / 3 : ℝ) < 1 / Real.sqrt 2 ∧
      (0 : ℝ) < Real.sqrt 15 / 9 ∧
      Run (SetOracle {w}) (GroverStep (Reg 2))
        (MarkedVector {w} ((2 / 3 : ℝ) : ℂ) ((Real.sqrt 15 / 9 : ℝ) : ℂ)) =
        MarkedVector {w} (distinguishedAfter 4 (-(2 / 3)) (Real.sqrt 15 / 9) : ℂ)
          (ordinaryAfter 4 (-(2 / 3)) (Real.sqrt 15 / 9) : ℂ) ∧
      distinguishedAfter 4 (-(2 / 3)) (Real.sqrt 15 / 9) - 2 / 3 < 1 / Real.sqrt 8 := by
  have h2 : Real.sqrt (2 : ℝ) < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3 / 2)]
    norm_num
  have h15 : Real.sqrt (15 : ℝ) < 4 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have h8 : Real.sqrt (8 : ℝ) < 3 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3)]
    norm_num
  refine ⟨?_, by norm_num, ?_, by positivity, ?_, ?_⟩
  · rw [Qatlib.Papers.GroverSearch96.MainResults.normalized_singleton_real_iff]
    norm_num [twoAmplitudeMass, div_pow]
  · rw [lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
    nlinarith
  · simpa using Qatlib.Papers.GroverSearch96.MainResults.run_singleton_real_step
      2 w (2 / 3) (Real.sqrt 15 / 9)
  · have he : distinguishedAfter 4 (-(2 / 3)) (Real.sqrt 15 / 9) - 2 / 3 =
        (Real.sqrt 15 - 2) / 6 := by norm_num [distinguishedAfter]; ring
    rw [he]
    have hl : (Real.sqrt 15 - 2) / 6 < (1 / 3 : ℝ) := by linarith
    have hr : (1 / 3 : ℝ) < 1 / Real.sqrt 8 := by
      rw [lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 8))]
      linarith
    exact hl.trans hr

end Qatlib.Papers.GroverSearch97.MainResults
