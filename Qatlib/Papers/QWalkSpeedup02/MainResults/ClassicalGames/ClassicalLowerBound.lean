/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkSpeedup02.MainResults.Common.FiniteProbability
import Qatlib.Papers.QWalkSpeedup02.MainResults.Common.RpowArith
import Qatlib.Papers.QWalkSpeedup02.MainResults.ClassicalGames.GameReductions
import Qatlib.Papers.QWalkSpeedup02.MainResults.ClassicalGames.TreeEmbeddingBound
import Mathlib.Tactic

/-!
# Classical success probability bound

This module combines the assumed game comparison and tree embedding estimates into the classical
success bound used in Theorem 9 of [ChildsEtAl2003]. For `n ≥ 3` and `t ≤ 2^(n/6)`,
`theorem9_classical_query_lower_bound` bounds the first winning event by `4 * 2^(-n/6)`.

## Main statements

* `theorem9_classical_query_lower_bound`: the success bound under the two preceding probability
  estimates.

## References

* [Childs et al., 2003][ChildsEtAl2003]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QWalkSpeedup02.MainResults.ClassicalGames.ClassicalLowerBound

open Qatlib.Papers.QWalkSpeedup02.MainResults.Common.FiniteProbability
open Qatlib.Papers.QWalkSpeedup02.MainResults.Common.RpowArith

/-- For `n ≥ 3` and `t ≤ 2^(n/6)`, the assumed game comparison and bound on the second winning
event imply that the first winning probability is at most `4 * 2^(-n/6)`. See [Childs et
al., Theorem 9][ChildsEtAl2003]. -/
theorem theorem9_classical_query_lower_bound
    {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (n t : ℕ) (hn : 3 ≤ n)
    (ht : (t : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 6))
    (win1 win2 : Ω → Prop) [DecidablePred win1] [DecidablePred win2]
    (hlemma4 : P.eventMass win1 ≤ P.eventMass win2 + 4 * (t : ℝ) / (2 : ℝ) ^ n)
    (hlemma8 : P.eventMass win2 ≤ 3 * (2 : ℝ) ^ (-((n : ℝ) / 6))) :
    P.eventMass win1 ≤ 4 * (2 : ℝ) ^ (-((n : ℝ) / 6)) := by
  have h4 : 4 * (t : ℝ) / (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (-((n : ℝ) / 6)) := by
    have h2n : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
    have hrhs : (2 : ℝ) ^ (-((n : ℝ) / 6)) * (2 : ℝ) ^ n = (2 : ℝ) ^ (5 * (n : ℝ) / 6) := by
      rw [two_pow_eq_two_rpow, two_rpow_add]
      rw [show -((n : ℝ) / 6) + (n : ℝ) = 5 * (n : ℝ) / 6 by ring]
    have hnum : 4 * (t : ℝ) ≤ (2 : ℝ) ^ (5 * (n : ℝ) / 6) := by
      calc 4 * (t : ℝ) ≤ 4 * ((2 : ℝ) ^ ((n : ℝ) / 6)) := by linarith
        _ = (2 : ℝ) ^ (2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 6) := by
            rw [four_eq_two_rpow_two]
        _ = (2 : ℝ) ^ ((2 : ℝ) + (n : ℝ) / 6) := by rw [two_rpow_add]
        _ ≤ (2 : ℝ) ^ (5 * (n : ℝ) / 6) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
            have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            linarith
    rw [div_le_iff₀ h2n, hrhs]
    exact hnum
  linarith

end Qatlib.Papers.QWalkSpeedup02.MainResults.ClassicalGames.ClassicalLowerBound
