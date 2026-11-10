/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.GroverBudget
import Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential.Q2LastRounds
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential

open Complexity

noncomputable def q1SimpleLastRoundsData (hS : ℝ) : ℝ := pow2 (hS + 1)

noncomputable def q1SimpleLastRoundsCost (hS Δfin n k hout Cstar : ℝ) : ℝ :=
  pow2 (hS + 1) +
    pow2 ((hS + Δfin - n) / 2) * lastRoundsCheckingCost k hout Cstar

noncomputable def classicalSimpleLastRoundsCost (hS Δfin n k hout C : ℝ) : ℝ :=
  pow2 (hS + 1) + pow2 (hS + Δfin - n) * (C + pow2 (k - hout))

theorem q1_simple_lastrounds_data_eq_classical (hS : ℝ) :
    q1SimpleLastRoundsData hS = classicalSimpleDistinguisherCost hS := rfl

theorem q1_simple_lastrounds_second_term_sqrt (hS Δfin n : ℝ) :
    pow2 ((hS + Δfin - n) / 2) ^ 2 = pow2 (hS + Δfin - n) :=
  pow2_half_sq (hS + Δfin - n)

theorem q1_simple_lastrounds_cost (hS Δfin n k hout Cstar : ℝ) :
    q1SimpleLastRoundsCost hS Δfin n k hout Cstar =
      q1SimpleLastRoundsData hS +
        pow2 ((hS + Δfin - n) / 2) * lastRoundsCheckingCost k hout Cstar := rfl

theorem q1_simple_lastrounds_time_ge_data (hS Δfin n k hout Cstar : ℝ)
    (hCstar : 0 ≤ Cstar) :
    q1SimpleLastRoundsData hS ≤ q1SimpleLastRoundsCost hS Δfin n k hout Cstar := by
  unfold q1SimpleLastRoundsCost q1SimpleLastRoundsData lastRoundsCheckingCost
  have hcheck : 0 ≤ Cstar + pow2 ((k - hout) / 2) := by
    have := pow2_nonneg ((k - hout) / 2)
    linarith
  have hiter : 0 ≤ pow2 ((hS + Δfin - n) / 2) := pow2_nonneg _
  have : 0 ≤ pow2 ((hS + Δfin - n) / 2) * (Cstar + pow2 ((k - hout) / 2)) :=
    mul_nonneg hiter hcheck
  linarith

theorem q1_simple_lastrounds_grover_budget (hS Δfin n : ℝ) :
    Real.pi / (4 * Real.sqrt (pow2 (-(hS + Δfin - n)))) + 1 =
      Real.pi / 4 * pow2 ((hS + Δfin - n) / 2) + 1 :=
  amplification_budget_pow2 (hS + Δfin - n)

end Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential
