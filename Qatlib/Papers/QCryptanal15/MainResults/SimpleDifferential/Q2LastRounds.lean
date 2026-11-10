/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.GroverBudget
import Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential.Q2Distinguisher
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential

open Complexity

noncomputable def q2SimpleLastRoundsMarkedFraction (hS Δfin n : ℝ) : ℝ :=
  pow2 (-(hS + Δfin - n))

noncomputable def lastRoundsCheckingCost (k hout Cstar : ℝ) : ℝ :=
  Cstar + pow2 ((k - hout) / 2)

noncomputable def q2SimpleLastRoundsData (hS : ℝ) : ℝ := pow2 (hS / 2 + 1)

noncomputable def q2SimpleLastRoundsCost (hS Δfin n k hout Cstar : ℝ) : ℝ :=
  pow2 (hS / 2 + 1) +
    pow2 ((hS + Δfin - n) / 2) * lastRoundsCheckingCost k hout Cstar

theorem q2_simple_lastrounds_marked_fraction (hS Δfin n : ℝ) :
    q2SimpleLastRoundsMarkedFraction hS Δfin n = pow2 (-hS - Δfin + n) := by
  unfold q2SimpleLastRoundsMarkedFraction
  congr 1
  ring

theorem q2_simple_lastrounds_filter_iterations (hS Δfin n : ℝ) :
    (Real.sqrt (q2SimpleLastRoundsMarkedFraction hS Δfin n))⁻¹ =
      pow2 ((hS + Δfin - n) / 2) := by
  unfold q2SimpleLastRoundsMarkedFraction
  exact inv_sqrt_pow2_neg (hS + Δfin - n)

theorem q2_simple_lastrounds_cost (hS Δfin n k hout Cstar : ℝ) :
    q2SimpleLastRoundsCost hS Δfin n k hout Cstar =
      q2SimpleLastRoundsData hS +
        (Real.sqrt (q2SimpleLastRoundsMarkedFraction hS Δfin n))⁻¹ *
          lastRoundsCheckingCost k hout Cstar := by
  unfold q2SimpleLastRoundsCost q2SimpleLastRoundsData
  rw [q2_simple_lastrounds_filter_iterations]

theorem q2_simple_lastrounds_data_eq_distinguisher (hS : ℝ) :
    q2SimpleLastRoundsData hS = q2SimpleDistinguisherCost hS := rfl

theorem q2_simple_lastrounds_time_ge_data (hS Δfin n k hout Cstar : ℝ)
    (hCstar : 0 ≤ Cstar) :
    q2SimpleLastRoundsData hS ≤ q2SimpleLastRoundsCost hS Δfin n k hout Cstar := by
  unfold q2SimpleLastRoundsCost q2SimpleLastRoundsData lastRoundsCheckingCost
  have hcheck : 0 ≤ Cstar + pow2 ((k - hout) / 2) := by
    have := pow2_nonneg ((k - hout) / 2)
    linarith
  have hiter : 0 ≤ pow2 ((hS + Δfin - n) / 2) := pow2_nonneg _
  have : 0 ≤ pow2 ((hS + Δfin - n) / 2) * (Cstar + pow2 ((k - hout) / 2)) :=
    mul_nonneg hiter hcheck
  linarith

theorem q2_simple_lastrounds_grover_budget (hS Δfin n : ℝ) :
    Real.pi / (4 * Real.sqrt (q2SimpleLastRoundsMarkedFraction hS Δfin n)) + 1 =
      Real.pi / 4 * pow2 ((hS + Δfin - n) / 2) + 1 := by
  unfold q2SimpleLastRoundsMarkedFraction
  exact amplification_budget_pow2 (hS + Δfin - n)

end Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential
